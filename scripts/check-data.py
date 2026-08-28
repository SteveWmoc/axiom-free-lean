#!/usr/bin/env python3
"""Validate the pinned theorem-level audit exports."""

from __future__ import annotations

import csv
from collections import Counter
from pathlib import Path


EXPECTED_WHOLE = [19_454, 11_362, 4_412, 27_466, 413, 336, 158, 198_615, 0]
EXPECTED_STATEMENT = [42_839, 11_632, 4_690, 27_530, 520, 162, 91, 174_752, 0]
EXPECTED_STRICT_FRONTIER = 23_385
EXPECTED_CHOICE_FRONTIER = 23_997


def validate_theorem_data(path: Path) -> dict[str, tuple[int, int]]:
    whole_counts: Counter[int] = Counter()
    statement_counts: Counter[int] = Counter()
    theorem_classes: dict[str, tuple[int, int]] = {}
    strict_frontier = 0
    choice_frontier = 0
    previous_name = ""

    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        expected_fields = [
            "name",
            "module",
            "statement_class",
            "whole_class",
            "proof_added_mask",
        ]
        assert reader.fieldnames == expected_fields, reader.fieldnames

        for row in reader:
            name = row["name"]
            assert name > previous_name, f"rows are not strictly sorted at {name!r}"
            previous_name = name
            assert row["module"] == "Mathlib" or row["module"].startswith("Mathlib."), row

            statement = int(row["statement_class"])
            whole = int(row["whole_class"])
            added = int(row["proof_added_mask"])
            assert 0 <= statement <= 8 and 0 <= whole <= 8 and 0 <= added <= 8, row
            if statement < 8 and whole < 8:
                assert statement & ~whole == 0, row
                assert added == whole - statement, row

            statement_counts[statement] += 1
            whole_counts[whole] += 1
            theorem_classes[name] = (statement, whole)
            strict_frontier += statement == 0 and whole != 0
            choice_frontier += (
                statement < 8
                and whole < 8
                and statement & 4 == 0
                and whole & 4 != 0
            )

    assert [whole_counts[i] for i in range(9)] == EXPECTED_WHOLE, whole_counts
    assert [statement_counts[i] for i in range(9)] == EXPECTED_STATEMENT, statement_counts
    assert strict_frontier == EXPECTED_STRICT_FRONTIER, strict_frontier
    assert choice_frontier == EXPECTED_CHOICE_FRONTIER, choice_frontier
    return theorem_classes


def validate_dependency_frequency(path: Path) -> None:
    rows_by_policy: dict[str, list[tuple[int, str]]] = {
        "strict_zero": [],
        "choice_free": [],
    }
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        expected_fields = [
            "policy",
            "direct_dependency",
            "theorem_count",
            "dependency_class",
            "module",
        ]
        assert reader.fieldnames == expected_fields, reader.fieldnames
        for row in reader:
            policy = row["policy"]
            assert policy in rows_by_policy, row
            count = int(row["theorem_count"])
            dependency_class = int(row["dependency_class"])
            assert count > 0 and 0 <= dependency_class <= 8, row
            if policy == "strict_zero":
                assert dependency_class != 0, row
            else:
                assert 4 <= dependency_class < 8, row
            rows_by_policy[policy].append((count, row["direct_dependency"]))

    for policy, rows in rows_by_policy.items():
        assert len(rows) == 100, (policy, len(rows))
        assert rows == sorted(rows, key=lambda item: (-item[0], item[1])), policy


def validate_counterfactual_gain(
    path: Path, theorem_classes: dict[str, tuple[int, int]]
) -> dict[tuple[str, str], tuple[int, int, int]]:
    rows_by_policy: dict[str, list[tuple[int, str]]] = {
        "strict_zero": [],
        "choice_free": [],
    }
    candidates: dict[tuple[str, str], tuple[int, int, int]] = {}
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        expected_fields = [
            "policy",
            "candidate",
            "theorem_gain",
            "candidate_class",
            "statement_class",
            "kind",
            "module",
            "examples",
        ]
        assert reader.fieldnames == expected_fields, reader.fieldnames
        seen: set[tuple[str, str]] = set()
        for row in reader:
            policy = row["policy"]
            assert policy in rows_by_policy, row
            candidate = row["candidate"]
            key = (policy, candidate)
            assert key not in seen, key
            seen.add(key)

            gain = int(row["theorem_gain"])
            candidate_class = int(row["candidate_class"])
            statement_class = int(row["statement_class"])
            assert gain > 0, row
            assert 0 <= candidate_class < 8 and 0 <= statement_class < 8, row
            assert row["kind"] != "axiom", row
            assert row["module"] and row["module"] != "(current)", row

            if policy == "strict_zero":
                assert candidate_class != 0 and statement_class == 0, row
                assert gain <= EXPECTED_STRICT_FRONTIER, row
            else:
                assert candidate_class & 4 and not statement_class & 4, row
                assert gain <= EXPECTED_CHOICE_FRONTIER, row

            examples = row["examples"].split(";")
            assert 1 <= len(examples) <= 5 and len(examples) <= gain, row
            assert examples == sorted(set(examples)), row
            for theorem in examples:
                theorem_statement, theorem_whole = theorem_classes[theorem]
                if policy == "strict_zero":
                    assert theorem_statement == 0 and theorem_whole != 0, row
                else:
                    assert not theorem_statement & 4 and theorem_whole & 4, row

            rows_by_policy[policy].append((gain, candidate))
            candidates[key] = (gain, candidate_class, statement_class)

    for policy, rows in rows_by_policy.items():
        assert len(rows) == 100, (policy, len(rows))
        assert rows == sorted(rows, key=lambda item: (-item[0], item[1])), policy
    return candidates


def validate_repair_ledger(
    path: Path,
    counterfactual: dict[tuple[str, str], tuple[int, int, int]],
) -> None:
    classifications = {
        "verified_repair",
        "foundational_principle",
        "implies_forbidden_principle",
        "classical_principle",
        "choice_principle",
        "choice_using_interface",
    }
    expected_keys = {
        ("strict_zero", "funext"),
        ("strict_zero", "Eq.propIntro"),
        ("choice_free", "Classical.propDecidable"),
        ("choice_free", "Set.instCompleteAtomicBooleanAlgebra"),
        ("choice_free", "Classical.indefiniteDescription"),
        ("choice_free", "map_sub'"),
    }
    seen: set[tuple[str, str]] = set()

    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        assert reader.fieldnames == [
            "policy",
            "candidate",
            "theorem_gain",
            "current_class",
            "statement_class",
            "classification",
            "replacement",
            "replacement_class",
            "evidence",
        ], reader.fieldnames

        for row in reader:
            key = (row["policy"], row["candidate"])
            assert key in expected_keys and key not in seen, key
            seen.add(key)
            gain, current_class, statement_class = counterfactual[key]
            assert int(row["theorem_gain"]) == gain, row
            assert int(row["current_class"]) == current_class, row
            assert int(row["statement_class"]) == statement_class, row
            assert row["classification"] in classifications, row
            assert row["evidence"], row

            if row["classification"] == "verified_repair":
                assert row["replacement"], row
                assert int(row["replacement_class"]) == 0, row
            else:
                assert not row["replacement"] and not row["replacement_class"], row

    assert seen == expected_keys, expected_keys - seen


def main() -> None:
    theorem_classes = validate_theorem_data(Path("results/TheoremData.tsv"))
    validate_dependency_frequency(Path("results/DirectDependencyFrequency.tsv"))
    counterfactual = validate_counterfactual_gain(
        Path("results/CounterfactualGain.tsv"), theorem_classes
    )
    validate_repair_ledger(Path("results/RepairLedger.tsv"), counterfactual)
    print("theorem-level data and repair-ledger checks passed")


if __name__ == "__main__":
    main()
