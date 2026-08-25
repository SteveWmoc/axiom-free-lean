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


def validate_theorem_data(path: Path) -> None:
    whole_counts: Counter[int] = Counter()
    statement_counts: Counter[int] = Counter()
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


def main() -> None:
    validate_theorem_data(Path("results/TheoremData.tsv"))
    validate_dependency_frequency(Path("results/DirectDependencyFrequency.tsv"))
    print("theorem-level data checks passed")


if __name__ == "__main__":
    main()
