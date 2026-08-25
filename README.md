# axiom-free-lean

[![CI](https://github.com/SteveWmoc/axiom-free-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/SteveWmoc/axiom-free-lean/actions/workflows/ci.yml)
[![Lean 4.33.0](https://img.shields.io/badge/Lean-4.33.0-blue)](https://github.com/leanprover/lean4/releases/tag/v4.33.0)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue)](LICENSE)

A reproducible census of what Lean and mathlib can formalize without
`propext`, `Quot.sound`, or `Classical.choice`.

The baseline is pinned to Lean `v4.33.0` and mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d` (tag `v4.33.0`). The audit uses
Lean's transitive kernel dependency computation, `Lean.collectAxioms`, rather
than source-text searches.

## Results at a glance

The census finds 262,216 user-facing theorems whose source module is in
`Mathlib.*`:

| Whole-theorem dependency set | Theorems |
|---|---:|
| none | 19,454 |
| `propext` | 11,362 |
| `Quot.sound` | 4,412 |
| `propext` + `Quot.sound` | 27,466 |
| `Classical.choice` | 413 |
| `propext` + `Classical.choice` | 336 |
| `Quot.sound` + `Classical.choice` | 158 |
| all three | 198,615 |
| other axiom | 0 |

So 62,694 theorems (23.91%) are choice-free, while 19,454 (7.42%) depend on
none of the three standard axioms. Every one of the eight subsets occurs.

The statement/proof split is equally important: 42,839 theorem statements are
zero-axiom, but only 19,454 complete theorems are. That leaves 23,385
zero-axiom statements whose current proofs use at least one of the three
axioms. This is a triage set, not a claim that every such statement is
constructively provable.

See [REPORT.md](REPORT.md) for the full method, domain tables, dependency
paths, interpretation, and limitations.

## What “zero-axiom” means here

A declaration is zero-axiom when Lean's `#print axioms` dependency set is
empty. For the census, declarations are partitioned by the exact subset of

```text
{propext, Quot.sound, Classical.choice}
```

that their transitive dependencies reach, with a ninth bucket for any other
axiom. No theorem in the Mathlib-only census reached that ninth bucket.

The user-facing filter is explicit and reproducible:

```lean
!isPrivateName name && !name.isInternalDetail
```

It is an approximation to the public theorem surface, not an official mathlib
API designation.

## Repository layout

| Path | Purpose |
|---|---|
| `AxiomFreeLean/Benchmarks.lean` | Reusable declarations with verified empty axiom sets |
| `Audit/AxiomCensus.lean` | Eight-class theorem and statement census |
| `Audit/AxiomPaths.lean` | Shortest transitive dependency paths to the three axioms |
| `Audit/CoreProbe.lean` | Small kernel and `Std` landmarks |
| `Audit/RepresentativeProbe.lean` | Representative mathlib landmarks |
| `Audit/ZeroBenchmarks.lean` | `#print axioms` checks for the replacement proofs |
| `results/TheoremData.tsv` | One machine-readable row per user-facing Mathlib theorem |
| `results/DirectDependencyFrequency.tsv` | Most frequent contaminated direct proof dependencies |
| `results/` | Other committed output from the pinned audit run |
| `REPORT.md` | Full findings and interpretation |

## Machine-readable data

`results/TheoremData.tsv` is sorted by declaration name and has the columns

```text
name  module  statement_class  whole_class  proof_added_mask
```

The three low bits encode `propext` (1), `Quot.sound` (2), and
`Classical.choice` (4). Thus class 0 is zero-axiom, class 3 is
`propext + Quot.sound`, and class 7 contains all three. Class 8 is reserved
for any dependency on another axiom; it does not occur in this pinned
Mathlib-only dataset. For classes 0--7, `proof_added_mask` is the set of
standard axioms contributed by the proof rather than its statement.

The strict frontier consists of rows with `statement_class = 0` and
`whole_class != 0`. The choice frontier consists of rows whose statement
class does not contain bit 4 but whose whole class does.

`results/DirectDependencyFrequency.tsv` ranks direct constants occurring in
frontier proof terms by the number of frontier theorems that mention them.
This is an exact direct-reference count and a useful triage heuristic. It is
not yet a counterfactual cleanup score: a theorem may have additional paths
to the same axiom after one dependency is repaired.

## Reproduce

Install [elan](https://github.com/leanprover/elan), then run:

```bash
git clone https://github.com/SteveWmoc/axiom-free-lean.git
cd axiom-free-lean
lake update
lake exe cache get
lake build
./scripts/check.sh
```

To regenerate the committed result files:

```bash
./scripts/run-audit.sh
git diff -- results/
```

`AxiomCensus.lean` imports all of Mathlib and scans its environment, so that
step takes substantially longer than the targeted probes.

## Verified cleanup examples

The reusable benchmark library includes identical-statement, zero-axiom
replacement proofs for:

- `List.reverse_reverse`, whose existing proof reaches `propext`;
- `Nat.dvd_antisymm`, whose existing proof reaches `propext`.

It also includes pointwise formulations that avoid extensional equality, plus
constructive forms of excluded middle.

## Contributing

Reproductions, corrections, additional clean proofs, and constructive
interfaces are welcome. Please keep numerical claims pinned to an exact Lean
and mathlib revision and include generated audit output with changes. See
[CONTRIBUTING.md](CONTRIBUTING.md).

## License

Apache-2.0. See [LICENSE](LICENSE).
