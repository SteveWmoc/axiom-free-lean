# Axiom-Free Lean 4.33: First Definitive Census

Date: 2026-08-25

Lean: `v4.33.0` (`d8b18978322de05a8f3dba51ef03cf5461676c17`)

mathlib: `v4.33.0` (`db584cd6d46c92f209a44c0f1c829460d327499d`)

## Executive answer

Strictly axiom-free Lean is already capable of substantial constructive mathematics. In the
`Mathlib` source modules alone, 19,454 user-facing theorems have proofs depending on none of
`propext`, `Quot.sound`, or `Classical.choice`. They include elementary arithmetic, generic
algebra, categorical equational reasoning, and some topology.

At the same time, current mathlib is foundationally optimized for extensional classical
mathematics. Only 7.42% of the 262,216 user-facing Mathlib theorems in this census are strictly
zero-axiom. The existing `Real` type, `Filter.Tendsto`, and `HasDerivAt` already depend on standard
axioms at the level of their definitions or theorem statements. Thus a strict zero-axiom analysis
library cannot simply clean proofs: it needs alternative definitions and relational interfaces.

Removing all three axioms is much stronger than removing choice. In Lean 4.33, `funext` depends on
`Quot.sound`; combining `funext` with `propext` gives ordinary set extensionality. The official Lean
documentation likewise explains that function extensionality is derived from quotient soundness
and that predicate-sets become extensional only after combining function and propositional
extensionality: <https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/>.

## Method

The census imports `Mathlib` and uses the same transitive kernel dependency computation as
`#print axioms`, namely `Lean.collectAxioms`. It classifies every theorem into the eight subsets of

`{propext, Quot.sound, Classical.choice}`

and a ninth bucket for any other axiom.

The Mathlib-only table below counts `ConstantInfo.thmInfo` declarations whose source module begins
with `Mathlib.`. The reproducible “user-facing” filter is:

```lean
!isPrivateName name && !name.isInternalDetail
```

This is a useful, explicit approximation to the public theorem surface, not an official mathlib API
designation. External packages such as Batteries and Aesop are excluded from the Mathlib row.

The statement census separately collects the axioms reachable from constants occurring in each
theorem's type. This distinguishes dependencies already baked into a statement from dependencies
introduced by its proof.

## Exact Mathlib theorem census

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
| **Total** | **262,216** |

Consequently:

| Restriction | Surviving theorems | Share |
|---|---:|---:|
| no `Classical.choice` | 62,694 | 23.91% |
| no `Quot.sound` | 31,565 | 12.04% |
| no `propext` | 24,437 | 9.32% |
| none of the three | 19,454 | 7.42% |

Every subset actually occurs. A single “classical/nonclassical” bit therefore loses important
information; the correct audit object is the full dependency lattice.

## Statement dependencies versus proof dependencies

| Statement dependency set | Statements |
|---|---:|
| none | 42,839 |
| `propext` | 11,632 |
| `Quot.sound` | 4,690 |
| `propext` + `Quot.sound` | 27,530 |
| `Classical.choice` | 520 |
| `propext` + `Classical.choice` | 162 |
| `Quot.sound` + `Classical.choice` | 91 |
| all three | 174,752 |
| **Total** | **262,216** |

There are 42,839 zero-axiom statements but only 19,454 zero-axiom whole theorems. The other 23,385
zero-axiom statements currently have proofs using at least one standard axiom:

| Whole-proof class for a zero-axiom statement | Count |
|---|---:|
| `propext` | 5,549 |
| `Quot.sound` | 1,466 |
| `propext` + `Quot.sound` | 6,036 |
| a class containing `Classical.choice` | 10,334 |
| **Total with a nonzero proof** | **23,385** |

This is an upper bound on the cleanup opportunity, not a claim that every proof can be made
constructive: excluded middle itself has an axiom-free statement but is not constructively
provable. Still, concrete examples below prove that a nontrivial part is accidental contamination.

More broadly, 86,691 statements (33.06%) use no choice, whereas only 62,694 whole theorems (23.91%)
use no choice. Thus 23,997 currently choice-using proofs have already choice-free statements.

## Domain snapshot

These are source-directory counts. “Choice-free” allows `propext` and/or `Quot.sound`; “zero” allows
none of the three.

| Mathlib directory | Total | Zero | Choice-free | Zero share | Choice-free share |
|---|---:|---:|---:|---:|---:|
| Algebra | 46,356 | 5,810 | 19,966 | 12.53% | 43.07% |
| Analysis | 26,256 | 208 | 706 | 0.79% | 2.69% |
| CategoryTheory | 32,421 | 1,865 | 5,162 | 5.75% | 15.92% |
| Combinatorics | 6,956 | 788 | 1,916 | 11.33% | 27.54% |
| Computability | 1,552 | 334 | 664 | 21.52% | 42.78% |
| Control | 316 | 124 | 291 | 39.24% | 92.09% |
| Data | 21,845 | 2,665 | 8,869 | 12.20% | 40.60% |
| Logic | 2,306 | 700 | 1,482 | 30.36% | 64.27% |
| MeasureTheory | 11,628 | 173 | 371 | 1.49% | 3.19% |
| NumberTheory | 6,005 | 95 | 459 | 1.58% | 7.64% |
| Order | 16,887 | 3,675 | 8,789 | 21.76% | 52.05% |
| Topology | 24,073 | 763 | 3,155 | 3.17% | 13.11% |

Counts measure library architecture and generated lemma volume, not the informal depth of a field.
They nevertheless identify where current definitions make strict reuse especially difficult.

## Verified landmarks

The following were checked directly with `#print axioms`.

| Declaration | Exact result |
|---|---|
| `Nat.add_comm`, `Nat.mul_comm` | none |
| `pow_add`, `mul_assoc`, `MonoidHom.map_mul` | none |
| `CategoryTheory.Category.assoc` | none |
| `CategoryTheory.NatTrans.ext` | none; it assumes equality of the component function |
| `Continuous`, `Continuous.comp` | none |
| `funext` | `Quot.sound` |
| `List.reverse_reverse` | `propext` |
| `Nat.gcd_comm` | `propext`, `Quot.sound` |
| `Nat.exists_infinite_primes` | all three |
| `Set.ext`, `Subgroup.ext` | `propext`, `Quot.sound` |
| `LinearMap.ext` | `Quot.sound` |
| `Finset.ext`, `Polynomial.ext` | all three |
| `Filter.Tendsto` | `propext`, `Quot.sound` |
| `Real`, `Real.linearOrder` | all three |
| `HasDerivAt`, `HasDerivAt.add` | all three |
| `MeasureTheory.integral_add` | all three |

The standard axioms and `#print axioms` are documented in the Lean reference manual:
<https://lean-lang.org/doc/reference/latest/Axioms/>. The pinned source trees are
<https://github.com/leanprover/lean4/tree/v4.33.0> and
<https://github.com/leanprover-community/mathlib4/tree/v4.33.0>.

## Concrete contamination paths

The shortest-path tracer found, among others:

```text
List.reverse_reverse
  -> List.reverseAux_reverseAux_nil -> eq_self -> eq_true -> propext

Nat.exists_infinite_primes
  -> Nat.minFac_dvd -> Nat.minFac_has_prop -> Nat.add_eq_right._simp_1
  -> Nat.add_eq_right -> ... -> Classical.propDecidable -> Classical.choice

Finset.ext
  -> Finset.instSetLike -> ... -> Multiset.Nodup.ext
  -> List.perm_ext_iff_of_nodup -> Classical.propDecidable -> Classical.choice

Real
  -> Real.ofCauchy -> Rat.instIsStrictOrderedRing -> ...
  -> Classical.or_iff_not_imp_right -> Classical.propDecidable -> Classical.choice
```

The first three are strong contamination candidates: their mathematical content does not call for
choice. The `Real` path is deeper. Current real-number structure and order packages embed classical
and extensional infrastructure in the type itself.

## Zero-axiom replacement proofs already verified

`ZeroBenchmarks.lean` compiles with every listed declaration reporting “does not depend on any
axioms.” It contains:

- excluded middle for an explicitly decidable proposition;
- double-negated excluded middle for every proposition;
- the pointwise form of `List.map id`;
- an identical zero-axiom replacement proof of `List.reverse_reverse`;
- an identical zero-axiom replacement proof of `Nat.dvd_antisymm`;
- a pointwise-equivalence formulation of commutativity of set union.

The first two cleanup proofs show that at least some dependencies recorded in core/Mathlib are proof
engineering artifacts. The pointwise examples show the complementary phenomenon: eliminating
`Quot.sound` sometimes requires replacing equality of functions or extensional objects by an
explicit equivalence relation.

## What can be formalized without all three?

Operationally, the answer is now fairly sharp.

1. **Directly and comfortably:** inductive data, structural recursion, constructive propositional
   reasoning, decidable mathematics, much elementwise arithmetic and algebra, equational category
   theory, algorithms and correctness proofs, and any theorem whose witnesses are carried as data.

2. **Directly but with redesigned interfaces:** functions, sets, quotients, morphisms, and finite
   unordered objects can be handled using pointwise equality, setoids, explicit equivalence
   relations, and respectfulness lemmas. One must avoid treating extensionally equivalent objects as
   Lean-equal.

3. **Not reusable unchanged from current mathlib:** large parts of real analysis, measure theory,
   probability, and equality-heavy algebraic constructions. Their present statements often already
   depend on the three axioms. Strict zero-axiom work needs a new constructive/setoid-based real and
   analysis layer, not merely alternative tactics.

4. **Classical mathematics can still be represented metamathematically:** Lean can define the syntax
   and proof relation of a classical theory and prove statements about its derivations without using
   the three axioms. Negative translations can also turn classical propositions into constructive
   ones. These routes do not make the original extensional Lean statement axiom-free; they change
   what is asserted.

## Recommended program of work

1. Turn `AxiomCensus.lean` and `AxiomPaths.lean` into a small pinned audit project with CI.
2. Submit the two proven low-level cleanups (`List.reverse_reverse` and `Nat.dvd_antisymm`) upstream,
   then use the same method on `Nat.gcd_comm` and `Nat.exists_infinite_primes`.
3. Export the 42,839 zero-statement declarations and triage them into: logically classical;
   proof/tactic contamination; dependency contamination; and extensional reformulation needed.
4. Build the compatibility layer already suggested by the SDG investigation: explicit
   `Decidable` parameters, witnessed data rather than `Nonempty` extraction, pointwise relations,
   setoids, list-backed finite constructions, and audited bridges to ordinary mathlib.
5. Treat strict zero-axiom analysis as a separate foundational track centered on a relational
   construction of the reals.

## Reproduction

Clone this repository, obtain mathlib's cached build artifacts, and run:

```bash
lake update
lake exe cache get
lake env lean Audit/AxiomCensus.lean
lake env lean Audit/AxiomPaths.lean
lake env lean Audit/RepresentativeProbe.lean
lake env lean Audit/ZeroBenchmarks.lean
```

All counts in this report are generated from those pinned artifacts rather than inferred from source
text searches.
