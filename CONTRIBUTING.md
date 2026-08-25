# Contributing

Corrections, new zero-axiom proofs, dependency-path investigations, and
constructive interfaces are welcome.

## Ground rules

1. Pin numerical claims to an exact Lean and mathlib revision.
2. Use `Lean.collectAxioms` or `#print axioms`; source-text search is not a
   substitute for transitive kernel dependency analysis.
3. Distinguish dependencies in a theorem's statement from dependencies added
   by its proof.
4. Do not describe every zero-axiom statement as constructively provable.
5. Prefer small, reviewable examples with an explanation of what caused the
   original dependency.

## Before opening a pull request

```bash
lake exe cache get
./scripts/run-audit.sh
git diff -- results/
./scripts/check.sh
```

Commit changed result files when an intentional audit change affects them.
