import Mathlib
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean

private def standardMask (axioms : Array Name) : Nat × Bool :=
  axioms.foldl (init := (0, false)) fun (mask, other) ax =>
    if ax == ``propext then (mask + 1, other)
    else if ax == ``Quot.sound then (mask + 2, other)
    else if ax == ``Classical.choice then (mask + 4, other)
    else (mask, true)

private def classLabel : Nat → String
  | 0 => "none"
  | 1 => "propext"
  | 2 => "Quot.sound"
  | 3 => "propext + Quot.sound"
  | 4 => "Classical.choice"
  | 5 => "propext + Classical.choice"
  | 6 => "Quot.sound + Classical.choice"
  | 7 => "propext + Quot.sound + Classical.choice"
  | _ => "other"

private def bump (counts : Array Nat) (i : Nat) : Array Nat :=
  counts.set! i (counts[i]! + 1)

private def exprAxioms [Monad m] [MonadEnv m] (expr : Expr) : m (Array Name) := do
  let mut result : NameSet := {}
  for constant in expr.getUsedConstants do
    for ax in (← Lean.collectAxioms constant) do
      result := result.insert ax
  return result.toArray

private def moduleGroup (env : Environment) (name : Name) : Nat :=
  match env.getModuleIdxFor? name with
  | none => 5
  | some modIdx =>
      let modName := env.header.moduleNames[modIdx.toNat]!.toString
      if modName == "Init" || modName.startsWith "Init." then 0
      else if modName == "Std" || modName.startsWith "Std." then 1
      else if modName == "Lean" || modName.startsWith "Lean." then 2
      else if modName == "Mathlib" || modName.startsWith "Mathlib." then 3
      else 4

private def groupLabel : Nat → String
  | 0 => "Init"
  | 1 => "Std"
  | 2 => "Lean"
  | 3 => "Mathlib"
  | 4 => "other packages"
  | _ => "current file"

private def mathlibDomain (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | none => "(current)"
  | some modIdx =>
      let parts := env.header.moduleNames[modIdx.toNat]!.toString.splitOn "."
      parts.getD 1 "(root)"

run_cmd do
  let env ← getEnv
  let mut allCounts := Array.replicate 9 0
  let mut theoremCounts := Array.replicate 9 0
  let mut apiCounts := Array.replicate 9 0
  let mut apiTheoremCounts := Array.replicate 9 0
  let mut apiTheoremsByGroup : Array (Array Nat) := Array.replicate 6 (Array.replicate 9 0)
  let mut mathlibStatementCounts := Array.replicate 9 0
  let mut mathlibZeroStatementByProof := Array.replicate 9 0
  let mut mathlibStatementProofMatrix : Array (Array Nat) :=
    Array.replicate 9 (Array.replicate 9 0)
  let mut mathlibDomainCounts : Std.HashMap String (Array Nat) := {}
  let mut theoremExamples : Array (Array Name) := Array.replicate 9 #[]
  for (name, info) in env.constants do
    let axioms ← Lean.collectAxioms name
    let (mask, hasOther) := standardMask axioms
    let idx := if hasOther then 8 else mask
    allCounts := bump allCounts idx
    if info matches .thmInfo _ then
      theoremCounts := bump theoremCounts idx
    if !isPrivateName name && !name.isInternalDetail then
      apiCounts := bump apiCounts idx
      match info with
      | .thmInfo theoremInfo =>
          apiTheoremCounts := bump apiTheoremCounts idx
          let group := moduleGroup env name
          apiTheoremsByGroup := apiTheoremsByGroup.set! group (bump apiTheoremsByGroup[group]! idx)
          if group == 3 then
            let statementAxioms ← exprAxioms theoremInfo.type
            let (statementMask, statementHasOther) := standardMask statementAxioms
            let statementIdx := if statementHasOther then 8 else statementMask
            mathlibStatementCounts := bump mathlibStatementCounts statementIdx
            if statementIdx == 0 then
              mathlibZeroStatementByProof := bump mathlibZeroStatementByProof idx
            mathlibStatementProofMatrix := mathlibStatementProofMatrix.set! statementIdx
              (bump mathlibStatementProofMatrix[statementIdx]! idx)
            let domain := mathlibDomain env name
            let counts := mathlibDomainCounts[domain]?.getD (Array.replicate 9 0)
            mathlibDomainCounts := mathlibDomainCounts.insert domain (bump counts idx)
          if theoremExamples[idx]!.size < 12 then
            theoremExamples := theoremExamples.set! idx (theoremExamples[idx]!.push name)
      | _ => pure ()
  IO.println "raw environment"
  IO.println "class\tall declarations\ttheorems"
  for idx in [0:9] do
    IO.println s!"{classLabel idx}\t{allCounts[idx]!}\t{theoremCounts[idx]!}"
  IO.println "\nuser-facing names (not private or internal-detail)"
  IO.println "class\tall declarations\ttheorems"
  for idx in [0:9] do
    IO.println s!"{classLabel idx}\t{apiCounts[idx]!}\t{apiTheoremCounts[idx]!}"
  IO.println "\nuser-facing theorem counts by source module group"
  IO.println "group\tnone\tpropext\tQuot.sound\tp+Q\tchoice\tp+C\tQ+C\tp+Q+C\tother"
  for group in [0:6] do
    IO.println s!"{groupLabel group}\t{String.intercalate "\t" (apiTheoremsByGroup[group]!.toList.map toString)}"
  IO.println "\nMathlib theorem statement dependencies (same user-facing-name filter)"
  IO.println "class\tstatements"
  for idx in [0:9] do
    IO.println s!"{classLabel idx}\t{mathlibStatementCounts[idx]!}"
  IO.println "\nMathlib theorems with zero-axiom statements, classified by whole theorem"
  IO.println "whole-theorem class\tcount"
  for idx in [0:9] do
    IO.println s!"{classLabel idx}\t{mathlibZeroStatementByProof[idx]!}"
  IO.println "\nMathlib statement-class by whole-theorem-class matrix"
  IO.println "statement\\whole\tnone\tpropext\tQuot.sound\tp+Q\tchoice\tp+C\tQ+C\tp+Q+C\tother"
  for statementIdx in [0:9] do
    IO.println s!"{classLabel statementIdx}\t{String.intercalate "\t"
      (mathlibStatementProofMatrix[statementIdx]!.toList.map toString)}"
  IO.println "\nMathlib user-facing theorem counts by top-level source directory"
  IO.println "domain\tnone\tpropext\tQuot.sound\tp+Q\tchoice\tp+C\tQ+C\tp+Q+C\tother"
  let domains := mathlibDomainCounts.toList.map (·.1) |>.mergeSort (· < ·)
  for domain in domains do
    IO.println s!"{domain}\t{String.intercalate "\t" (mathlibDomainCounts[domain]!.toList.map toString)}"
  IO.println "\nfirst user-facing theorem examples by class"
  for idx in [0:9] do
    IO.println s!"{classLabel idx}: {theoremExamples[idx]!.toList}"
