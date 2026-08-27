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

private structure TheoremRow where
  name : Name
  moduleName : String
  statementClass : Nat
  wholeClass : Nat

private structure FrontierCandidate where
  name : Name
  statementMask : Nat
  statementHasOther : Bool
  wholeMask : Nat
  wholeHasOther : Bool
  directProofDependencies : Array Name

private structure DominatorInfo where
  root : Name
  idom : Std.HashMap Name Name := {}
  nodeCount : Nat := 0
  missingEdgeDetected : Bool := false

private structure GainEvidence where
  theoremCount : Nat := 0
  examples : Array Name := #[]

private structure GainRow where
  candidate : Name
  theoremCount : Nat
  candidateClass : Nat
  statementClass : Nat
  kind : String
  moduleName : String
  examples : Array Name

private def usesChoice (mask : Nat) : Bool :=
  mask >= 4

private def isStrictFrontier (candidate : FrontierCandidate) : Bool :=
  candidate.statementMask == 0 && !candidate.statementHasOther &&
    (candidate.wholeMask != 0 || candidate.wholeHasOther)

private def isChoiceFrontier (candidate : FrontierCandidate) : Bool :=
  !usesChoice candidate.statementMask && usesChoice candidate.wholeMask

private def maskUses (mask bit : Nat) : Bool :=
  (mask / bit) % 2 == 1

private def addExprConstants (result : NameSet) (expr : Expr) : NameSet :=
  expr.getUsedConstants.foldl (init := result) fun result name => result.insert name

private def directDependencies (env : Environment) (name : Name) : Array Name :=
  match env.find? name with
  | some (.axiomInfo value) => (addExprConstants {} value.type).toArray
  | some (.defnInfo value) =>
      (addExprConstants (addExprConstants {} value.type) value.value).toArray
  | some (.thmInfo value) =>
      (addExprConstants (addExprConstants {} value.type) value.value).toArray
  | some (.opaqueInfo value) =>
      (addExprConstants (addExprConstants {} value.type) value.value).toArray
  | some (.ctorInfo value) => (addExprConstants {} value.type).toArray
  | some (.recInfo value) => (addExprConstants {} value.type).toArray
  | some (.inductInfo value) =>
      let result := value.ctors.foldl (init := addExprConstants {} value.type) fun result ctor =>
        result.insert ctor
      result.toArray
  | some value => (addExprConstants {} value.type).toArray
  | none => #[]

private def intersectNameSets (left right : NameSet) : NameSet :=
  left.toArray.foldl (init := {}) fun result name =>
    if right.contains name then result.insert name else result

private partial def reversePostorderVisit
    (successors : Std.HashMap Name (Array Name)) (name : Name) :
    StateM (NameSet × Array Name) Unit := do
  let (visited, _) ← get
  if visited.contains name then
    return ()
  modify fun state => (state.1.insert name, state.2)
  for successor in successors[name]?.getD #[] do
    reversePostorderVisit successors successor
  modify fun state => (state.1, state.2.push name)

private def intersectImmediateDominators
    (idom : Std.HashMap Name Name) (rpoIndex : Std.HashMap Name Nat)
    (left right : Name) : Name := Id.run do
  let mut left := left
  let mut right := right
  while left != right do
    while (rpoIndex[left]?.getD 0) > (rpoIndex[right]?.getD 0) do
      left := idom[left]?.getD left
    while (rpoIndex[right]?.getD 0) > (rpoIndex[left]?.getD 0) do
      right := idom[right]?.getD right
  return left

private def buildDominatorInfo (target : Name)
    (successors predecessors : Std.HashMap Name (Array Name))
    (missingEdgeDetected : Bool) : DominatorInfo := Id.run do
  let (_, traversal) := (reversePostorderVisit successors target).run ({}, #[])
  let reversePostorder := traversal.2.reverse
  let mut rpoIndex : Std.HashMap Name Nat := {}
  for i in [0:reversePostorder.size] do
    rpoIndex := rpoIndex.insert reversePostorder[i]! i
  let mut idom : Std.HashMap Name Name := {}
  idom := idom.insert target target
  let mut changed := true
  while changed do
    changed := false
    for i in [1:reversePostorder.size] do
      let name := reversePostorder[i]!
      let mut newIdom? : Option Name := none
      for predecessor in predecessors[name]?.getD #[] do
        if idom.contains predecessor then
          newIdom? := some <| match newIdom? with
            | none => predecessor
            | some current =>
                intersectImmediateDominators idom rpoIndex current predecessor
      if let some newIdom := newIdom? then
        if idom[name]? != some newIdom then
          idom := idom.insert name newIdom
          changed := true
  return {
    root := target
    idom
    nodeCount := reversePostorder.size
    missingEdgeDetected
  }

private def dominatorChainAux (info : DominatorInfo) :
    Nat → Name → NameSet → Option NameSet
  | 0, _, _ => none
  | Nat.succ fuel, name, result =>
      let result := result.insert name
      if name == info.root then
        some result
      else
        match info.idom[name]? with
        | some parent => dominatorChainAux info fuel parent result
        | none => none

private def dominatorChain (info : DominatorInfo) (name : Name) : Option NameSet :=
  dominatorChainAux info (info.nodeCount + 1) name {}

private def isNonAxiomDeclaration (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some (.axiomInfo _) => false
  | some _ => true
  | none => false

private def bumpEvidence (counts : Std.HashMap Name GainEvidence)
    (candidate theoremName : Name) : Std.HashMap Name GainEvidence :=
  let evidence := counts[candidate]?.getD {}
  let examples :=
    if evidence.examples.size < 5 then evidence.examples.push theoremName else evidence.examples
  counts.insert candidate {
    theoremCount := evidence.theoremCount + 1
    examples
  }

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .inductInfo _ => "inductive"
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

private def sourceModule (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | none => "(current)"
  | some modIdx => env.header.moduleNames[modIdx.toNat]!.toString

private def writeTheoremData (rows : Array TheoremRow) : IO Unit := do
  IO.FS.createDirAll "results"
  let out ← IO.FS.Handle.mk "results/TheoremData.tsv" .write
  out.putStrLn "name\tmodule\tstatement_class\twhole_class\tproof_added_mask"
  let rows := rows.toList.mergeSort fun a b => a.name.toString < b.name.toString
  for row in rows do
    let proofAddedMask :=
      if row.statementClass < 8 && row.wholeClass < 8 then
        row.wholeClass - row.statementClass
      else
        8
    out.putStrLn s!"{row.name}\t{row.moduleName}\t{row.statementClass}\t{row.wholeClass}\t{proofAddedMask}"
  out.flush

private def bumpName (counts : Std.HashMap Name Nat) (name : Name) : Std.HashMap Name Nat :=
  counts.insert name (counts[name]?.getD 0 + 1)

private def writeDependencyFrequency (env : Environment)
    (classes : Std.HashMap Name (Nat × Bool)) (candidates : Array FrontierCandidate) : IO Unit := do
  let mut strictCounts : Std.HashMap Name Nat := {}
  let mut choiceCounts : Std.HashMap Name Nat := {}
  for candidate in candidates do
    for dependency in candidate.directProofDependencies do
      let (dependencyMask, dependencyHasOther) := classes[dependency]?.getD (0, false)
      if isStrictFrontier candidate && (dependencyMask != 0 || dependencyHasOther) then
        strictCounts := bumpName strictCounts dependency
      if isChoiceFrontier candidate && usesChoice dependencyMask then
        choiceCounts := bumpName choiceCounts dependency
  let out ← IO.FS.Handle.mk "results/DirectDependencyFrequency.tsv" .write
  out.putStrLn "policy\tdirect_dependency\ttheorem_count\tdependency_class\tmodule"
  for (policy, counts) in [("strict_zero", strictCounts), ("choice_free", choiceCounts)] do
    let entries := counts.toList.mergeSort fun a b =>
      if a.2 == b.2 then a.1.toString < b.1.toString else a.2 > b.2
    for (name, count) in entries.take 100 do
      let (mask, hasOther) := classes[name]?.getD (0, false)
      let idx := if hasOther then 8 else mask
      out.putStrLn s!"{policy}\t{name}\t{count}\t{idx}\t{sourceModule env name}"
  out.flush

private def scoreCounterfactualGains (env : Environment)
    (classes : Std.HashMap Name (Nat × Bool)) (candidates : Array FrontierCandidate) :
    Std.HashMap Name GainEvidence × Std.HashMap Name GainEvidence × Bool × Nat := Id.run do
  let candidates := candidates.toList.mergeSort fun left right =>
    left.name.toString < right.name.toString
  let mut propextSuccessors : Std.HashMap Name (Array Name) := {}
  let mut propextPredecessors : Std.HashMap Name (Array Name) := {}
  let mut quotSuccessors : Std.HashMap Name (Array Name) := {}
  let mut quotPredecessors : Std.HashMap Name (Array Name) := {}
  let mut choiceSuccessors : Std.HashMap Name (Array Name) := {}
  let mut choicePredecessors : Std.HashMap Name (Array Name) := {}
  let mut propextMissingEdgeDetected := false
  let mut quotMissingEdgeDetected := false
  let mut choiceMissingEdgeDetected := false
  -- Extract every declaration's constants once, then route each relevant edge to all
  -- of the standard-axiom graphs it belongs to.
  for (name, _) in env.constants do
    let (mask, _) := classes[name]?.getD (0, false)
    let nameUsesPropext := maskUses mask 1
    let nameUsesQuot := maskUses mask 2
    let nameUsesChoice := maskUses mask 4
    if nameUsesPropext || nameUsesQuot || nameUsesChoice then
      let mut foundPropext := false
      let mut foundQuot := false
      let mut foundChoice := false
      for dependency in directDependencies env name do
        let (dependencyMask, _) := classes[dependency]?.getD (0, false)
        if nameUsesPropext && maskUses dependencyMask 1 then
          foundPropext := true
          let dependentNodes := propextSuccessors[dependency]?.getD #[]
          propextSuccessors := propextSuccessors.insert dependency (dependentNodes.push name)
          let dependencyNodes := propextPredecessors[name]?.getD #[]
          propextPredecessors := propextPredecessors.insert name (dependencyNodes.push dependency)
        if nameUsesQuot && maskUses dependencyMask 2 then
          foundQuot := true
          let dependentNodes := quotSuccessors[dependency]?.getD #[]
          quotSuccessors := quotSuccessors.insert dependency (dependentNodes.push name)
          let dependencyNodes := quotPredecessors[name]?.getD #[]
          quotPredecessors := quotPredecessors.insert name (dependencyNodes.push dependency)
        if nameUsesChoice && maskUses dependencyMask 4 then
          foundChoice := true
          let dependentNodes := choiceSuccessors[dependency]?.getD #[]
          choiceSuccessors := choiceSuccessors.insert dependency (dependentNodes.push name)
          let dependencyNodes := choicePredecessors[name]?.getD #[]
          choicePredecessors := choicePredecessors.insert name (dependencyNodes.push dependency)
      if nameUsesPropext && name != ``propext && !foundPropext then
        propextMissingEdgeDetected := true
      if nameUsesQuot && name != ``Quot.sound && !foundQuot then
        quotMissingEdgeDetected := true
      if nameUsesChoice && name != ``Classical.choice && !foundChoice then
        choiceMissingEdgeDetected := true
  let propextInfo :=
    buildDominatorInfo ``propext propextSuccessors propextPredecessors
      propextMissingEdgeDetected
  let quotInfo :=
    buildDominatorInfo ``Quot.sound quotSuccessors quotPredecessors quotMissingEdgeDetected
  let choiceInfo :=
    buildDominatorInfo ``Classical.choice choiceSuccessors choicePredecessors
      choiceMissingEdgeDetected
  let mut strictCounts : Std.HashMap Name GainEvidence := {}
  let mut choiceCounts : Std.HashMap Name GainEvidence := {}
  let mut graphInvalid :=
    propextInfo.missingEdgeDetected || quotInfo.missingEdgeDetected ||
      choiceInfo.missingEdgeDetected
  let mut unsupportedOther := 0
  for candidate in candidates do
    if isStrictFrontier candidate then
      if candidate.wholeHasOther then
        unsupportedOther := unsupportedOther + 1
      else
        let mut common? : Option NameSet := none
        if maskUses candidate.wholeMask 1 then
          match dominatorChain propextInfo candidate.name with
          | some nodes => common? := some nodes
          | none => graphInvalid := true
        if maskUses candidate.wholeMask 2 then
          match dominatorChain quotInfo candidate.name with
          | some nodes =>
              common? := some <| common?.map (intersectNameSets · nodes) |>.getD nodes
          | none => graphInvalid := true
        if maskUses candidate.wholeMask 4 then
          match dominatorChain choiceInfo candidate.name with
          | some nodes =>
              common? := some <| common?.map (intersectNameSets · nodes) |>.getD nodes
          | none => graphInvalid := true
        for name in common?.getD {} |>.toArray do
          if isNonAxiomDeclaration env name then
            strictCounts := bumpEvidence strictCounts name candidate.name
    if isChoiceFrontier candidate then
      match dominatorChain choiceInfo candidate.name with
      | some nodes =>
          for name in nodes.toArray do
            if isNonAxiomDeclaration env name then
              choiceCounts := bumpEvidence choiceCounts name candidate.name
      | none => graphInvalid := true
  return (strictCounts, choiceCounts, graphInvalid, unsupportedOther)

private def gainRows (env : Environment) (classes : Std.HashMap Name (Nat × Bool))
    (strictPolicy : Bool) (counts : Std.HashMap Name GainEvidence) :
    Lean.Elab.Command.CommandElabM (Array GainRow) := do
  let entries := counts.toList.mergeSort fun left right =>
    if left.2.theoremCount == right.2.theoremCount then
      left.1.toString < right.1.toString
    else
      left.2.theoremCount > right.2.theoremCount
  let mut rows : Array GainRow := #[]
  for (name, evidence) in entries do
    if rows.size < 100 then
      match env.find? name with
      | some info =>
          let statementAxioms ← exprAxioms info.type
          let (statementMask, statementHasOther) := standardMask statementAxioms
          let policyClean :=
            if strictPolicy then statementMask == 0 && !statementHasOther
            else !usesChoice statementMask
          if policyClean then
            let (candidateMask, candidateHasOther) := classes[name]?.getD (0, false)
            rows := rows.push {
              candidate := name
              theoremCount := evidence.theoremCount
              candidateClass := if candidateHasOther then 8 else candidateMask
              statementClass := if statementHasOther then 8 else statementMask
              kind := declarationKind info
              moduleName := sourceModule env name
              examples := evidence.examples
            }
      | none => pure ()
  return rows

private def writeCounterfactualGains (env : Environment)
    (classes : Std.HashMap Name (Nat × Bool)) (candidates : Array FrontierCandidate) :
    Lean.Elab.Command.CommandElabM Unit := do
  let (strictCounts, choiceCounts, graphInvalid, unsupportedOther) :=
    scoreCounterfactualGains env classes candidates
  if graphInvalid then
    throwError "cycle or missing edge found in an axiom-relevant dependency graph"
  if unsupportedOther != 0 then
    throwError s!"strict frontier contains {unsupportedOther} theorem(s) using an unclassified axiom"
  let strictRows ← gainRows env classes true strictCounts
  let choiceRows ← gainRows env classes false choiceCounts
  let out ← IO.FS.Handle.mk "results/CounterfactualGain.tsv" .write
  out.putStrLn
    "policy\tcandidate\ttheorem_gain\tcandidate_class\tstatement_class\tkind\tmodule\texamples"
  for (policy, rows) in [("strict_zero", strictRows), ("choice_free", choiceRows)] do
    for row in rows do
      out.putStrLn s!"{policy}\t{row.candidate}\t{row.theoremCount}\t{row.candidateClass}\t{row.statementClass}\t{row.kind}\t{row.moduleName}\t{String.intercalate ";" (row.examples.toList.map toString)}"
  out.flush

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
  let mut axiomClasses : Std.HashMap Name (Nat × Bool) := {}
  let mut theoremRows : Array TheoremRow := #[]
  let mut frontierCandidates : Array FrontierCandidate := #[]
  for (name, info) in env.constants do
    let axioms ← Lean.collectAxioms name
    let (mask, hasOther) := standardMask axioms
    axiomClasses := axiomClasses.insert name (mask, hasOther)
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
            theoremRows := theoremRows.push {
              name
              moduleName := sourceModule env name
              statementClass := statementIdx
              wholeClass := idx
            }
            let candidate : FrontierCandidate := {
              name
              statementMask
              statementHasOther
              wholeMask := mask
              wholeHasOther := hasOther
              directProofDependencies := theoremInfo.value.getUsedConstants
            }
            if isStrictFrontier candidate || isChoiceFrontier candidate then
              frontierCandidates := frontierCandidates.push candidate
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
  writeTheoremData theoremRows
  writeDependencyFrequency env axiomClasses frontierCandidates
  writeCounterfactualGains env axiomClasses frontierCandidates
