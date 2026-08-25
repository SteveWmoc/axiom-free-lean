import Mathlib
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean

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
  | _ => #[]

private def shortestAxiomPath (root target : Name) :
    Lean.Elab.Command.CommandElabM (Option (List Name)) := do
  let env := (← getEnv).setExporting false
  let mut queue : Array (Name × List Name) := #[(root, [root])]
  let mut cursor := 0
  let mut seen : NameSet := {}
  seen := seen.insert root
  while cursor < queue.size do
    let (current, path) := queue[cursor]!
    cursor := cursor + 1
    if current == target then return some path
    for dependency in directDependencies env current do
      if !seen.contains dependency then
        seen := seen.insert dependency
        let relevant := dependency == target || (← Lean.collectAxioms dependency).contains target
        if relevant then
          queue := queue.push (dependency, path ++ [dependency])
  return none

private def printPaths (root : Name) : Lean.Elab.Command.CommandElabM Unit := do
  IO.println s!"{root}"
  for target in [``propext, ``Quot.sound, ``Classical.choice] do
    match ← shortestAxiomPath root target with
    | some path => IO.println s!"  {target}: {String.intercalate " -> " (path.map toString)}"
    | none => IO.println s!"  {target}: (not used)"

run_cmd do
  for root in [``List.reverse_reverse, ``Nat.gcd_comm, ``Nat.exists_infinite_primes,
      ``Finset.ext, ``Set.ext, ``LinearMap.ext, ``Filter.Tendsto, ``Real,
      ``HasDerivAt.add] do
    printPaths root
