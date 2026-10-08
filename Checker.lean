/-
Yang Mills Gap — the judge. A proof of a node is accepted only if:

1. the proof module declares no axioms;
2. every new declaration of the module is re-checked by the Lean kernel (like `leanchecker`),
   which catches environment hacking and `debug.skipKernelTC`;
3. `YangMillsGap.Proved.<id>` is a theorem whose type is exactly `YangMillsGap.Stmt.<id>`
   (the frozen statement from the compiled `YangMillsGap.Statements`);
4. the proof depends only on `propext`, `Classical.choice`, `Quot.sound`
   (`sorry` gives `sorryAx`, `native_decide` gives `Lean.ofReduceBool`: both are rejected).

Proofs are compiled in a sandbox (no network, no file system access) before this check.
Usage: `lake env .lake/build/bin/ymgcheck <module> <id>`. Prints one line of JSON.
-/
import Lean
import Lean.Replay

open Lean

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- All axioms a constant depends on transitively. An unknown constant counts as an axiom. -/
def axiomsOf (env : Environment) (root : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut todo := #[root]
  let mut ax := #[]
  while true do
    let some n := todo.back? | break
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => ax := ax.push n
    | some (.axiomInfo _) => ax := ax.push n
    | some ci =>
      for c in ci.type.getUsedConstants do todo := todo.push c
      if let some v := ci.value? (allowOpaque := true) then
        for c in v.getUsedConstants do todo := todo.push c
      match ci with
      | .inductInfo i => for c in i.ctors do todo := todo.push c
      | .ctorInfo c => todo := todo.push c.induct
      | .recInfo r => for c in r.all do todo := todo.push c
      | _ => pure ()
  return ax

def jsonStr (s : String) : String := (Json.str s).compress

unsafe def check (module : Name) (id : Name) : IO Unit := do
  let thm := `YangMillsGap.Proved ++ id
  let stmt := `YangMillsGap.Stmt ++ id
  let mFile ← findOLean module
  unless (← mFile.pathExists) do throw <| IO.userError s!"no compiled module {module}"
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read the module" else
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  for name in parts[parts.size - 1].1.constNames, ci in parts[parts.size - 1].1.constants do
    if ci matches .axiomInfo _ then
      throw <| IO.userError s!"the proof declares an axiom: {name}"
    newConstants := newConstants.insert name ci
  unless newConstants.contains thm do
    throw <| IO.userError s!"the module has no theorem {thm}"
  -- 2. kernel replay
  discard <| env.toKernelEnv.replay newConstants
  env.freeRegions
  -- 3–4. statement and axioms, in the environment with the module
  let full ← importModules #[{ module }] {} (trustLevel := 0)
  let some ci := full.find? thm | throw <| IO.userError s!"missing {thm}"
  unless ci matches .thmInfo _ do throw <| IO.userError s!"{thm} is not a theorem"
  unless ci.levelParams.isEmpty && ci.type == mkConst stmt do
    throw <| IO.userError s!"the type of {thm} is not the frozen statement {stmt}"
  let bad := (axiomsOf full thm).filter (fun a => !allowedAxioms.contains a)
  unless bad.isEmpty do
    throw <| IO.userError s!"forbidden axioms: {bad.toList}"

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | [modStr, idStr] =>
    try
      check modStr.toName idStr.toName
      IO.println "{\"ok\":true}"
      return 0
    catch e =>
      IO.println s!"\{\"ok\":false,\"error\":{jsonStr (toString e)}}"
      return 1
  | _ =>
    IO.println "{\"ok\":false,\"error\":\"usage: ymgcheck <module> <id>\"}"
    return 2
