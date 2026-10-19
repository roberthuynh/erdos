import Lean

/-!
# Environment-based hygiene check for `check-clean.sh` (B2)

Run as `lean --run tools/Hygiene.lean <TargetModule> <Decl>...` with `LEAN_PATH` set to the fresh build directory
and the pinned packages. It imports `<TargetModule>` and inspects the environment itself (no regex on sources):

* every constant whose defining module is under review (the closure list in the environment variable `OURS`, set by
  `check-clean.sh`; else every module starting with `Openmath`) is classified by kind; it is FLAGGED if it is an
  axiom, an `opaque`, an unsafe or partial definition, or carries `@[implemented_by]` or `@[extern]`, except for
  three named Lean-generated recursion helpers whose source parent is a safe definition;
* axioms are collected by walking the type and value of every such constant and, transitively, of every constant
  they use (Mathlib included), with one shared visited set. This deliberately does not use `Lean.collectAxioms`,
  which in this Lean version reads axiom sets precomputed into imported `.olean` files;
* for each requested `<Decl>`: the module that defines it and its own axiom set (same walk).

Output lines (parsed by `check-clean.sh`): `MODULES ...`, `KINDS ...`, `FLAG ...` (one per flagged constant),
`UNION_AXIOMS [...]`, `DECL <name> module=<M> axioms=[...]` or `DECL <name> missing`, and `HYGIENE ok|fail`.
-/

open Lean

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The modules under review: the comma-separated list in `OURS` (set by `check-clean.sh` to the run's closure),
else every module whose name starts with `Openmath`. -/
def oursList : IO (Option (List Name)) := do
  match (← IO.getEnv "OURS") with
  | some s => return some (((s.splitOn ",").filter (· ≠ "")).map String.toName)
  | none => return none

/-- Axioms reachable from `roots`, walking constant types and values with a shared visited set. -/
partial def axiomsFrom (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut axs : NameSet := {}
  let mut stack : Array Name := roots
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if visited.contains c then continue
    visited := visited.insert c
    match env.find? c with
    | some ci =>
      if ci matches .axiomInfo _ then axs := axs.insert c
      for d in ci.type.getUsedConstants do
        unless visited.contains d do stack := stack.push d
      if let some v := ci.value? (allowOpaque := true) then
        for d in v.getUsedConstants do
          unless visited.contains d do stack := stack.push d
      if let .inductInfo iv := ci then
        for d in iv.ctors do
          unless visited.contains d do stack := stack.push d
    | none => axs := axs.insert (`MISSING ++ c)
  return axs

def showNames (s : NameSet) : String :=
  ",".intercalate ((s.toList.map toString).toArray.qsort (· < ·)).toList

/-- Lean 4.33.1 emits these three private recursion helpers for safe recursive definitions in
`PwCheck`. The list is closed and each parent must still be a safe definition. This exception
does not apply to user definitions, other unsafe helpers, or any axiom/opaque/extern flag. -/
def generatedSafeRecursor (env : Environment) (m n : Name) : Bool :=
  let names := ["Erdos643R3.PwCheck.bb._unsafe_rec",
                "Erdos643R3.PwCheck.kdLoop._unsafe_rec",
                "Erdos643R3.PwCheck.bb2._unsafe_rec"]
  if m != `Openmath.Erdos643R3.PwCheck || !names.contains n.toString then false else
    match env.find? n.getPrefix with
    | some (.defnInfo parent) => parent.safety == .safe
    | _ => false

def main (args : List String) : IO UInt32 := do
  let target := args.head!.toName
  let decls := args.tail!.map String.toName
  initSearchPath (← findSysroot)
  let env0 ← importModules #[{ module := target }] {} (trustLevel := 0)
  let env := env0.setExporting false
  let mods := env.header.moduleNames
  let ol ← oursList
  let isOurs : Name → Bool := fun m => match ol with
    | some l => l.contains m
    | none => (`Openmath).isPrefixOf m
  let ours := mods.filter isOurs
  IO.println s!"MODULES {ours.size} {",".intercalate (ours.map toString).toList}"
  let mut nThm := 0; let mut nDef := 0; let mut nInd := 0; let mut nCtor := 0; let mut nRec := 0
  let mut nAx := 0; let mut nOpq := 0; let mut nQuot := 0
  let mut flags : Array String := #[]
  let mut roots : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := mods[idx.toNat]!
    unless isOurs m do continue
    roots := roots.push n
    match ci with
    | .thmInfo _ => nThm := nThm + 1
    | .defnInfo v =>
      nDef := nDef + 1
      unless v.safety == .safe do
        if generatedSafeRecursor env m n then
          IO.println s!"GENERATED_SAFE_RECURSOR {n} parent={n.getPrefix}"
        else
          flags := flags.push s!"FLAG {n} unsafe-or-partial-def ({m})"
    | .inductInfo _ => nInd := nInd + 1
    | .ctorInfo _ => nCtor := nCtor + 1
    | .recInfo _ => nRec := nRec + 1
    | .axiomInfo _ => nAx := nAx + 1; flags := flags.push s!"FLAG {n} axiom ({m})"
    | .opaqueInfo _ => nOpq := nOpq + 1; flags := flags.push s!"FLAG {n} opaque ({m})"
    | .quotInfo _ => nQuot := nQuot + 1
    if ci.isUnsafe && !generatedSafeRecursor env m n then
      flags := flags.push s!"FLAG {n} unsafe ({m})"
    if (Compiler.getImplementedBy? env n).isSome then flags := flags.push s!"FLAG {n} implemented_by ({m})"
    if isExtern env n then flags := flags.push s!"FLAG {n} extern ({m})"
  IO.println s!"KINDS constants={roots.size} theorems={nThm} defs={nDef} inductives={nInd} ctors={nCtor} recursors={nRec} axioms={nAx} opaques={nOpq} quot={nQuot}"
  for f in flags do IO.println f
  let union := axiomsFrom env roots
  IO.println s!"UNION_AXIOMS [{showNames union}]"
  let badUnion := union.toList.filter (fun a => !allowedAxioms.contains a)
  let mut ok := flags.isEmpty && badUnion.isEmpty
  for d in decls do
    match env.find? d with
    | none => IO.println s!"DECL {d} missing"; ok := false
    | some _ =>
      let m := match env.getModuleIdxFor? d with
        | some idx => toString mods[idx.toNat]!
        | none => "?"
      let axs := axiomsFrom env #[d]
      IO.println s!"DECL {d} module={m} axioms=[{showNames axs}]"
      if axs.toList.any (fun a => !allowedAxioms.contains a) then ok := false
  IO.println s!"HYGIENE {if ok then "ok" else "fail"}"
  return if ok then 0 else 1
