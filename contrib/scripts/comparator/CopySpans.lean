/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen

Input of `gen_defs.py` (read-only; writes nothing). From the package directory `contrib/`:

  lake env lean --run scripts/comparator/CopySpans.lean > SPANS.tsv

For every theorem of the comparator configuration `comparator.json` (named
`Airy1GumbelLeanContribAudit.D`, `D` the claimed declaration), it walks the `Airy1GumbelContrib`
constants reachable from `D` itself, its proof included (through the types and values of project
definitions, theorems, opaques and inductives), and prints
`REACH<TAB>name<TAB>module<TAB>first line<TAB>last line` (`-` when the constant has no source
range, e.g. a generated `_proof_N`), then `ALL<TAB>name<TAB>module<TAB>first<TAB>last` for every
ranged declaration of every project module. Extra roots come from
`scripts/comparator/extra_reach.txt` (one name per line, `#` comments). Adapted from the
l1-delta and stratonovich-ham-second-moment-lean companions.
-/
import Lean
import Airy1GumbelContrib
open Lean

def projMod? (env : Environment) (c : Name) : Option Name := do
  let i ← env.getModuleIdxFor? c
  let m := env.header.moduleNames[i.toNat]!
  if (`Airy1GumbelContrib).isPrefixOf m then some m else none

/-- A printed name, with numeric components (`_private.M.0.N`) read back as numbers. -/
def parseName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n p => match p.toNat? with
    | some k => .num n k
    | none => .str n p) .anonymous

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Airy1GumbelContrib }] {}
  let cfgPath := (← IO.getEnv "CMP_CONFIG").getD "comparator.json"
  let cfg ← IO.ofExcept <| Json.parse (← IO.FS.readFile cfgPath)
  let names ← IO.ofExcept <| cfg.getObjValAs? (Array String) "theorem_names"
  let pfx := "Airy1GumbelLeanContribAudit."
  let mut work : Array Name := #[]
  for s in names do
    unless s.startsWith pfx do throw <| IO.userError s!"{s}: not under {pfx}"
    let d := parseName (s.drop pfx.length).toString
    unless env.contains d do throw <| IO.userError s!"unknown declaration {d}"
    -- the claimed theorem itself is copied with its proof: the Solution proves the Challenge
    -- statement by the copy, so no bridge between copies and library is needed
    work := work.push d
  -- CMP_TYPES_ONLY=1: roots are the constants of the claimed TYPES (definitions-only reach)
  if (← IO.getEnv "CMP_TYPES_ONLY") == some "1" then
    work := work.foldl (fun acc d => acc ++ ((env.find? d).map (·.type.getUsedConstants)).getD #[]) #[]
  if ← System.FilePath.pathExists "scripts/comparator/extra_reach.txt" then
    for l in ← IO.FS.lines "scripts/comparator/extra_reach.txt" do
      let l := l.trimAscii.toString
      if l.isEmpty || l.startsWith "#" then continue
      let n := parseName l
      unless env.contains n do throw <| IO.userError s!"extra_reach: unknown declaration {n}"
      work := work.push n
  let mut seen : NameSet := {}
  let mut reach : Array (Name × Name) := #[]
  while h : work.size > 0 do
    let c := work.back
    work := work.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some m := projMod? env c | continue
    let some cc := env.find? c | continue
    reach := reach.push (c, m)
    work := work ++ cc.type.getUsedConstants
    match cc with
    | .defnInfo v => work := work ++ v.value.getUsedConstants
    | .thmInfo v => work := work ++ v.value.getUsedConstants
    | .opaqueInfo v => work := work ++ v.value.getUsedConstants
    | .inductInfo v => work := work ++ v.ctors.toArray
    | .ctorInfo v => work := work.push v.induct
    | .recInfo v => work := work.push v.getMajorInduct
    | _ => pure ()
  let ctx : Core.Context := { fileName := "<CopySpans>", fileMap := default }
  let st : Core.State := { env }
  let span (n : Name) : IO String := do
    let (r, _) ← (findDeclarationRanges? n : CoreM _).toIO ctx st
    return match r with
      | some r => s!"{r.range.pos.line}\t{r.range.endPos.line}"
      | none => "-\t-"
  for (c, m) in reach.qsort (fun a b => a.1.toString < b.1.toString) do
    IO.println s!"REACH\t{c}\t{m}\t{← span c}"
  for mi in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[mi]!
    unless (`Airy1GumbelContrib).isPrefixOf m do continue
    for n in env.header.moduleData[mi]!.constNames do
      let s ← span n
      unless s.startsWith "-" do IO.println s!"ALL\t{n}\t{m}\t{s}"
  return 0
