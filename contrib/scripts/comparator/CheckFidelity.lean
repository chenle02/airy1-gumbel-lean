/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen

Statement-fidelity check for the comparator tier (read-only; writes nothing). From `contrib/`,
after `lake build Airy1GumbelContrib Comparator.Challenge`:

  lake env lean --run scripts/comparator/CheckFidelity.lean

The copies (`Comparator.Defs.*`) keep the library's declaration names, so they cannot share one
environment with the library. This program imports the library `Airy1GumbelContrib` only, reads
the compiled copy modules and `Comparator.Challenge` from their `.olean` files without adding
them to the environment (`readModuleData`), and checks with `Expr` equality (`==`: no unfolding,
no definitional equality):

1. every copy module `Comparator.Defs.M` declares exactly the constants of the library module
   `M` (notation syntax constants aside: parser, macro and unexpander constants, whose names and
   strings carry the module name and which no statement or definition mentions), and each
   equals the library's constant of the same name: kind, universe parameters,
   type, value (definitions, opaques; for a theorem the type only, proofs being irrelevant), and
   inductive, constructor and recursor data. A private name `_private.Comparator.Defs.M.0.N` is
   read as `_private.M.0.N`, inside every expression too;
2. every theorem of `theorem_names` of `comparator.json` is listed once, is declared by
   `Comparator.Challenge`, is `Airy1GumbelLeanContribAudit.D` for a library theorem `D` of a
   theorem claim of `claims.yaml`, and its type (and universe parameters) equals the type of `D`.
   A proof that Lean lifts out of a restated type (`Airy1GumbelLeanContribAudit.D._proof_N`) is
   read as the library's `D._proof_N`, and the two auxiliary theorems must have equal types.

So each Challenge statement is the claimed declaration's elaborated type, and every constant it
mentions is the library's constant, by name and by content. It prints one line per problem and a
summary; exit 0 only when there is none.
-/
import Lean
import Airy1GumbelContrib
open Lean

/-- The prefix of the Challenge theorems. -/
def cpfx : Name := `Airy1GumbelLeanContribAudit
/-- The module prefix of the copies. -/
def dpfx : Name := `Comparator.Defs
def libRoot : Name := `Airy1GumbelContrib

/-- `pre ++ n ↦ n` on names, `none` when `pre` is not a prefix. -/
def dropPrefix? (pre n : Name) : Option Name :=
  let s := n.toString (escape := false)
  let p := pre.toString (escape := false) ++ "."
  if s.startsWith p then some (parseName (s.drop p.length).toString) else none
where
  parseName (s : String) : Name :=
    (s.splitOn ".").foldl (fun n p => match p.toNat? with
      | some k => .num n k
      | none => .str n p) .anonymous

/-- Rebuild `n` with its leading component sequence `a` replaced by `b`. -/
partial def replacePrefix (n a b : Name) : Name :=
  if n == a then b else
  match n with
  | .str p s => .str (replacePrefix p a b) s
  | .num p k => .num (replacePrefix p a b) k
  | .anonymous => .anonymous

/-- A copy's name read as the library's: `_private.Comparator.Defs.M.0.N ↦ _private.M.0.N`;
`Airy1GumbelLeanContribAudit.D._proof_N ↦ D._proof_N`; every other name unchanged. -/
def rn (n : Name) : Name :=
  if isPrivateName n then
    -- `_private.<module>.0.<name>`: replace the module part
    let pre := Name.mkStr .anonymous "_private"
    let s := n.toString (escape := false)
    if s.startsWith "_private.Comparator.Defs." then
      replacePrefix n (pre ++ dpfx) pre
    else n
  else
    match dropPrefix? cpfx n with
    | some d => if d.isStr && (d.getString!.startsWith "_proof_") then d else n
    | none => n

partial def ren (e : Expr) : Expr :=
  e.replace fun
    | .const n us => some (.const (rn n) us)
    | .proj s i b => some (.proj (rn s) i (ren b))
    | _ => none

/-- The first differing pair of subterms (for the problem report only). -/
partial def firstDiff (a b : Expr) : Option (Expr × Expr) :=
  if a == b then none else
  match a, b with
  | .app f x, .app g y => (firstDiff f g).orElse fun _ => firstDiff x y
  | .lam _ t x _, .lam _ u y _ => (firstDiff t u).orElse fun _ => firstDiff x y
  | .forallE _ t x _, .forallE _ u y _ => (firstDiff t u).orElse fun _ => firstDiff x y
  | .letE _ t v x _, .letE _ u w y _ =>
    ((firstDiff t u).orElse fun _ => firstDiff v w).orElse fun _ => firstDiff x y
  | .mdata _ x, .mdata _ y => firstDiff x y
  | .proj _ i x, .proj _ j y => if i == j then firstDiff x y else some (a, b)
  | _, _ => some (a, b)

def showDiff (a b : Expr) : String :=
  match firstDiff a b with
  | some (x, y) => s!"\n    copy/challenge: {(toString x).take 300}\n    library:        {(toString y).take 300}"
  | none => ""

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

/-- The differing field of a copy `c` and the library constant `p`, if any. -/
def differs (c p : ConstantInfo) : Option String :=
  if kind c != kind p then some s!"kind {kind c} vs {kind p}"
  else if c.levelParams != p.levelParams then some s!"universe parameters {c.levelParams} vs {p.levelParams}"
  else if ren c.type != p.type then some s!"type{showDiff (ren c.type) p.type}"
  else match c, p with
    | .defnInfo a, .defnInfo b =>
      if ren a.value != b.value then some s!"value{showDiff (ren a.value) b.value}"
      else if a.safety != b.safety then some "safety" else none
    | .thmInfo _, .thmInfo _ => none  -- a proof is irrelevant: the type is compared above
    | .opaqueInfo a, .opaqueInfo b =>
      if ren a.value != b.value then some "value" else if a.isUnsafe != b.isUnsafe then some "safety" else none
    | .axiomInfo a, .axiomInfo b => if a.isUnsafe != b.isUnsafe then some "safety" else none
    | .inductInfo a, .inductInfo b =>
      if a.ctors.map rn != b.ctors || a.all.map rn != b.all
        || a.numParams != b.numParams || a.numIndices != b.numIndices || a.numNested != b.numNested
        || a.isRec != b.isRec || a.isUnsafe != b.isUnsafe || a.isReflexive != b.isReflexive
      then some "inductive data" else none
    | .ctorInfo a, .ctorInfo b =>
      if rn a.induct != b.induct || a.cidx != b.cidx || a.numParams != b.numParams
        || a.numFields != b.numFields || a.isUnsafe != b.isUnsafe then some "constructor data" else none
    | .recInfo a, .recInfo b =>
      if a.all.map rn != b.all || a.numParams != b.numParams || a.numIndices != b.numIndices
        || a.numMotives != b.numMotives || a.numMinors != b.numMinors || a.k != b.k
        || a.isUnsafe != b.isUnsafe || a.rules.length != b.rules.length
        || (a.rules.zip b.rules).any (fun (x, y) =>
             rn x.ctor != y.ctor || x.nfields != y.nfields || ren x.rhs != y.rhs)
      then some "recursor data" else none
    | _, _ => some "kind"

/-- Parser, macro and unexpander constants that a `notation` command generates: syntax, never
part of an elaborated statement or definition (their names and strings carry the module name). -/
def syntaxOnly (c : ConstantInfo) : Bool :=
  match c.type.getAppFn with
  | .const n _ => n == ``Lean.ParserDescr || n == ``Lean.TrailingParserDescr
      || n == ``Lean.Macro || n == ``Lean.PrettyPrinter.Unexpander
  | _ => false

/-- The olean of module `m` in the package build directory. -/
def olean (m : Name) : System.FilePath :=
  (m.components.foldl (fun p c => p / c.toString (escape := false)) (".lake/build/lib/lean" : System.FilePath))
    |>.addExtension "olean"

/-- The `decl:` and `kind:` values of the claims of `claims.yaml` (a line-level read of the
two keys, which the claims schema keeps on one line each). -/
def theoremClaims : IO (Array Name) := do
  let mut out := #[]
  let mut decl : Option String := none
  for l in ← IO.FS.lines "claims.yaml" do
    let t := l.trimAscii.toString
    if t.startsWith "- id:" then decl := none
    if t.startsWith "decl:" then decl := some (t.drop 5).trimAscii.toString
    if t.startsWith "kind:" then
      if (t.drop 5).trimAscii.toString == "theorem" then
        if let some d := decl then out := out.push d.toName
  return out

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := libRoot }] {}
  let mut problems := 0
  let mut nConsts := 0
  let mut nMods := 0
  let mut nSyntax := 0
  let mut libNames : NameSet := {}
  let mut copyNames : NameSet := {}
  -- 1. the copies, module by module
  for mi in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[mi]!
    unless libRoot.isPrefixOf m && m != libRoot do continue
    let cm := dpfx ++ m
    let path := olean cm
    unless ← path.pathExists do
      IO.println s!"PROBLEM {cm}: no compiled copy ({path})"; problems := problems + 1; continue
    let (md, _) ← readModuleData path
    nMods := nMods + 1
    for c in env.header.moduleData[mi]!.constants do
      if syntaxOnly c then nSyntax := nSyntax + 1 else libNames := libNames.insert c.name
    for c in md.constants do
      unless syntaxOnly c do copyNames := copyNames.insert (rn c.name)
    for c in md.constants do
      if syntaxOnly c then continue
      let n := rn c.name
      match env.find? n with
      | none => IO.println s!"PROBLEM {c.name}: no library constant {n}"; problems := problems + 1
      | some p =>
        match differs c p with
        | some f => IO.println s!"PROBLEM {c.name}: {f}"; problems := problems + 1
        | none => nConsts := nConsts + 1
  -- the same declarations: every library constant has a copy (an equation or congruence lemma
  -- that Lean realizes on demand may sit in another module of either side, so the sets are
  -- compared over all modules)
  for n in libNames do
    unless copyNames.contains n do
      IO.println s!"PROBLEM {n}: no copy"; problems := problems + 1
  -- 2. the Challenge theorems
  let chPath := olean `Comparator.Challenge
  let (ch, _) ← readModuleData chPath
  let chConsts : NameMap ConstantInfo := ch.constants.foldl (fun m c => m.insert c.name c) {}
  let claimed := ← theoremClaims
  let cfg ← IO.ofExcept <| Json.parse (← IO.FS.readFile "comparator.json")
  let names ← IO.ofExcept <| cfg.getObjValAs? (Array String) "theorem_names"
  let mut seen : NameSet := {}
  let mut nThms := 0
  let mut nAux := 0
  for s in names do
    let n := dropPrefix?.parseName s
    if seen.contains n then
      IO.println s!"PROBLEM {n}: listed twice"; problems := problems + 1
    seen := seen.insert n
    let some c := chConsts.find? n
      | IO.println s!"PROBLEM {n}: not declared by Comparator.Challenge"; problems := problems + 1; continue
    let some d := dropPrefix? cpfx n
      | IO.println s!"PROBLEM {n}: not under {cpfx}"; problems := problems + 1; continue
    unless claimed.contains d do
      IO.println s!"PROBLEM {n}: {d} is not the decl of a theorem claim"; problems := problems + 1
    match env.find? d with
    | none => IO.println s!"PROBLEM {n}: no library declaration {d}"; problems := problems + 1
    | some p =>
      if !p.isTheorem then IO.println s!"PROBLEM {n}: {d} is not a theorem"; problems := problems + 1
      else if !c.isTheorem then IO.println s!"PROBLEM {n}: not a theorem"; problems := problems + 1
      else if c.levelParams != p.levelParams then
        IO.println s!"PROBLEM {n}: universe parameters {c.levelParams} vs {p.levelParams}"; problems := problems + 1
      else if ren c.type != p.type then
        IO.println s!"PROBLEM {n}: type differs from {d}{showDiff (ren c.type) p.type}"; problems := problems + 1
      else nThms := nThms + 1
      -- proofs lifted out of the restated type: equal types to the library's auxiliaries
      for a in c.type.getUsedConstants do
        if let some ad := dropPrefix? cpfx a then
          match chConsts.find? a, env.find? ad with
          | some ac, some ap =>
            if ac.isTheorem && ap.isTheorem && ren ac.type == ap.type then nAux := nAux + 1
            else IO.println s!"PROBLEM {a}: auxiliary differs from {ad}"; problems := problems + 1
          | _, _ => IO.println s!"PROBLEM {a}: no library auxiliary {ad}"; problems := problems + 1
  -- every theorem claim is compared
  for d in claimed do
    unless seen.contains (cpfx ++ d) do
      IO.println s!"PROBLEM {d}: a theorem claim with no Challenge theorem"; problems := problems + 1
  IO.println s!"fidelity: {nMods} copied module(s), {nConsts} copied constant(s) equal to the library's ({nSyntax} notation syntax constant(s) of the library not compared); {nThms} of {names.size} Challenge theorem type(s) equal to the claimed declaration's ({nAux} lifted proof auxiliary(ies) checked); {problems} problem(s)"
  return if problems == 0 then 0 else 1
