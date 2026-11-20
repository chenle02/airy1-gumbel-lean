"""Write Comparator/Challenge.lean and Comparator/Solution.lean (from the package directory contrib/:
python3 scripts/comparator/gen_cs.py) from scripts/comparator/scaffold.json: the scaffold that
`lean-pkg comparator config --from-claims airy1-gumbel-lean-contrib --from-output TYPES.json` wrote
(lean-pkg-signoff.json, configs['comparator.json'].scaffold.todo), each entry with the
round-trip verdict of the type driver's TYPES.json added (`round_trip`, `round_trip_exact`,
`round_trip_open`) and the module lists dropped.

Each Challenge theorem is `Airy1GumbelLeanContribAudit.<decl>`, proved by `sorry`:

* the claimed declaration's elaborated type as Lean prints it, where lean-pkg's round-trip check
  found it syntactically exact (`round_trip_exact`); the printed text uses full names, so it needs
  no `open`;
* otherwise (a printed type that failed the round trip, or re-elaborated only up to definitional
  equality) the declaration's own source text, in the scope context of its file: the `namespace`
  and `section` nesting and every `open`, `variable`, `universe`, `include`, `omit` and
  `set_option` command in force at the declaration, plus the `... in` prefixes directly above it,
  inside a `section` of its own, with Lean's default `autoImplicit true` under which the library is
  compiled; the header is renamed to `_root_.Airy1GumbelLeanContribAudit.<decl>`.

The Solution states the same text and proves each theorem by the copied library theorem
(`Comparator.Defs`, the same name as the library's): `exact @_root_.<decl>` for a printed type,
`apply _root_.<decl> <;> assumption` for a source statement, or a hand-written proof in
scripts/comparator/manual/<decl>.proof.lean. Challenge and Solution import only the copies
(`Comparator.Defs`, which import Mathlib modules only). scripts/comparator/CheckFidelity.lean checks
that every Challenge type equals the claimed declaration's type."""
# Copyright (c) 2026 Le Chen. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
import json
import os
import re

PFX = "Airy1GumbelLeanContribAudit"
HDR = """/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/"""
MANUAL = "scripts/comparator/manual"

todo = json.load(open("scripts/comparator/scaffold.json"))["todo"]
cfg = json.load(open("comparator.json"))
names = cfg["theorem_names"]
assert len(names) == len(set(names))
assert set(names) == {e["theorem_name"] for e in todo}, "the configuration and the scaffold differ"

SCOPE = re.compile(r"^(open|variable|universe|set_option|include|omit|attribute \[local|local notation|local infix)\b")


def strip_comments_keep_lines(lines):
    """A copy of `lines` with block comments (doc comments included) and line comments replaced by
    spaces (same lengths), so that scope commands and `:=` are only recognized in code."""
    out, depth = [], 0
    for l in lines:
        res, i = [], 0
        while i < len(l):
            if depth == 0 and l.startswith("--", i):
                res.append(" " * (len(l) - i))
                break
            if l.startswith("/-", i):
                depth += 1; res.append("  "); i += 2; continue
            if depth > 0 and l.startswith("-/", i):
                depth -= 1; res.append("  "); i += 2; continue
            res.append(l[i] if depth == 0 else " ")
            i += 1
        out.append("".join(res))
    return out


def decl_start(lines, d):
    """The line (1-based) of `theorem <name>` declaring `d` (the last component may carry part of
    the namespace)."""
    last = d.split(".")
    cands = []
    for i, l in enumerate(lines, 1):
        m = re.match(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(theorem|lemma)\s+([^\s({\[:]+)", l)
        if m:
            nm = m.group(2)
            if d == nm or d.endswith("." + nm):
                cands.append(i)
    assert len(cands) == 1, (d, cands)
    return cands[0]


def source_statement(e, proof):
    d = e["decl"]
    lines = open(e["file"], encoding="utf-8").read().split("\n")
    code = strip_comments_keep_lines(lines)
    t = decl_start(lines, d)
    # the declaration's own leading doc comment and attributes, and the `... in` prefixes above
    # comment depth at the start of each line
    dstart, depth = [], 0
    for l in lines:
        dstart.append(depth)
        depth += l.count("/-") - l.count("-/")
    a = t
    while a > 1:
        prev = lines[a - 2]
        if re.match(r"^\s*@\[", prev):
            a -= 1; continue
        if prev.rstrip().endswith("-/"):
            # the doc comment ending just above: up to the line where it opens
            k = a - 1
            while dstart[k - 1] > 0 or "/-" not in lines[k - 1]:
                k -= 1
            a = k; continue
        break
    pre = []
    j = a - 1
    while j >= 1 and re.match(r"^(omit|include|open|set_option|variable)\b.*\bin\s*$", code[j - 1]):
        pre.insert(0, lines[j - 1]); j -= 1
    stack, top = [], []
    i = 0
    while i < j - 1:
        st = code[i].rstrip()
        if st.startswith(" ") or st.startswith("\t") or st == "":
            i += 1; continue
        mns = re.match(r"^namespace\s+(\S+)", st)
        msec = re.match(r"^(noncomputable\s+)?section\b\s*(\S*)", st)
        if mns:
            stack.append(["namespace " + mns.group(1), [], mns.group(1)])
        elif msec and not re.search(r"\bin\s*$", st):
            stack.append([st, [], msec.group(2)])
        elif re.match(r"^end\b", st):
            stack.pop()
        elif SCOPE.match(st) and not re.search(r"\bin\s*$", st):
            cmd = [lines[i]]
            while i + 1 < j - 1 and lines[i + 1].startswith((" ", "\t")) and code[i + 1].strip():
                i += 1; cmd.append(lines[i])
            (stack[-1][1] if stack else top).extend(cmd)
        i += 1
    # the declaration, from its doc comment to the top-level `:=` of the statement
    hdr = "\n".join(lines[a - 1:])
    hcode = "\n".join(code[a - 1:])
    depth, k = 0, 0
    while k < len(hcode):
        c = hcode[k]
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif hcode.startswith(":=", k) and depth == 0 and re.match(r":=[ \t]*(by\b|\n)", hcode[k:]):
            break
        k += 1
    hdr = hdr[:k].rstrip()
    mt = re.search(r"^((?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?)(theorem|lemma)\s+([^\s({\[:]+)", hdr, re.M)
    assert mt, d
    hdr2 = hdr[:mt.start()] + f"theorem _root_.{PFX}.{d}" + hdr[mt.end():]
    # the library is compiled with Lean's default `autoImplicit true` (its lakefile sets no option),
    # so a source statement may bind a variable implicitly (`(hr : 0 < r)`); restate it the same way
    out = [f"section  -- {d}: source statement ({e['file']})", "set_option autoImplicit true"] + top
    for opener, ctx, _ in stack:
        out += [opener] + ctx
    out += pre + [hdr2 + " := by", "  " + proof]
    for opener, _, nm in reversed(stack):
        out += [("end " + nm).rstrip()]
    out += ["end"]
    return "\n".join(out)


CLAIMED = sorted({e["decl"] for e in todo}, key=len, reverse=True)
CLAIMED_RE = re.compile(r"(?<![\w.'])(" + "|".join(re.escape(x) for x in CLAIMED) + r")(?![\w'])")


def printed(e, proof):
    c = "\n".join(l for l in e["challenge"].split("\n") if not l.startswith("-- TODO"))
    # a theorem `PFX.N.x` resolves names in the namespaces `PFX.N` and `PFX` too, so a claimed
    # declaration `N.y` that the printed type mentions (a proof inside the statement) would name the
    # Challenge's own `PFX.N.y`: write it `_root_.N.y` (the header line is left alone)
    head, _, rest = c.partition(f"theorem {PFX}.{e['decl']}")
    assert rest, e["decl"]
    c = head + f"theorem {PFX}.{e['decl']}" + CLAIMED_RE.sub(r"_root_.\1", rest)
    assert c.rstrip().endswith(":= by\n  sorry"), e["decl"]
    return c.rstrip()[: -len("sorry")] + proof


imports = ["Comparator.Defs"]
ch = [HDR] + [f"import {i}" for i in imports] + ["",
    "/-!",
    "# Comparator challenge (trusted): the 103 theorem claims of `airy1-gumbel-lean-contrib`",
    "",
    f"One theorem `{PFX}.<decl>` per theorem claim of `claims.yaml`, each proved by `sorry`.",
    "Each statement is the claimed declaration's elaborated type as Lean prints it (lean-pkg's",
    "round-trip check found the text exact), or, where the printed text is not exact, the",
    "declaration's own source statement in the scope context of its file. The definitions the",
    "statements use are those of `Comparator.Defs`, a verbatim copy of the library (same names; it",
    "imports Mathlib modules only); this file imports nothing else.",
    "`scripts/comparator/CheckFidelity.lean` checks with `Expr` equality that every statement equals",
    "the claimed declaration's type and every copied constant the library's.",
    "",
    "Generated by `scripts/comparator/gen_cs.py`; do not edit.",
    "-/", "", "set_option autoImplicit false", ""]
so = [HDR] + [f"import {i}" for i in imports] + ["",
    "/-!",
    "# Comparator solution (untrusted): each Challenge theorem, proved by its copied proof",
    "",
    "Same names and statements as `Comparator.Challenge`. Each proof applies the copy, in",
    "`Comparator.Defs`, of the claimed library theorem; the library itself is not imported, so the",
    "comparator replays every copied proof.",
    "",
    "Generated by `scripts/comparator/gen_cs.py`; do not edit.",
    "-/", "", "set_option autoImplicit false",
    "-- the printed statements name instance binders they never mention",
    "set_option linter.unusedVariables false", ""]
nsrc = nman = 0
for e in todo:
    d = e["decl"]
    mp = f"{MANUAL}/{d}.proof.lean"
    manual = open(mp).read().rstrip("\n") if os.path.exists(mp) else None
    if e.get("round_trip_exact") is True and e.get("type"):
        assert not e.get("round_trip_open"), d
        c = printed(e, "sorry")
        s = printed(e, manual or f"exact @_root_.{d}")
    else:
        c = source_statement(e, "sorry")
        s = source_statement(e, manual or f"apply _root_.{d} <;> assumption")
        nsrc += 1
    if manual:
        nman += 1
    assert "TODO" not in c and "TODO" not in s, d
    ch += [c, ""]
    so += [s, ""]
open("Comparator/Challenge.lean", "w", encoding="utf-8").write("\n".join(ch))
open("Comparator/Solution.lean", "w", encoding="utf-8").write("\n".join(so))
print(len(todo), "entries:", len(todo) - nsrc, "printed,", nsrc, "from source,", nman, "manual proof(s)")
