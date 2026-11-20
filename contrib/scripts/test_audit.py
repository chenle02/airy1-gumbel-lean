#!/usr/bin/env python3
"""Exercise failures that would turn an incomplete Lean package falsely green."""
import tempfile
import importlib.util
from pathlib import Path

path = Path(__file__).with_name('audit.py')
spec = importlib.util.spec_from_file_location('contrib_audit', path)
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)

# --- transcript validation (sibling-parity cases) ---
names = ['A.one', 'A.two']
valid = "'A.one' depends on axioms: [propext]\n'A.two' depends on axioms: [Classical.choice, Quot.sound]\n"
assert len(audit.validate_transcript(valid, names)) == 2
primed = "'A.rpow_half_sq'' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
assert list(audit.validate_transcript(primed, ["A.rpow_half_sq'"])) == ["A.rpow_half_sq'"]
mutations = {
    'missing': valid.splitlines()[0] + '\n',
    'extra': valid + "'A.three' depends on axioms: []\n",
    'replacement': valid.replace('A.two', 'A.other'),
    'duplicate': valid + valid.splitlines()[0] + '\n',
    'unfinished': valid.replace('[propext]', '[sorryAx]'),
    'project axiom': valid.replace('[propext]', '[AiryTailAssumption]'),
    'malformed output': valid + 'unparsed error\n',
}
for name, text in mutations.items():
    try:
        audit.validate_transcript(text, names)
    except ValueError:
        print('PASS rejection:', name)
    else:
        raise AssertionError('False acceptance: ' + name)

# --- namespace/section parser ---
src = """
import Mathlib

namespace Outer
theorem one : True := trivial
section Middle
theorem two : True := trivial
end Middle
private theorem helper : True := trivial
theorem Real.dotted : True := trivial
theorem primed' : True := trivial
section
theorem three : True := trivial
end
end Outer
theorem four : True := trivial
noncomputable section NCSec
theorem five : True := trivial
end NCSec
@[simp] theorem six : True := trivial
@[simp, norm_cast] lemma seven : True := trivial
@[simp] private theorem hidden : True := trivial
"""
got = audit.qualified_names(audit.without_comments(src), 'fixture')
assert got == ['Outer.one', 'Outer.two', 'Outer.Real.dotted', "Outer.primed'",
               'Outer.three', 'four', 'five', 'six', 'seven'], got
print('PASS: same-line attributes are audited; private stays excluded')

bad_blocks = {
    'unbalanced end': 'theorem a : True := trivial\nend\n',
    'mismatched end': 'namespace A\ntheorem a : True := trivial\nend B\n',
    'unclosed namespace': 'namespace A\ntheorem a : True := trivial\n',
}
for name, text in bad_blocks.items():
    try:
        audit.qualified_names(audit.without_comments(text), 'fixture')
    except ValueError:
        print('PASS rejection:', name)
    else:
        raise AssertionError('False acceptance: ' + name)

# --- comment stripper keeps line structure and hides comment tokens ---
stripped = audit.without_comments('/- sorry\n-/\n-- admit\ntheorem t : True := trivial\n')
assert 'sorry' not in stripped and 'admit' not in stripped and stripped.count('\n') == 4

print('PASS: positive inventory plus adversarial transcript, parser, and comment cases')


# Declared-but-unused Lake requirement check.
with tempfile.TemporaryDirectory() as tmp:
    root = Path(tmp)
    (root / 'dep').mkdir()
    (root / 'dep' / 'lakefile.toml').write_text('name = "dep"\n[[lean_lib]]\nname = "DepLib"\n')
    (root / 'lakefile.toml').write_text('name = "pkg"\n[[require]]\nname = "dep"\npath = "dep"\n')
    src = root / 'Src.lean'
    src.write_text('import Mathlib.Foo\n')
    try:
        audit.check_requires(root, [src])
    except ValueError as e:
        assert 'unused' in str(e), e
        print('PASS rejection: declared but unused Lake requirement')
    else:
        raise AssertionError('unused requirement was not rejected')
    src.write_text('-- import DepLib.Hidden\nimport DepLib.Core\n')
    audit.check_requires(root, [src])
    src.write_text('/- import DepLib.Core -/\nimport Mathlib.Foo\n')
    try:
        audit.check_requires(root, [src])
    except ValueError:
        print('PASS rejection: commented-out import does not count as use')
    else:
        raise AssertionError('commented-out import was counted as use')


# check_requires portability (2026-10-28): the tomllib-free fallback parser and the
# enclosing-package lookup for a package used as a path dependency.
import builtins
_real_import = builtins.__import__
def _no_tomllib(name, *a, **k):
    if name == 'tomllib':
        raise ImportError('simulated Python < 3.11')
    return _real_import(name, *a, **k)
toml_text = ('name = "pkg"  # comment\n[[require]]\nname = "dep"\npath = "dep"\n'
             '[[require]]\nname = "mathlib"\ngit = "https://x"\n'
             '[[lean_lib]]\nname = "Lib"\nglobs = ["Lib.*", "Extra.Sub"]\n')
with_tomllib = audit._toml_tables(toml_text, 'require')
builtins.__import__ = _no_tomllib
try:
    without = audit._toml_tables(toml_text, 'require')
    libs = audit._toml_tables(toml_text, 'lean_lib')
finally:
    builtins.__import__ = _real_import
assert [r['name'] for r in without] == ['dep', 'mathlib'] and without[0]['path'] == 'dep', without
assert [{k: r[k] for k in ('name',)} for r in with_tomllib] == [{'name': 'dep'}, {'name': 'mathlib'}]
assert libs == [{'name': 'Lib', 'globs': ['Lib.*', 'Extra.Sub']}], libs
print('PASS: lakefile tables parse identically without tomllib')
with tempfile.TemporaryDirectory() as tmp:
    outer = Path(tmp)
    (outer / '.lake' / 'packages' / 'mathlib').mkdir(parents=True)
    (outer / '.lake' / 'packages' / 'mathlib' / 'lakefile.toml').write_text('name = "mathlib"\n[[lean_lib]]\nname = "Mathlib"\n')
    inner = outer / 'contrib'; inner.mkdir()
    (inner / 'lakefile.toml').write_text('name = "c"\n[[require]]\nname = "mathlib"\ngit = "x"\n')
    s = inner / 'S.lean'; s.write_text('import Mathlib.Foo\n')
    audit.check_requires(inner, [s])
    print('PASS: path-dependency package resolves requires from the enclosing package')
