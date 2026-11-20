#!/usr/bin/env python3
"""Exercise failures that would turn an incomplete Lean package falsely green."""
import importlib.util
from pathlib import Path

path = Path(__file__).with_name('audit.py')
spec = importlib.util.spec_from_file_location('airy1_audit', path)
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
names = ['A.one', 'A.two']
valid = "'A.one' depends on axioms: [propext]\n'A.two' depends on axioms: [Classical.choice, Quot.sound]\n"
assert len(audit.validate_transcript(valid, names)) == 2
primed = "'Airy1Gumbel.foo'' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
assert list(audit.validate_transcript(primed, ["Airy1Gumbel.foo'"])) == ["Airy1Gumbel.foo'"]
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

# Attribute-prefixed declarations must be inventoried (blind spot fixed with
# the @[simp] natCast bridges): a same-line attribute block before
# theorem/lemma does not exempt the declaration from the exact inventory.
import tempfile
with tempfile.TemporaryDirectory() as tmp:
    root = Path(tmp)
    (root / 'Airy1Gumbel').mkdir()
    (root / 'Airy1Gumbel' / 'Foo.lean').write_text(
        'namespace Airy1Gumbel\n\n'
        '@[simp] lemma bar : True := trivial\n\n'
        'theorem baz : True := trivial\n\n'
        "@[simp, measurability] theorem bar' : True := trivial\n\n"
        'end Airy1Gumbel\n')
    (root / 'Airy1Gumbel.lean').write_text('import Airy1Gumbel.Foo\n')
    check_lines = ('#print axioms Airy1Gumbel.bar\n#print axioms Airy1Gumbel.baz\n'
                   "#print axioms Airy1Gumbel.bar'\n")
    (root / 'AxiomCheck.lean').write_text('import Airy1Gumbel\n' + check_lines)
    got = audit.inventory(root)
    assert got == ['Airy1Gumbel.bar', 'Airy1Gumbel.baz', "Airy1Gumbel.bar'"], got
    print('PASS attribute-prefixed inventory:', got)
    (root / 'AxiomCheck.lean').write_text(
        'import Airy1Gumbel\n#print axioms Airy1Gumbel.baz\n')
    try:
        audit.inventory(root)
    except ValueError:
        print('PASS rejection: attribute-prefixed declaration missing from AxiomCheck')
    else:
        raise AssertionError('False acceptance: attribute-prefixed inventory gap')

print('PASS: positive inventory and seven adversarial transcript cases, '
      'plus attribute-prefixed inventory positive and rejection')


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
