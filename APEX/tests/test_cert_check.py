"""Negative and positive tests of the certification gate (run: python3 -I APEX/tests/test_cert_check.py)."""
import importlib.util
import sys
import tempfile
from pathlib import Path

here = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("cert_check", here.parent / "cert_check.py")
cc = importlib.util.module_from_spec(spec); spec.loader.exec_module(cc)

EXP = ["A.foo", "A.bar"]
GOOD = ("'A.foo' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n"
        "'A.bar' does not depend on any axioms\n")
cases = {
    "good report": (GOOD, True),
    "empty report": ("", False),
    "missing target": ("'A.foo' depends on axioms: [propext]\n", False),
    "extra target": (GOOD + "'A.baz' depends on axioms: [propext]\n", False),
    "sorryAx": ("'A.foo' depends on axioms: [propext, sorryAx]\n'A.bar' does not depend on any axioms\n", False),
    "native_decide": ("'A.foo' depends on axioms: [Lean.ofReduceBool]\n'A.bar' does not depend on any axioms\n", False),
    "custom axiom": ("'A.foo' depends on axioms: [A.myAxiom, propext]\n'A.bar' does not depend on any axioms\n", False),
    "duplicate verdict": (GOOD + "'A.foo' depends on axioms: [propext]\n", False),
    "lean error": (GOOD + "scripts/Axioms.lean:3:0: error: unknown constant\n", False),
}
fails = 0
for name, (text, ok) in cases.items():
    got = not cc.check_report(text, EXP)
    if got != ok:
        fails += 1; print("WRONG:", name)
if cc.check_report(GOOD, []) == []:
    fails += 1; print("WRONG: empty registry accepted")

srcs = {
    "clean": ("theorem t : 1 = 1 := rfl -- sorry in a comment is fine\n/- admit -/\n", True),
    "sorry with trailing comment": ("theorem t : 1 = 2 := by sorry -- no native_decide here\n", False),
    "native_decide": ("example : 2 + 2 = 4 := by native_decide\n", False),
    "axiom decl": ("axiom cheat : False\n", False),
    "sorry after block comment": ("/- x -/ theorem t : False := sorry\n", False),
    "string literal": ('def s := "sorry"\n', True),
    "nested comment": ("/- a /- b -/ sorry -/\ntheorem t : True := trivial\n", True),
}
for name, (src, ok) in srcs.items():
    with tempfile.TemporaryDirectory() as d:
        Path(d, "X.lean").write_text(src)
        got = not cc.check_sources(Path(d))
    if got != ok:
        fails += 1; print("WRONG:", name)
print("negative tests:", "OK" if not fails else f"{fails} FAILED")
sys.exit(1 if fails else 0)
