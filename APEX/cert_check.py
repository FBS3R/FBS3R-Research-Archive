"""Certification gate for APEX (stdlib only).

check_report: the `#print axioms` output must contain exactly one verdict line for every theorem in the
registry (APEX/Audit/ACCEPTED_THEOREMS.txt), no theorem outside it, and only standard axioms.
check_sources: no forbidden construct in Lean code; comments and string literals are stripped first,
so appending a comment to a line cannot hide a `sorry`.
"""
import re
import sys
from pathlib import Path

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"(?<![\w.'])(sorry|admit|native_decide|sorryAx|axiom|implemented_by|extern|unsafe"
                       r"|ofReduceBool|ofReduceNat|decide_eq_true_eval_native)(?![\w'])")


def strip_lean(src: str) -> str:
    """Remove nested block comments, line comments and string literals (keeping newlines)."""
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            if src[i] == "\n": out.append("\n")
            i += 1; continue
        if src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j; continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append('""'); i = j + 1; continue
        out.append(src[i]); i += 1
    if depth:
        raise ValueError("unterminated block comment")
    return "".join(out)


def check_sources(root: Path) -> list:
    errs = []
    for f in sorted(root.rglob("*.lean")):
        if ".lake" in f.parts:
            continue
        code = strip_lean(f.read_text(encoding="utf-8"))
        for ln, line in enumerate(code.splitlines(), 1):
            m = FORBIDDEN.search(line)
            if m:
                errs.append(f"{f}:{ln}: forbidden `{m.group(1)}`")
    return errs


def parse_report(text: str) -> dict:
    flat = re.sub(r"\s+", " ", text)
    res = {}
    for m in re.finditer(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", flat):
        name = m.group(1)
        axs = {a.strip() for a in (m.group(3) or "").split(",") if a.strip()}
        if name in res:
            raise ValueError(f"duplicate verdict for {name}")
        res[name] = axs
    return res


def check_report(text: str, expected: list) -> list:
    errs = []
    if not expected:
        return ["empty registry"]
    try:
        rep = parse_report(text)
    except ValueError as e:
        return [str(e)]
    if not rep:
        return ["no axiom verdicts in report"]
    for name in expected:
        if name not in rep:
            errs.append(f"missing verdict: {name}")
    for name, axs in rep.items():
        if name not in expected:
            errs.append(f"unregistered target: {name}")
        bad = axs - STANDARD
        if bad:
            errs.append(f"non-standard axioms in {name}: {sorted(bad)}")
    if re.search(r"\berror\b", text):
        errs.append("Lean reported an error")
    return errs


def read_registry(path: Path) -> list:
    names = [l.split("#")[0].strip() for l in path.read_text().splitlines()]
    names = [n for n in names if n]
    if len(set(names)) != len(names):
        raise SystemExit("duplicate names in registry")
    return names


def targets_in_script(path: Path) -> list:
    return re.findall(r"^#print axioms\s+(\S+)", path.read_text(), re.M)


def main(argv):
    report, registry, script, src = Path(argv[1]), Path(argv[2]), Path(argv[3]), Path(argv[4])
    expected = read_registry(registry)
    errs = []
    tg = targets_in_script(script)
    if sorted(tg) != sorted(expected):
        errs.append(f"Axioms.lean targets differ from registry: "
                    f"missing {sorted(set(expected) - set(tg))}, extra {sorted(set(tg) - set(expected))}")
    errs += check_report(report.read_text(), expected)
    errs += check_sources(src)
    for e in errs:
        print("FAIL:", e)
    if errs:
        return 1
    print(f"OK: {len(expected)} registered targets, standard axioms only, sources clean")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
