#!/usr/bin/env python3
"""Regenerate derived registries from the source of truth (APEX_RESULTS.json + scripts/Axioms.lean output).
Usage: python3 APEX/Audit/sync_registries.py [--axioms AXIOMS_OUTPUT.txt]
Writes: APEX_CLAIMS.jsonl, PROOF_MANIFEST.json, AXIOM_REPORT.txt (if axioms output given), SHA256SUMS.txt."""
import json, sys, hashlib, pathlib, re, datetime, subprocess
A = pathlib.Path(__file__).resolve().parent; APEX = A.parent; LEAN = APEX / "Lean"
res = json.load(open(A / "APEX_RESULTS.json"))
with open(A / "APEX_CLAIMS.jsonl", "w") as f:
    for e in res: f.write(json.dumps(e, ensure_ascii=False) + "\n")
targets = [l.split()[2] for l in open(LEAN / "scripts/Axioms.lean") if l.startswith("#print axioms ")]
reg = set(x.strip() for e in res for n in (e["lean"] if isinstance(e["lean"], list) else [e["lean"]]) for x in n.split(","))
man = {"date": datetime.date.today().isoformat(), "lean": "4.36.0 (611c117b)", "mathlib": "fc4f59e5 (v4.36.0)",
       "accepted_axioms": ["propext", "Classical.choice", "Quot.sound"], "axiom_targets": len(targets),
       "registered_results": len(res), "targets_in_registry": len([t for t in targets if t in reg]),
       "results": [{"claim": e["id"], "area": e.get("area"), "status": e["status"], "novelty": e.get("novelty"),
                    "lean": e["lean"], "file": e.get("file"), "scope": e.get("scope")} for e in res]}
json.dump(man, open(A / "PROOF_MANIFEST.json", "w"), ensure_ascii=False, indent=1)
if "--axioms" in sys.argv:
    out = open(sys.argv[sys.argv.index("--axioms") + 1]).read()
    lines = [l for l in out.splitlines() if "axioms" in l]
    bad = [l for l in lines if not re.search(r"depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$|does not depend on any axioms", l)]
    hdr = (f"AXIOM REPORT — FBS3R-APEX (generated {man['date']} by sync_registries.py)\n"
           f"Toolchain: Lean 4.36.0, Mathlib v4.36.0. Accepted: propext, Classical.choice, Quot.sound.\n"
           f"Targets: {len(targets)}; lines: {len(lines)}; non-standard: {len(bad)}\n\n")
    open(A / "AXIOM_REPORT.txt", "w").write(hdr + "\n".join(lines) + "\n")
    if bad: print("NON-STANDARD:", *bad, sep="\n"); sys.exit(1)
with open(A / "SHA256SUMS.txt", "w") as f:
    for p in sorted(LEAN.glob("APEX/**/*.lean")) + [LEAN / "APEX.lean", LEAN / "scripts/Axioms.lean"]:
        f.write(f"{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(APEX.parent)}\n")
print(f"synced: {len(res)} results, {len(targets)} targets, {man['targets_in_registry']} registered")
