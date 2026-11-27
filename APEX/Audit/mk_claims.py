import json, re, csv, sys
res = open(sys.argv[1]).read(); cov = open(sys.argv[2]).read(); out = sys.argv[3]
claims = []
for line in res.splitlines():
    m = re.match(r"^\| ([AB]\d+) \| (.*?) \| (.*?) \| (.*?) \|(?: (.*?) \|)?$", line)
    if not m: continue
    cid, src, c1, c2, c3 = m.groups()
    if cid.startswith("A"):
        claims.append(dict(id="FBS3R-"+cid, source=src, original_statement=c1, finding=c2, lean=c3,
            status="DISPROVED", lean_package="Lean/FBS3R-Lean", kernel_checked=True,
            novelty="error found in archive paper; not a world-priority claim"))
    else:
        claims.append(dict(id="FBS3R-"+cid, source=src, original_statement=c1, finding=c1, lean=c2,
            status="PROVED", lean_package="Lean/FBS3R-Lean", kernel_checked=True,
            novelty="NEW_FORMALIZATION of an archive statement (mathematics mostly classical)"))
new = [
 dict(id="APEX-PXP-1", source="2026_10_23 Rational Spectral Hierarchies, Thm th:denom",
      original_statement="sum_n Tr A_n^{2m} z^n = P_m/(1-z-z^2)^{m+1}, deg P_m <= 3m+2",
      finding="PROVED for all m>=1 with the sharper bound deg P_m <= 3m-2 (Tr = trace of the Fibonacci-cube adjacency matrix)",
      lean="APEX.PXP.pxp_moment_rational", status="PROVED", lean_package="APEX/Lean", kernel_checked=True,
      novelty="NEW_THEOREM_CANDIDATE (sharpening of the archive bound); literature search not exhaustive"),
 dict(id="APEX-PXP-2", source="this work", original_statement="P_m == (2m)! z^(2m-1) mod (1-z-z^2) in Z[z]; 1-z-z^2 does not divide P_m, so the denominator (1-z-z^2)^(m+1) is sharp",
      finding="PROVED for all m>=1", lean="APEX.PXP.pxp_moment_residue, APEX.PXP.pxp_denominator_sharp",
      status="PROVED", lean_package="APEX/Lean", kernel_checked=True, novelty="NEW_THEOREM_CANDIDATE; literature search not exhaustive"),
 dict(id="APEX-PXP-5", source="2026_10_23 Rational Spectral Hierarchies, Cor. cor:moment, eqs (4th),(6th)",
      original_statement="explicit rational GFs of Tr A_n^4 and Tr A_n^6",
      finding="PROVED for all n (first coefficients by decide +kernel, no native_decide)", lean="APEX.PXP.fourth_moment_gf, APEX.PXP.sixth_moment_gf",
      status="PROVED", lean_package="APEX/Lean", kernel_checked=True, novelty="NEW_FORMALIZATION of archive formulas"),
 dict(id="APEX-PXP-6", source="2026_10_23 Rational Spectral Hierarchies, eq (8th)",
      original_statement="explicit rational GF of Tr A_n^8", finding="exact-integer check only (pxp_verify.py); Lean kernel evaluation of Tr A_10^8 not attempted",
      lean=None, status="NUMERICAL_ONLY", lean_package=None, kernel_checked=False, novelty="archive formula"),
 dict(id="APEX-PXP-3", source="this work", original_statement="deg P_m = 3m-2 exactly (leading coefficient (-1)^(m-1) c(m,0), c(m,0)>0)",
      finding="exact-integer check m<=5; proof sketch (pattern decomposition) in manuscript; Lean pending",
      lean=None, status="NUMERICAL_ONLY", lean_package=None, kernel_checked=False, novelty="NEW_THEOREM_CANDIDATE"),
 dict(id="APEX-PXP-4", source="this work", original_statement="with uniform field mu: sum_n Tr (A_n+mu N)^k z^n has denominator (1-z-z^2)^(k+1)",
      finding="exact-integer check mu=1, k<=3 only", lean=None, status="OPEN", lean_package=None, kernel_checked=False,
      novelty="conjecture"),
]
claims += new
with open(out+"/CLAIMS.jsonl","w") as f:
    for c in claims: f.write(json.dumps(c, ensure_ascii=False)+"\n")
rows=[]
for line in cov.splitlines():
    if line.startswith("| 20"):
        parts=[p.strip() for p in line.strip().strip("|").split(" | ")]
        rows.append((parts[0],parts[1]," | ".join(parts[2:])))
with open(out+"/COVERAGE_MATRIX.csv","w",newline="") as f:
    w=csv.writer(f); w.writerow(["folder","status","note"])
    for r in rows: w.writerow(r)
print(len(claims), "claims;", len(rows), "coverage rows")
