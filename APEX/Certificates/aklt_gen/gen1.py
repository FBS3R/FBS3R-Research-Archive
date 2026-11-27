exec(open('peel.py').read().split("print(len(known)")[0])
def nm(t): return "h"+"".join(map(str,t))
L=[]
for l in range(5):
    t=(0,4-l,l,4)
    L.append(f"  have {nm(t)} : φ 0 {4-l} {l} 4 = 0 := by simpa using hpin {l}")
known=list(pins)
for kind,e,u in steps:
    hyp = "hP" if kind=='p' else "hM"
    dep=[nm(v) for v in (eqs_d[(kind,e)]) if v!=u]
    L.append(f"  have {nm(u)} : φ {' '.join(map(str,u))} = 0 := by")
    L.append(f"    have h := {hyp} {' '.join(map(str,e))}")
    L.append(f"    simp [{'SpTotf, sp1' if kind=='p' else 'SmTotf, sm1'}, {', '.join(dep)}] at h")
    L.append(f"    omega")
open('peel_haves.lean','w').write("\n".join(L)+"\n")
