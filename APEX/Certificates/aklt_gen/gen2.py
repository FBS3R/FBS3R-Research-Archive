import pickle
from fractions import Fraction as F
exec(open('/home/claude/repo/APEX/Certificates/aklt_cert.py').read().split("# ---------------------------------------------------------------- one site")[0].replace("import sys",""))
d=pickle.load(open('cert.pkl','rb'))
Ms=d['Ms']; PAIRS=d['PAIRS']
def q(x):
    x=F(x)
    return str(x.numerator) if x.denominator==1 else f"{x.numerator}/{x.denominator}"
def qp(x):
    s=q(x); return s if '/' not in s and not s.startswith('-') else f"({s})"
def mlit(A): return "!![" + "; ".join(", ".join(q(x) for x in r) for r in A) + "]"
def vlit(v): return "![" + ", ".join(q(x) for x in v) + "]"
def mpow(A,k):
    R=eye(len(A))
    for _ in range(k): R=mul(R,A)
    return R
out=[]
ops=[mpow(Ms[p],k) for p in PAIRS for k in range(1,5)]
out.append("/-- literal table of the 24 operators `X_p^k` (`p` = 01,02,03,12,13,23; `k` = 1..4). -/")
out.append("def opsT : Fin 24 → Matrix (Fin 5) (Fin 5) ℚ := ![\n  " + ",\n  ".join(mlit(A) for A in ops) + "]")
pos=[(0,1),(0,2),(0,3),(4,1),(4,2),(4,3)]
Lb=[[A[i][j] for A in ops] for (i,j) in pos]
assert rank(Lb)==6
R,piv=rref(Lb)
free=[c for c in range(24) if c not in piv]
ker=nullspace(Lb); assert len(ker)==18
# right inverse: Cm (24x6) supported on piv
Bp=[[Lb[i][c] for c in piv] for i in range(6)]
Bi=inv(Bp)
Cm=zeros(24,6)
for a,c in enumerate(piv):
    for m in range(6): Cm[c][m]=Bi[a][m]
assert mul(Lb,Cm)==eye(6)
out.append("/-- right inverse of the leakage block matrix (6 explicit preimages, as columns). -/")
out.append("def Cm : Matrix (Fin 24) (Fin 6) ℚ := " + mlit(Cm))
Kb=T(ker)  # 24x18
assert mul(Lb,Kb)==zeros(6,18)
for a,f in enumerate(free):
    for b in range(18): assert Kb[f][b]==(1 if a==b else 0)
out.append("/-- explicit kernel basis of the leakage map (columns). -/")
out.append("def Kb : Matrix (Fin 24) (Fin 18) ℚ := " + mlit(Kb))
out.append("/-- free coordinates of the kernel basis. -/")
out.append("def freeIdx : Fin 18 → Fin 24 := ![" + ", ".join(map(str,free)) + "]")
# logical images
def opof(c):
    A=zeros(5,5)
    for ci,Ai in zip(c,ops):
        if ci: A=add(A,scal(ci,Ai))
    return A
li=[[r[1:4] for r in opof(c)[1:4]] for c in ker]
out.append("/-- logical images (middle 3×3 block) of the kernel basis vectors. -/")
out.append("def liT : Fin 18 → Matrix (Fin 3) (Fin 3) ℚ := ![\n  " + ",\n  ".join(mlit(A) for A in li) + "]")
fl=[[x for r in A for x in r] for A in li]
# choose independent subset greedily
sel=[]
for j in range(18):
    if rank([fl[s] for s in sel]+[fl[j]])>len(sel): sel.append(j)
assert len(sel)==4
# coefficients: fl[j] = sum_m R[j][m] fl[sel[m]]
Bsel=T([fl[s] for s in sel])  # 9x4
Rco=T(solve_cols(Bsel,T(fl)))  # 18x4
out.append("def selIdx : Fin 4 → Fin 18 := ![" + ", ".join(map(str,sel)) + "]")
out.append("/-- coordinates of each logical image in the basis `liT ∘ selIdx`. -/")
out.append("def Rco : Matrix (Fin 18) (Fin 4) ℚ := " + mlit(Rco))
# functional: choose 4 entry positions with invertible minor
import itertools
for P4 in itertools.combinations(range(9),4):
    Mn=[[fl[s][p] for s in sel] for p in P4]
    if rank(Mn)==4: break
Mi=inv(Mn)  # Mi * Mn = I : rows m, cols positions
W4=[[[F(0)]*3 for _ in range(3)] for m in range(4)]
for m in range(4):
    for a,p in enumerate(P4): W4[m][p//3][p%3]=Mi[m][a]
out.append("/-- dual functionals certifying independence of the 4 logical images. -/")
out.append("def W4 : Fin 4 → Matrix (Fin 3) (Fin 3) ℚ := ![" + ", ".join(mlit(A) for A in W4) + "]")
# interpretation B words
X01,X02=Ms[(0,1)],Ms[(0,2)]
words=[(None,None,eye(5))]; vecs=[[x for r in eye(5) for x in r]]
i=0
while len(words)<25:
    for gi,Gm in ((0,X01),(1,X02)):
        A=mul(Gm,words[i][2]); v=[x for r in A for x in r]
        if rank(vecs+[v])>len(vecs) and len(words)<25:
            words.append((gi,i,A)); vecs.append(v)
    i+=1
out.append("/-- 25 words in `X₀₁, X₀₂` (literal values); word `m > 0` is `X_g * word parent`. -/")
out.append("def wordT : Fin 25 → Matrix (Fin 5) (Fin 5) ℚ := ![\n  " + ",\n  ".join(mlit(w[2]) for w in words) + "]")
Wi=inv(T(vecs))  # Wi * (25x25 cols=words) = I
W25=[[[Wi[m][5*a+b] for b in range(5)] for a in range(5)] for m in range(25)]
out.append("/-- dual functionals certifying independence of the 25 words. -/")
out.append("def W25 : Fin 25 → Matrix (Fin 5) (Fin 5) ℚ := ![\n  " + ",\n  ".join(mlit(A) for A in W25) + "]")
open('data.lean','w').write("\n\n".join(out)+"\n")
# word membership haves
H=[]
for m,(gi,par,_) in enumerate(words):
    if m==0: continue
    H.append(f"  have h{m} : wordT {m} ∈ Algebra.adjoin ℚ (Set.range Xs) := by\n    rw [show wordT {m} = Xs {gi} * wordT {par} by decide +kernel]\n    exact Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨{gi}, rfl⟩) h{par}")
open('words.lean','w').write("\n".join(H)+"\n")
print("piv",piv,"free",free,"sel",sel,"P4",P4)
print("maxlen words", max(len(str(w)) for w in W25))
