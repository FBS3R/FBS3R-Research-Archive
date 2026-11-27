# Independent computation of M(8,n) = Tr A_n^8, A_n = adjacency of Fibonacci cube Gamma_n
import itertools
def M(k,n):
    V=[s for s in range(1<<n) if s & (s>>1)==0]
    idx={v:i for i,v in enumerate(V)}
    N=len(V); tot=0
    for v in V:
        vec={v:1}
        for _ in range(k):
            nv={}
            for u,c in vec.items():
                for j in range(n):
                    w=u^(1<<j)
                    if w & (w>>1)==0: nv[w]=nv.get(w,0)+c
            vec=nv
        tot+=vec.get(v,0)
    return tot
vals=[M(8,n) for n in range(11)]
print("M8:",vals)
print("M4:",[M(4,n) for n in range(5)]); print("M6:",[M(6,n) for n in range(8)])
P=[0,2,22,716,1146,8236,-206,13114,-8308,3152,-568]
# multiply series by (1-x-x^2)^5 and compare
D=[1]
for _ in range(5):
    D=[ (D[i] if i<len(D) else 0) - (D[i-1] if 0<=i-1<len(D) else 0) - (D[i-2] if 0<=i-2<len(D) else 0) for i in range(len(D)+2)]
vals2=[M(8,n) for n in range(16)]
prod=[sum(D[j]*vals2[i-j] for j in range(len(D)) if 0<=i-j) for i in range(16)]
print("prod:",prod)
print("match P4 (incl. zeros up to 15):", prod==P+[0]*5)
