"""Independent check of the PXP moment generating functions (Rational Spectral Hierarchies, 2026-10-23).
Builds the open-chain adjacency A_n on strings without '11' (flip j allowed iff neighbours are 0)
and compares Tr A_n^{2m} with the series of P_m(z)/(1-z-z^2)^{m+1}."""
import itertools
from sympy import symbols, series, Rational
import numpy as np
def tr(n,k):
    S=[s for s in itertools.product((0,1),repeat=n) if all(not(s[i] and s[i+1]) for i in range(n-1))]
    idx={s:i for i,s in enumerate(S)}; A=np.zeros((len(S),len(S)),dtype=object)
    for s in S:
        for j in range(n):
            if (j==0 or s[j-1]==0) and (j==n-1 or s[j+1]==0):
                t=list(s); t[j]^=1; A[idx[s],idx[tuple(t)]]=1
    M=np.identity(len(S),dtype=object)
    for _ in range(k): M=M.dot(A)
    return sum(M[i,i] for i in range(len(S)))
z=symbols('z'); D=1-z-z**2
P={4:(2*z+2*z**2+18*z**3-4*z**4,3),6:(2*z+8*z**2+130*z**3+40*z**4+350*z**5-156*z**6+36*z**7,4),
   8:(2*z+22*z**2+716*z**3+1146*z**4+8236*z**5-206*z**6+13114*z**7-8308*z**8+3152*z**9-568*z**10,5)}
N=11
for k,(p,e) in P.items():
    ser=series(p/D**e,z,0,N).removeO()
    pred=[ser.coeff(z,n) for n in range(N)]
    got=[tr(n,k) if n>0 else 0 for n in range(N)]
    print(k, 'OK' if pred==got else 'MISMATCH', got)
