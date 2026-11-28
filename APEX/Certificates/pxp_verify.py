#!/usr/bin/env python3
"""Independent exact-integer check of the APEX PXP rational-hierarchy statements.

Checks, for m = 1..MMAX, with M_{m,n} = Tr A_n^{2m} computed by sparse propagation on the
Fibonacci cube (no transfer matrix, no generating function assumed):
  (1) (sum_n M_{m,n} z^n) (1-z-z^2)^{m+1} is a polynomial P_m of degree exactly 3m-2
      on the computed window n <= NMAX  (the Lean theorem proves deg <= 3m-2 for all n);
  (2) P_m == (2m)! z^(2m-1)  (mod 1-z-z^2)  in Z[z]  (=> pole order exactly m+1);
  (3) for m = 2,3,4, P_m equals the numerator printed in the 2026-10-23 preprint.
Standard library only; all comparisons are integer equalities.
Usage: python3 -I pxp_verify.py [NMAX] [MMAX]
"""
import itertools, math, sys

def configs(n):
    return [s for s in itertools.product((0, 1), repeat=n)
            if all(not (s[i] and s[i + 1]) for i in range(n - 1))]

def traces(n, K):
    C = configs(n); idx = {s: i for i, s in enumerate(C)}
    nb = [[idx[t] for j in range(n) for t in [s[:j] + (1 - s[j],) + s[j + 1:]] if t in idx] for s in C]
    tr = [0] * (K + 1)
    for i in range(len(C)):
        v = {i: 1}
        for k in range(1, K + 1):
            w = {}
            for a, c in v.items():
                for b in nb[a]:
                    w[b] = w.get(b, 0) + c
            v = w
            tr[k] += v.get(i, 0)
    return tr

def mul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r

def mod_D(p):  # reduce modulo z^2 = 1 - z
    p = list(p) + [0, 0]
    for i in range(len(p) - 1, 1, -1):
        c = p[i]; p[i] = 0; p[i - 2] += c; p[i - 1] -= c
    return p[:2]

PAPER = {2: [0, 2, 2, 18, -4], 3: [0, 2, 8, 130, 40, 350, -156, 36],
         4: [0, 2, 22, 716, 1146, 8236, -206, 13114, -8308, 3152, -568]}

def main():
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 15
    MMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    T = [[0] * (2 * MMAX + 1)] + [traces(n, 2 * MMAX) for n in range(1, NMAX + 1)]
    ok = True
    for m in range(1, MMAX + 1):
        M = [T[n][2 * m] for n in range(NMAX + 1)]
        Dm = [1]
        for _ in range(m + 1):
            Dm = mul(Dm, [1, -1, -1])
        P = mul(M, Dm)[:NMAX + 1]
        deg = max(i for i, c in enumerate(P) if c)
        c1 = deg == 3 * m - 2 and all(c == 0 for c in P[deg + 1:]) and NMAX > 3 * m + 2
        c2 = mod_D(P[:deg + 1]) == mod_D([0] * (2 * m - 1) + [math.factorial(2 * m)])
        c3 = (m not in PAPER) or P[:deg + 1] == PAPER[m]
        print(f"m={m}: P_m={P[:deg+1]} deg={deg} [deg=3m-2:{c1}] [mod D:{c2}] [paper:{c3}]")
        ok &= c1 and c2 and c3
    print("ALL CHECKS PASSED" if ok else "FAILURE")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
