"""Exact-integer certificate for range-r blockade moments (stdlib only).

For r = 1..4 and m = 1..M: S_m(z) = sum_n Tr A_{n,r}^{2m} z^n, D_r = 1 - z - z^{r+1}.
Checks (1) a_n = |C_{n,r}| obeys the recurrence; (2) S_m * D_r^{m+1} is a polynomial within the
computed window (all trailing coefficients vanish); (3) exact integer congruence P_{m,r} = (2m)! z^{(r+1)m-r} (mod D_r) by polynomial division over Z
(D_r has leading coefficient -1); (4) deg P_{m,r} = (2r+1)(m-1)+1 and top coefficient (-1)^(m-1) W(m,m,1)
with W = 2, 4, 36, 568, 14560 independent of r.  Evidence only (finite window), not a proof, for m >= 3.
"""
import sys
from math import factorial

def conf(n, r):
    return [s for s in range(1 << n) if all(not (s >> i & 1 and s >> j & 1)
            for i in range(n) for j in range(i + 1, min(n, i + r + 1)))]

def traces(n, r, K):
    st = conf(n, r); S = set(st)
    nb = {s: [s ^ (1 << j) for j in range(n) if (s ^ (1 << j)) in S] for s in st}
    res = [0] * (K + 1)
    for v in st:
        d = {v: 1}
        for h in range(1, K + 1):
            e = {}
            for s, c in d.items():
                for t in nb[s]:
                    e[t] = e.get(t, 0) + c
            d = e
            res[h] += sum(c * c for c in d.values())
    return len(st), res  # res[h] = Tr A^{2h}

def polmul(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i + j] += x * y
    return out

def polmod(p, d):
    """Remainder of p modulo d over Z; d must have leading coefficient +-1."""
    p = list(p); ld = d[-1]; assert ld in (1, -1)
    while len(p) >= len(d):
        c = p[-1] * ld  # since ld = +-1, c / ld = c * ld
        if c:
            sh = len(p) - len(d)
            for i, x in enumerate(d):
                p[sh + i] -= c * x
        p.pop()
    while p and p[-1] == 0:
        p.pop()
    return p

TOP = {1: 2, 2: 4, 3: 36, 4: 568, 5: 14560}

def main(N, M):
    ok = True
    for r in range(1, 5):
        data = [traces(n, r, M) for n in range(N + 1)]
        a = [d[0] for d in data]
        rec = all(a[n] == (n + 1 if n <= r else a[n - 1] + a[n - r - 1]) for n in range(N + 1))
        Dr = [1, -1] + [0] * (r - 1) + [-1]
        print(f"r={r}: recurrence {'OK' if rec else 'FAIL'}, a = {a[:10]}")
        ok &= rec
        for m in range(1, M + 1):
            S = [data[n][1][m] for n in range(N + 1)]
            D = [1]
            for _ in range(m + 1):
                D = polmul(D, Dr)
            P = polmul(S, D)[:N + 1]
            deg = max(i for i, x in enumerate(P) if x)
            tail = N - deg
            e = (r + 1) * m - r
            mono = [0] * e + [factorial(2 * m)]
            res_ok = polmod(P[:deg + 1], Dr) == polmod(mono, Dr)
            deg_ok = deg == (2 * r + 1) * (m - 1) + 1
            top_ok = P[deg] == (-1) ** (m - 1) * TOP[m] if m in TOP else True
            poly_ok = tail >= 3
            ok &= res_ok and poly_ok and deg_ok and top_ok
            print(f"  m={m}: deg P = {deg} (zero tail {tail}), deg formula {'OK' if deg_ok else 'FAIL'}, "
                  f"top {P[deg]} {'OK' if top_ok else 'FAIL'}, exact residue (2m)! z^{e} mod D_r {'OK' if res_ok else 'FAIL'}")
    print("ALL OK" if ok else "SOME CHECK FAILED")
    return 0 if ok else 1

if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 22
    M = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    sys.exit(main(N, M))
