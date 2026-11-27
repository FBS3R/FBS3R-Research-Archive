#!/usr/bin/env python3
"""
Exact-arithmetic certificate for the spin-2 square-plaquette ("AKLT plaquette") claims.

Only the Python standard library is used (fractions.Fraction); every rank, kernel and
equality below is exact.  Run:  python3 aklt_cert.py   (exit code 0 iff all asserted
facts hold; the claim table is printed at the end).

Conventions (as in the task statement)
  one site:  e_k = u^(4-k) v^k, k = 0..4
             Sz e_k = (2-k) e_k,  S+ e_k = k e_(k-1),  S- e_k = (4-k) e_(k+1)
             Gram metric G = diag(1/binom(4,k))
  matrices:  column j = image of e_j   (A[i][j] = coefficient of e_i in A e_j)
  pair:      X_ij = Sz_i Sz_j + (S+_i S-_j + S-_i S+_j)/2
             P_ij = X(X+3)(X+5)(X+6)/2520
  square:    sites 0,1,2,3, edges 01,02,13,23 (diagonals 03,12)
             H_square = P01 + P02 + P13 + P23

Interpretation choices made for the ill-specified claims are printed explicitly.
"""
from fractions import Fraction as F
from itertools import product
from math import comb
import sys

FAILS = []


def check(cond, msg):
    print(("  [ok]   " if cond else "  [FAIL] ") + msg)
    if not cond:
        FAILS.append(msg)


# ---------------------------------------------------------------- linear algebra
def zeros(n, m):
    return [[F(0)] * m for _ in range(n)]


def eye(n):
    A = zeros(n, n)
    for i in range(n):
        A[i][i] = F(1)
    return A


def mul(A, B):
    n, k, m = len(A), len(B), len(B[0])
    C = zeros(n, m)
    for i in range(n):
        Ai = A[i]
        Ci = C[i]
        for t in range(k):
            a = Ai[t]
            if a:
                Bt = B[t]
                for j in range(m):
                    if Bt[j]:
                        Ci[j] += a * Bt[j]
    return C


def add(A, B, s=1):
    return [[a + s * b for a, b in zip(r, q)] for r, q in zip(A, B)]


def scal(c, A):
    return [[c * a for a in r] for r in A]


def T(A):
    return [list(r) for r in zip(*A)]


def comm(A, B):
    return add(mul(A, B), mul(B, A), -1)


def rref(A):
    A = [list(r) for r in A]
    n = len(A)
    m = len(A[0]) if n else 0
    piv = []
    r = 0
    for c in range(m):
        p = next((i for i in range(r, n) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        inv = 1 / A[r][c]
        A[r] = [x * inv for x in A[r]]
        for i in range(n):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(c)
        r += 1
        if r == n:
            break
    return A[:r], piv


def rank(A):
    if not A or not A[0]:
        return 0
    return len(rref(A)[1])


def nullspace(A, m=None):
    """basis (list of vectors) of {x : A x = 0}"""
    if not A:
        return [[F(int(i == j)) for i in range(m)] for j in range(m)]
    m = len(A[0])
    R, piv = rref(A)
    free = [c for c in range(m) if c not in piv]
    basis = []
    for f in free:
        x = [F(0)] * m
        x[f] = F(1)
        for row, p in zip(R, piv):
            x[p] = -row[f]
        basis.append(x)
    return basis


def inv(A):
    n = len(A)
    R, piv = rref([r + e for r, e in zip(A, eye(n))])
    assert piv == list(range(n)), "singular"
    return [r[n:] for r in R]


def solve_cols(B, Y):
    """B: n x r with independent columns; Y: n x s, each column in span B. Return C (r x s), B C = Y."""
    n, r = len(B), len(B[0])
    s = len(Y[0])
    M = [B[i] + Y[i] for i in range(n)]
    R, piv = rref(M)
    assert piv[:r] == list(range(r)) and all(p < r for p in piv), "not in span"
    return [R[i][r:] for i in range(r)]


def in_span(B, y):
    return rank([B[i] + [y[i]] for i in range(len(B))]) == rank(B)


def integerize(v):
    from math import gcd
    den = 1
    for x in v:
        den = den * x.denominator // gcd(den, x.denominator)
    w = [int(x * den) for x in v]
    g = 0
    for x in w:
        g = gcd(g, abs(x))
    w = [x // g for x in w]
    # make first nonzero positive
    for x in w:
        if x:
            if x < 0:
                w = [-y for y in w]
            break
    return w


def mpow(A, k):
    R = eye(len(A))
    for _ in range(k):
        R = mul(R, A)
    return R


# ---------------------------------------------------------------- one site
N = 5
Sz = zeros(N, N)
Sp = zeros(N, N)
Sm = zeros(N, N)
for k in range(N):
    Sz[k][k] = F(2 - k)
    if k >= 1:
        Sp[k - 1][k] = F(k)
    if k <= 3:
        Sm[k + 1][k] = F(4 - k)
G = zeros(N, N)
for k in range(N):
    G[k][k] = F(1, comb(4, k))
Ginv = inv(G)


def adjG(A, Gm=G, Gmi=Ginv):
    # <A x, y>_G = <x, adj(A) y>_G ;  adj(A) = G^-1 A^T G
    return mul(Gmi, mul(T(A), Gm))


print("== Step 0: one-site operators (5x5) ==")
check(adjG(Sz) == Sz, "Sz is G-self-adjoint")
check(adjG(Sp) == Sm, "S+^dagger_G = S-  (hence Sx, Sy are G-self-adjoint)")
check(comm(Sp, Sm) == scal(2, Sz), "[S+, S-] = 2 Sz")
check(comm(Sz, Sp) == Sp and comm(Sz, Sm) == scal(-1, Sm), "[Sz, S+-] = +-S+-")
Cas = add(mul(Sz, Sz), scal(F(1, 2), add(mul(Sp, Sm), mul(Sm, Sp))))
check(Cas == scal(6, eye(N)), "Casimir Sz^2 + (S+S- + S-S+)/2 = 6 I = s(s+1) I, s=2")
# G is the restriction of the SU(2)-invariant inner product: check identity e_k = u^(4-k)v^k norms
# (not needed further)

# ---------------------------------------------------------------- pair (25-dim)
print("== Step 0b: pair operators (25x25) ==")


def kron(A, B):
    n, m = len(A), len(B)
    C = zeros(n * m, n * m)
    for i in range(n):
        for j in range(n):
            if A[i][j]:
                for k in range(m):
                    for l in range(m):
                        if B[k][l]:
                            C[i * m + k][j * m + l] = A[i][j] * B[k][l]
    return C


Xp = add(kron(Sz, Sz), scal(F(1, 2), add(kron(Sp, Sm), kron(Sm, Sp))))
I25 = eye(25)
G2 = kron(G, G)
G2i = inv(G2)
check(adjG(Xp, G2, G2i) == Xp, "X = S1.S2 is G(x)G-self-adjoint")
minpoly = I25
for r in (0, 3, 5, 6, -4):
    minpoly = mul(minpoly, add(Xp, scal(r, I25)))
check(minpoly == zeros(25, 25), "X(X+3)(X+5)(X+6)(X-4) = 0 on the pair")
evs = {}
for r in (0, 3, 5, 6, -4):
    evs[-r] = 25 - rank(add(Xp, scal(r, I25)))
check(evs == {-6: 1, -5: 3, -3: 5, 0: 7, 4: 9},
      "eigenvalue multiplicities of X: -6:1, -5:3, -3:5, 0:7, 4:9  (J=0..4, (J(J+1)-12)/2)")
Pp = scal(F(1, 2520), mul(mul(Xp, add(Xp, scal(3, I25))), mul(add(Xp, scal(5, I25)), add(Xp, scal(6, I25)))))
check(mul(Pp, Pp) == Pp and rank(Pp) == 9 and adjG(Pp, G2, G2i) == Pp,
      "P = X(X+3)(X+5)(X+6)/2520 is a G-orthogonal projector of rank 9 (spin-4 multiplet)")

# ---------------------------------------------------------------- 4 sites, sparse
print("== Step 1: four sites (625) / Jz sectors ==")
SITES = 4
PAIRS = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
EDGES = [(0, 1), (0, 2), (1, 3), (2, 3)]
check(5 ** 4 == 625, "full dimension 625")


def sector(M):
    # Jz = sum(2-k) = M  <=>  sum k = 8 - M
    return [t for t in product(range(5), repeat=4) if sum(t) == 8 - M]


sizes = {M: len(sector(M)) for M in range(-8, 9)}
check(sum(sizes.values()) == 625, "Jz sectors partition the 625-dim space")
check(sizes[0] == 85, "dim Jz=0 sector = 85")
check(sizes[0] - sizes[1] == 5, "multiplicity of total spin 0 = dim(Jz=0) - dim(Jz=1) = 5")


def apply_Sp(v, i):
    w = {}
    for t, c in v.items():
        k = t[i]
        if k >= 1:
            s = t[:i] + (k - 1,) + t[i + 1:]
            w[s] = w.get(s, 0) + c * k
    return {s: c for s, c in w.items() if c}


def apply_Sm(v, i):
    w = {}
    for t, c in v.items():
        k = t[i]
        if k <= 3:
            s = t[:i] + (k + 1,) + t[i + 1:]
            w[s] = w.get(s, 0) + c * (4 - k)
    return {s: c for s, c in w.items() if c}


def apply_Sz(v, i):
    return {t: c * (2 - t[i]) for t, c in v.items() if 2 - t[i]}


def vadd(*vs):
    w = {}
    for (s, v) in vs:
        for t, c in v.items():
            w[t] = w.get(t, 0) + s * c
    return {t: c for t, c in w.items() if c}


def apply_X(v, i, j):
    return vadd((1, apply_Sz(apply_Sz(v, j), i)),
                (F(1, 2), apply_Sp(apply_Sm(v, j), i)),
                (F(1, 2), apply_Sm(apply_Sp(v, j), i)))


def op_matrix(f, basis_in, basis_out):
    idx = {t: n for n, t in enumerate(basis_out)}
    A = zeros(len(basis_out), len(basis_in))
    for c, t in enumerate(basis_in):
        for s, x in f({t: F(1)}).items():
            A[idx[s]][c] += x
    return A


B0 = sector(0)
Xs = {p: op_matrix(lambda v, p=p: apply_X(v, *p), B0, B0) for p in PAIRS}
I85 = eye(85)


def projP(X, I):
    return scal(F(1, 2520), mul(mul(X, add(X, scal(3, I))), mul(add(X, scal(5, I)), add(X, scal(6, I)))))


H85 = zeros(85, 85)
for e in EDGES:
    H85 = add(H85, projP(Xs[e], I85))

# total S+ : Jz=0 -> Jz=1
B1 = sector(1)
SpTot = op_matrix(lambda v: vadd(*[(1, apply_Sp(v, i)) for i in range(4)]), B0, B1)
sing = nullspace(SpTot)
check(len(sing) == 5, "singlet space (ker S+_tot on Jz=0) has dimension 5")
sing = [[F(x) for x in integerize(v)] for v in sing]
Vs = T(sing)  # 85 x 5, columns = singlet basis

# restrictions of X_ij to the singlet sector
Ms = {p: solve_cols(Vs, mul(Xs[p], Vs)) for p in PAIRS}
I5 = eye(5)
check(Ms[(0, 1)] == Ms[(2, 3)] and Ms[(0, 2)] == Ms[(1, 3)] and Ms[(0, 3)] == Ms[(1, 2)],
      "on singlets X01 = X23, X02 = X13, X03 = X12")
check(add(add(Ms[(0, 1)], Ms[(0, 2)]), Ms[(0, 3)]) == scal(-6, I5),
      "on singlets X01 + X02 + X03 = -6")
check(comm(Ms[(0, 1)], Ms[(0, 2)]) != zeros(5, 5), "X01 and X02 do not commute on singlets")
# Gram matrix of singlet basis (w.r.t. G^{(x)4})
def g4(t):
    r = F(1)
    for k in t:
        r /= comb(4, k)
    return r


Gs = [[sum(Vs[n][a] * Vs[n][b] * g4(B0[n]) for n in range(85)) for b in range(5)] for a in range(5)]
Gsi = inv(Gs)
check(all(adjG(Ms[p], Gs, Gsi) == Ms[p] for p in PAIRS), "restricted X_ij are self-adjoint for the induced Gram")

# H_square kernel, full space: sum over Jz sectors
kerdims = {}
for M in range(0, 9):
    BM = sector(M)
    IM = eye(len(BM))
    HM = zeros(len(BM), len(BM))
    for e in EDGES:
        XM = op_matrix(lambda v, e=e: apply_X(v, *e), BM, BM)
        HM = add(HM, projP(XM, IM))
    kerdims[M] = len(BM) - rank(HM)
full_ker = kerdims[0] + 2 * sum(kerdims[M] for M in range(1, 9))
hw = {J: kerdims[J] - (kerdims[J + 1] if J < 8 else 0) for J in range(9)}
print("  info: dim ker H_square in Jz=M sectors:", kerdims)
print("  info: dim ker H_square (full 625-dim space) =", full_ker,
      "; spin-J multiplicities in the kernel:", hw)

Hs = solve_cols(Vs, mul(H85, Vs))
check(Hs == scal(2, add(projP(Ms[(0, 1)], I5), projP(Ms[(0, 2)], I5))),
      "on singlets H_square = 2 (P(X01) + P(X02))")
check(rank(projP(Ms[(0, 1)], I5)) == 1 and rank(projP(Ms[(0, 2)], I5)) == 1,
      "P(X01), P(X02) each have rank 1 on singlets")
code = nullspace(Hs)
check(len(code) == 3, "ker(H_square restricted to J=0) has dimension 3")
check(hw[0] == 3, "consistency: the full kernel contains exactly 3 singlets")
# PSD: H_square is a sum of G-orthogonal projectors, so ker = ground space (energy 0),
# both inside the singlet sector and in the full space.
check(all(adjG(projP(Ms[p], I5), Gs, Gsi) == projP(Ms[p], I5) and
          mul(projP(Ms[p], I5), projP(Ms[p], I5)) == projP(Ms[p], I5) for p in EDGES),
      "each P_ij is an orthogonal projector on singlets => H_square >= 0, ground space = kernel")
code = [[F(x) for x in integerize(v)] for v in code]
Cc = T(code)  # 5 x 3

# orthogonal code projector P (w.r.t. Gs), Q = 1-P
Pc = mul(Cc, mul(inv(mul(T(Cc), mul(Gs, Cc))), mul(T(Cc), Gs)))
Qc = add(I5, Pc, -1)
check(mul(Pc, Pc) == Pc and rank(Pc) == 3 and adjG(Pc, Gs, Gsi) == Pc, "P is a Gs-orthogonal rank-3 projector")


def flat(A):
    return [x for r in A for x in r]


def leak(A):
    return flat(mul(Qc, mul(A, Pc)))


def preserves(A):
    return mul(Qc, mul(A, Pc)) == zeros(5, 5)


def logical(A):
    """matrix of A restricted to the code (code coordinates), requires A(code) in code"""
    return solve_cols(Cc, mul(A, Cc))


print("== Step 2: H2, H3 ==")
X01, X02, X03 = Ms[(0, 1)], Ms[(0, 2)], Ms[(0, 3)]
H2 = add(add(add(mpow(X03, 2), mpow(X01, 2), -1), mpow(X02, 2), -1), scal(-16, add(X01, X02)))
H3 = mpow(X03, 3)
for X in (X01, X02):
    H3 = add(H3, add(add(mpow(X, 3), scal(19, mpow(X, 2))), scal(152, X)))
check(preserves(H2), "Q H2 P = 0")
check(preserves(H3), "Q H3 P = 0")
L2, L3 = logical(H2), logical(H3)
check(rank([flat(eye(3)), flat(L2), flat(L3)]) == 3,
      "logical images of 1, H2, H3 are linearly independent")
print("  info: logical H2 and H3 commute?", comm(L2, L3) == zeros(3, 3))
print("  info: logical H2 =", [[str(x) for x in r] for r in L2])
print("  info: logical H3 =", [[str(x) for x in r] for r in L3])
# (the same check on the 85-dim Jz=0 sector, i.e. the full ground space restricted to Jz=0
# would be a different, stronger statement; we test it as information)
def kernel85_preserved(H):
    K = nullspace(H85)
    KK = T(K)
    return all(in_span(KK, [r[0] for r in mul(H, [[x] for x in k])]) for k in K)


H2f = add(add(add(mpow(Xs[(0, 3)], 2), mpow(Xs[(0, 1)], 2), -1), mpow(Xs[(0, 2)], 2), -1),
          scal(-16, add(Xs[(0, 1)], Xs[(0, 2)])))
print("  info: does H2 (as written, full-space operator) preserve ker H_square in the Jz=0 sector?",
      kernel85_preserved(H2f))

print("== Step 3: leakage map / logical images (interpretation A: formal span of X_ij^k) ==")
# Interpretation A: domain = formal coefficient vectors c_{(ij),k} for the 6 pairs and
# powers k = 1..d (d = 4 gives 24 = 6*4 coordinates);  L(c) = Q (sum c X_ij^k) P  on singlets.


def leakage_data(pairs, dmax, with_identity=False):
    ops = []
    if with_identity:
        ops.append(I5)
    for p in pairs:
        for k in range(1, dmax + 1):
            ops.append(mpow(Ms[p], k))
    Lmat = T([leak(A) for A in ops])  # 25 x n
    rk = rank(Lmat)
    ker = nullspace(Lmat)
    imgs = []
    for c in ker:
        A = zeros(5, 5)
        for ci, Ai in zip(c, ops):
            if ci:
                A = add(A, scal(ci, Ai))
        imgs.append(flat(logical(A)))
    ldim = rank(imgs) if imgs else 0
    scalar = all(in_span(T([flat(eye(3))]), v) for v in imgs)
    return len(ops), rk, len(ker), ldim, scalar, imgs


n, rk, kd, ld, sc, _ = leakage_data(PAIRS, 4)
print(f"  all 6 pairs, k=1..4: domain {n}, rank L = {rk}, dim ker L = {kd}, dim logical image = {ld}")
RES = {"leak_rank": rk, "leak_ker": kd, "full_logical": ld}
deg = {}
for d in (1, 2, 3, 4, 5, 6):
    n_, rk_, kd_, ld_, sc_, _ = leakage_data(PAIRS, d)
    n2, rk2, kd2, ld2, sc2, _ = leakage_data(PAIRS, d, True)
    deg[d] = ld_
    print(f"  degree <= {d}: domain {n_}, rank {rk_}, ker {kd_}, logical dim {ld_}"
          f"   (with explicit identity: {ld2})")
RES["deg"] = deg
ne, rke, kde, lde, sce, imgse = leakage_data(EDGES, 4)
print(f"  edges only, k=1..4: domain {ne}, rank {rke}, ker {kde}, logical dim {lde}, scalar: {sce}")
ne6, rke6, kde6, lde6, sce6, _ = leakage_data(EDGES, 8, True)
print(f"  edges only, k=0..8 (all polynomials in edge operators, no products): logical dim {lde6}, scalar: {sce6}")
RES["edge_scalar"] = sce
RES["edge_scalar_all"] = sce6

print("== Step 3b: interpretation B: associative algebra / Lie algebra generated ==")


def span_closure(gens, prod):
    basis = []
    vecs = []

    def addv(A):
        v = flat(A)
        if rank(vecs + [v]) > len(vecs):
            vecs.append(v)
            basis.append(A)
            return True
        return False

    for A in gens:
        addv(A)
    changed = True
    while changed:
        changed = False
        cur = list(basis)
        for A in cur:
            for B in cur:
                if addv(prod(A, B)):
                    changed = True
    return basis


alg = span_closure([I5, X01, X02], mul)
print(f"  associative algebra generated by the X_ij on singlets: dim {len(alg)}  (25 = all of M_5)")
lie = span_closure([X01, X02, X03], comm)
lie_tr = [A for A in lie]
print(f"  real Lie algebra generated by i*X01, i*X02, i*X03 on singlets: dim {len(lie)}")
# leakage restricted to the Lie algebra / to sl_5
Lmat = T([leak(A) for A in lie])
print(f"  leakage on that Lie algebra: rank {rank(Lmat)}, ker {len(lie) - rank(Lmat)}")
RES["alg_dim"] = len(alg)
RES["lie_dim"] = len(lie)
RES["lie_leak"] = (rank(Lmat), len(lie) - rank(Lmat))
Lalg = T([leak(A) for A in alg])
print(f"  leakage on the associative algebra (M_5): rank {rank(Lalg)}, ker {len(alg) - rank(Lalg)}")
kerA = nullspace(Lalg)
imgsA = []
for c in kerA:
    A = zeros(5, 5)
    for ci, Ai in zip(c, alg):
        A = add(A, scal(ci, Ai))
    imgsA.append(flat(logical(A)))
print(f"  logical image of the code-preserving part of M_5: dim {rank(imgsA)} (= gl(3))")

print("== Step 4: logical Lie algebra ==")
# logical images (interpretation A, all pairs, degree 4)
_, _, _, _, _, imgs = leakage_data(PAIRS, 4)
R, _ = rref(imgs)
Lbasis = [[r[3 * i:3 * i + 3] for i in range(3)] for r in R]
print(f"  logical image (interp. A) basis size {len(Lbasis)}")
Gc = mul(T(Cc), mul(Gs, Cc))
Gci = inv(Gc)
check(all(adjG(A, Gc, Gci) == A for A in Lbasis), "logical images are self-adjoint on the code (induced Gram)")
# Lie algebra generated by i*A: [iA,iB] = -[A,B]; i*[skew] ... Work with the real Lie algebra
# spanned by i*Herm and Skew parts: represent element as (H, K) meaning i*H + K, H self-adj, K skew-adj.
# Generated algebra: closure of {i A} under brackets. [iA, iB] = -[A,B] (skew-adjoint, real);
# [iA, K] = i[A,K] (i * self-adjoint); [K1, K2] skew-adjoint.  Since all matrices are real,
# the real Lie algebra is spanned by i*(real self-adjoint set Hset) + (real skew set Kset).
Hset = list(Lbasis)
Kset = []


def grow():
    changed = False
    allH, allK = list(Hset), list(Kset)
    cand_K = [scal(-1, comm(A, B)) for A in allH for B in allH] + [comm(A, B) for A in allK for B in allK]
    cand_H = [comm(A, B) for A in allH for B in allK]
    for A in cand_K:
        if rank([flat(x) for x in Kset] + [flat(A)]) > len(Kset):
            Kset.append(A)
            changed = True
    for A in cand_H:
        if rank([flat(x) for x in Hset] + [flat(A)]) > len(Hset):
            Hset.append(A)
            changed = True
    return changed


while grow():
    pass
liedim = len(Hset) + len(Kset)
print(f"  logical Lie algebra: dim {liedim} (i*selfadjoint part {len(Hset)}, skew part {len(Kset)})")
# center dimension and derived algebra dimension
elems = [("H", A) for A in Hset] + [("K", A) for A in Kset]


def to_vec(kind, A):
    z = [F(0)] * 9
    return (flat(A) + z) if kind == "H" else (z + flat(A))


def br(e1, e2):
    (k1, A), (k2, B) = e1, e2
    C = comm(A, B)
    if k1 == "H" and k2 == "H":
        return ("K", scal(-1, C))
    if k1 == "K" and k2 == "K":
        return ("K", C)
    return ("H", C)


derived = [to_vec(*br(a, b)) for a in elems for b in elems]
dder = rank(derived)
# center: solve sum x_a [e_a, e_b] = 0 for all b
rows = []
for b in elems:
    cols = [to_vec(*br(a, b)) for a in elems]
    rows += T(cols)
cen = len(nullspace(rows))
print(f"  derived algebra dim {dder}, center dim {cen}")
RES["lie_logical"] = (liedim, dder, cen)
# Decomposition of the code: commutant of the logical algebra
print("  info: u(2)+u(1) acting on C^3 = C^2 + C would have dim 5, derived dim 3, center dim 2")

print()
print("=================== CLAIM TABLE ===================")
table = [
    ("singlet sector dim 5, Jz=0 dim 85, full 625", True),
    ("singlet code space dim 3 (ker H|J=0 = ground space within singlets)", len(code) == 3),
    ("leakage map rank 6 (interp. A: 24 formal X_ij^k, k=1..4)", RES["leak_rank"] == 6),
    ("leakage map kernel 18 (interp. A)", RES["leak_ker"] == 18),
    ("full logical image dim 4 (interp. A)", RES["full_logical"] == 4),
    ("edge operators only => logical image scalar (interp. A, k=1..4)", RES["edge_scalar"]),
    ("degrees 1,2,3,4 => logical dims 1,2,3,4 (interp. A)", [RES["deg"][d] for d in (1, 2, 3, 4)] == [1, 2, 3, 4]),
    ("Q H2 P = 0", preserves(H2)),
    ("Q H3 P = 0", preserves(H3)),
    ("logical Lie algebra = u(2)+u(1) (dim 5, derived 3, center 2)", RES["lie_logical"] == (5, 3, 2)),
]
for name, val in table:
    print(f"  {'TRUE ' if val else 'FALSE'}  {name}")
print("  RES =", RES)

# ---------------------------------------------------------------- export for Lean
if "--lean-data" in sys.argv:
    out = sys.argv[sys.argv.index("--lean-data") + 1]

    def ilit(A):
        return "!![" + "; ".join(", ".join(str(int(x)) for x in r) for r in A) + "]"

    L = []
    for n_, v in enumerate(sing):
        d = {B0[n]: int(v[n]) for n in range(85)}
        def nest(pre):
            if len(pre) == 4:
                return str(d.get(tuple(pre), 0))
            return "![" + ", ".join(nest(pre + [k]) for k in range(5)) + "]"
        L.append(f"/-- singlet basis vector number {n_} (coordinates in the product basis). -/\n"
                 f"def sv{n_} : V := {nest([])}\n")
    names = {(0, 1): "N01", (0, 2): "N02", (0, 3): "N03", (1, 2): "N12", (1, 3): "N13", (2, 3): "N23"}
    for p in PAIRS:
        A = scal(2, Ms[p])
        assert all(x.denominator == 1 for r in A for x in r)
        L.append(f"/-- `2 X_{p[0]}{p[1]}` restricted to the singlet span, in the basis `sv0..sv4`. -/\n"
                 f"def {names[p]} : Matrix (Fin 5) (Fin 5) ℤ := {ilit(A)}\n")
    for nm, A in (("Hmat_val", scal(40320, Hs)), ("H2m_val", scal(4, H2)), ("H3m_val", scal(8, H3))):
        assert all(x.denominator == 1 for r in A for x in r)
        L.append(f"-- {nm} = {ilit(A)}\n")
    open(out, "w").write("\n".join(L))
    print("wrote", out)

if "--lean" in sys.argv:
    def lit(A):
        return "!![" + "; ".join(", ".join(str(x) if x.denominator == 1 else f"({x.numerator}/{x.denominator})"
                                           for x in r) for r in A) + "]"
    print("SINGLET_BASIS (integer vectors on Jz=0 basis tuples):")
    for v in sing:
        print({B0[n]: int(v[n]) for n in range(85) if v[n]})
    for p in PAIRS:
        print("M", p, lit(Ms[p]))
    print("Gs", lit(Gs))
    print("code", [[int(x) for x in c] for c in code])
    print("H2", lit(H2))
    print("H3", lit(H3))
    print("Hs", lit(Hs))

sys.exit(1 if FAILS else 0)
