# 6-lens.sage — LENS: the IPA fold IS an FRI fold; one transcript certifies both.
#   (solutions/4-lens.md; Lean core: SuccinctIPA/Lens.lean)
#
# Between Genesis (2) and Prism (3): small proof AND small verifier.
#
#   * Setup (transparent, one-time): RS-encode the generator vector as a group
#     codeword (coefficients = G, bit-reversed so round-1's IPA split is the
#     first folded variable), Merkle-commit.  Verifier key = seed + one root.
#   * Prove: ordinary Bulletproofs IPA rounds; at round j the prover folds the
#     codeword by x_j^2 (the round identity, proven in Lean as lens_fold_factor:
#       x^-1*G_lo + x*G_hi = x^-1 * (G_lo + x^2 * G_hi)
#     — the IPA generator fold IS an FRI fold by x^2, times a public scalar)
#     and commits the folded layer's Merkle root BEFORE the next challenge is
#     drawn.  So every FRI fold challenge is fresh randomness (commit-then-
#     challenge), even though it doubles as the IPA challenge — this closes the
#     ordering gap flagged in 5-prism.sage's decide.
#   * After k rounds the codeword has collapsed to a constant W and
#       G0 = (prod_j x_j^-1) * W                (Lean: lens_foldAll_eq_genFinal)
#   * Verify: usual O(log n) IPA checks + ell FRI query walks (2 Merkle opens +
#     3 smuls per level) + one rescale.  No circuit, no separate decide phase.
#
# Run:  sage sage/6-lens.sage
import hashlib, time

# ---------------------------------------------------------------- Pallas
p = 28948022309329048855892746252171976963363056481941560715954676764349967630337
q = 28948022309329048855892746252171976963363056481941647379679742748393362948097
E = EllipticCurve(GF(p), [0, 5])
Fq = GF(q)
INF = E(0)

class Transcript:
    def __init__(self, label):
        self.h = hashlib.sha256(label.encode()).digest()
    def absorb(self, label, obj):
        self.h = hashlib.sha256(self.h + label.encode() + b"|" +
                                repr(obj).encode()).digest()
    def absorb_point(self, label, P):
        self.absorb(label, "INF" if P == INF else (int(P[0]), int(P[1])))
    def challenge(self, label):
        while True:
            self.h = hashlib.sha256(self.h + label.encode()).digest()
            x = Fq(int.from_bytes(self.h, "big"))
            if x != 0:
                return x
    def challenge_idx(self, label, bound):
        self.h = hashlib.sha256(self.h + label.encode()).digest()
        return int.from_bytes(self.h, "big") % bound

class Cost:
    def __init__(self):
        self.smul = 0; self.hash = 0

def msm(scalars, points, cost=None):
    acc = INF
    for a, P in zip(scalars, points):
        acc += int(a) * P
        if cost is not None:
            cost.smul += 1
    return acc

def inner(a, b):
    return sum((a[i] * b[i] for i in range(len(a))), Fq(0))

def hash_to_curve(seed, i):
    ctr = 0
    while True:
        d = hashlib.sha256(seed + b"gen" + repr((i, ctr)).encode()).digest()
        x = GF(p)(int.from_bytes(d, "big"))
        rhs = x**3 + 5
        if rhs.is_square():
            P = E(x, rhs.sqrt())
            if P != INF:
                return P
        ctr += 1

def root_of_unity(m):
    g = Fq.multiplicative_generator()
    return g ** ((q - 1) // m)

def gfft(a, w):
    m = len(a)
    if m == 1:
        return a[:]
    ev = gfft(a[0::2], w * w)
    od = gfft(a[1::2], w * w)
    res = [INF] * m
    wk = Fq(1)
    for i in range(m // 2):
        t = int(wk) * od[i]
        res[i] = ev[i] + t
        res[i + m // 2] = ev[i] - t
        wk *= w
    return res

def leaf_hash(P):
    tag = (b"INF" if P == INF
           else int(P[0]).to_bytes(32, "big") + int(P[1]).to_bytes(32, "big"))
    return hashlib.sha256(b"leaf" + tag).digest()

def merkle_tree(points):
    level = [leaf_hash(P) for P in points]
    levels = [level]
    while len(level) > 1:
        level = [hashlib.sha256(level[i] + level[i + 1]).digest()
                 for i in range(0, len(level), 2)]
        levels.append(level)
    return levels

def merkle_path(levels, idx):
    path = []
    for lvl in levels[:-1]:
        path.append(lvl[idx ^^ 1])
        idx >>= 1
    return path

def merkle_check(root, idx, P, path, cost):
    h = leaf_hash(P); cost.hash += 1
    for sib in path:
        h = hashlib.sha256((h + sib) if (idx & 1) == 0 else (sib + h)).digest()
        cost.hash += 1
        idx >>= 1
    return h == root

def fri_fold(c, r, omega):
    """fold the codeword of f(X)=f_e(X^2)+X f_o(X^2) to f_e + r*f_o (eval form)."""
    m = len(c); half = m // 2
    inv2 = Fq(2)**-1
    out = [INF] * half
    xt = Fq(1)
    for t in range(half):
        a, bb = c[t], c[t + half]
        even = int(inv2) * (a + bb)
        odd = int(inv2 * xt**-1) * (a - bb)
        out[t] = even + int(r) * odd
        xt *= omega
    return out

def bitrev(i, k):
    r = 0
    for _ in range(k):
        r = (r << 1) | (i & 1); i >>= 1
    return r

RATE_LOG = 1          # rate 1/2: domain = 2n
NUM_QUERIES = 20      # demo (~2^-20); a production run uses ~80-100

# ---------------------------------------------------------------- setup
def setup(seed, n, k):
    """Transparent one-time setup: generators + RS codeword of the BIT-REVERSED
    generator coefficient vector (so round-1's IPA split = first folded var),
    Merkle root.  Verifier key = (seed, root0): 64 bytes."""
    G = [hash_to_curve(seed, i) for i in range(n)]
    U = hash_to_curve(seed, 10**9)
    dom = n << RATE_LOG
    omega = root_of_unity(dom)
    coeffs = [INF] * dom
    for i in range(n):
        coeffs[bitrev(i, k)] = G[i]
    code0 = gfft(coeffs, omega)
    tree0 = merkle_tree(code0)
    return G, U, code0, tree0, omega

# ---------------------------------------------------------------- prover
def lens_prove(G, U, code0, tree0, omega, a, z):
    n = len(a); k = n.bit_length() - 1
    b = [z**i for i in range(n)]
    C = msm(a, G)
    v = inner(a, b)
    tr = Transcript("lens")
    tr.absorb_point("C", C); tr.absorb("z", z); tr.absorb("v", v)
    tr.absorb("root0", tree0[-1][0])

    Ls, Rs, xs = [], [], []
    layers, trees = [code0], [tree0]
    aa, bb, GG = list(a), list(b), list(G)
    code, w = code0, omega
    while len(aa) > 1:
        m = len(aa) // 2
        aL, aR = aa[:m], aa[m:]; bL, bR = bb[:m], bb[m:]
        GL, GR = GG[:m], GG[m:]
        L = msm(aL, GR) + int(inner(aL, bR)) * U
        R = msm(aR, GL) + int(inner(aR, bL)) * U
        tr.absorb_point("L", L); tr.absorb_point("R", R)
        x = tr.challenge("x")                    # drawn AFTER previous root
        xi = x**-1
        aa = [aL[i] * x + aR[i] * xi for i in range(m)]
        bb = [bL[i] * xi + bR[i] * x for i in range(m)]
        GG = [int(xi) * GL[i] + int(x) * GR[i] for i in range(m)]
        # the SAME x folds the codeword (by x^2; lens_fold_factor):
        code = fri_fold(code, x**2, w)
        tree = merkle_tree(code)
        tr.absorb("root", tree[-1][0])           # committed BEFORE next x
        Ls.append(L); Rs.append(R); xs.append(x)
        layers.append(code); trees.append(tree)
        w = w * w
    W = code[0]                                  # collapsed constant
    # completeness self-check (Lean: lens_foldAll_eq_genFinal + rescale):
    scale = Fq(1)
    for x in xs:
        scale *= x**-1
    assert int(scale) * W == GG[0], "collapsed codeword != folded generator"
    return {"C": C, "v": v, "z": z, "Ls": Ls, "Rs": Rs, "a": aa[0],
            "xs": xs, "k": k, "W": W,
            "layers": layers, "trees": trees,
            "roots": [t[-1][0] for t in trees], "omega": omega}

# ---------------------------------------------------------------- verifier
def lens_verify(U, root0, proof, tampered_layers=None):
    cost = Cost()
    k = proof["k"]; n = 1 << k
    layers = tampered_layers if tampered_layers is not None else proof["layers"]
    trees = proof["trees"]
    if proof["roots"][0] != root0:
        return False, cost, "wrong base root"

    # replay the merged transcript
    tr = Transcript("lens")
    tr.absorb_point("C", proof["C"]); tr.absorb("z", proof["z"])
    tr.absorb("v", proof["v"])
    tr.absorb("root0", proof["roots"][0])
    xs = []
    for j in range(k):
        tr.absorb_point("L", proof["Ls"][j]); tr.absorb_point("R", proof["Rs"][j])
        x = tr.challenge("x"); xs.append(x)
        tr.absorb("root", proof["roots"][j + 1])
    if xs != proof["xs"]:
        return False, cost, "transcript mismatch"

    # FRI consistency: NUM_QUERIES walks down the k levels
    dom = n << RATE_LOG
    inv2 = Fq(2)**-1
    for _ in range(NUM_QUERIES):
        pos = tr.challenge_idx("query", dom)
        w = proof["omega"]
        for i in range(k):
            half = len(layers[i]) // 2
            t = pos % half
            aP, bP = layers[i][t], layers[i][t + half]
            if not merkle_check(proof["roots"][i], t, aP,
                                merkle_path(trees[i], t), cost):
                return False, cost, f"merkle fail level {i}"
            if not merkle_check(proof["roots"][i], t + half, bP,
                                merkle_path(trees[i], t + half), cost):
                return False, cost, f"merkle fail level {i}"
            xt = w ** t
            even = int(inv2) * (aP + bP)
            odd = int(inv2 * xt**-1) * (aP - bP)
            folded = even + int(xs[i]**2) * odd
            cost.smul += 3
            if folded != layers[i + 1][t]:
                return False, cost, f"fold check fail level {i}"
            pos = t; w = w * w
    # final constant layer
    if not merkle_check(proof["roots"][k], 0, layers[k][0],
                        merkle_path(trees[k], 0), cost):
        return False, cost, "final merkle fail"
    W = layers[k][0]

    # IPA checks with Q = (prod x^-1) * W
    scale = Fq(1)
    for x in xs:
        scale *= x**-1
    Q = int(scale) * W; cost.smul += 1
    b0 = Fq(1)
    for j in range(k):
        b0 *= xs[j]**-1 + xs[j] * proof["z"]**(2**(k - 1 - j))
    P0 = proof["C"] + int(proof["v"]) * U; cost.smul += 1
    for j, x in enumerate(xs):
        P0 += int(x**2) * proof["Ls"][j] + int(x**-2) * proof["Rs"][j]
        cost.smul += 2
    if P0 != int(proof["a"]) * Q + int(proof["a"] * b0) * U:
        return False, cost, "final IPA equation failed"
    cost.smul += 2
    return True, cost, "ok"

def linear_verify(G, U, proof):
    """Baseline: standard Bulletproofs verifier — G0 by the n-term MSM."""
    cost = Cost()
    k = proof["k"]; xs = proof["xs"]; n = 1 << k
    s = []
    for i in range(n):
        val = Fq(1)
        for j in range(k):
            val *= xs[j] if (i >> (k - 1 - j)) & 1 else xs[j]**-1
        s.append(val)
    G0 = msm(s, G, cost)
    b0 = Fq(1)
    for j in range(k):
        b0 *= xs[j]**-1 + xs[j] * proof["z"]**(2**(k - 1 - j))
    P0 = proof["C"] + int(proof["v"]) * U
    for j, x in enumerate(xs):
        P0 += int(x**2) * proof["Ls"][j] + int(x**-2) * proof["Rs"][j]
    ok = (P0 == int(proof["a"]) * G0 + int(proof["a"] * b0) * U)
    return ok, cost

def proof_size_bytes(proof):
    k = proof["k"]; n = 1 << k; dom = n << RATE_LOG
    grp = 2 * k + 2                                   # L,R + C + W
    roots = (k + 1) * 32
    per_query = 0
    m = dom
    for i in range(k):
        per_query += 2 * 64 + 2 * 32 * (m.bit_length() - 1)   # 2 pts + 2 paths
        m //= 2
    return grp * 64 + roots + NUM_QUERIES * per_query + 32

# ---------------------------------------------------------------- demo
def main():
    set_random_seed(7)
    seed = b"lens-demo"
    print("=== LENS on Pallas: the IPA fold doubles as the FRI fold ===")
    print(f"    (rate 1/{1 << RATE_LOG} codeword, {NUM_QUERIES} queries — demo "
          f"soundness ~2^-{NUM_QUERIES}; production uses ~80-100)\n")

    rows = []
    for k in (6, 8, 11):
        n = 1 << k
        t0 = time.time()
        G, U, code0, tree0, omega = setup(seed, n, k)
        tsetup = time.time() - t0
        a = [Fq.random_element() for _ in range(n)]
        z = Fq.random_element()

        t0 = time.time()
        proof = lens_prove(G, U, code0, tree0, omega, a, z)
        tp = time.time() - t0

        # plain IPA prover baseline (no codeword folding/hashing)
        t0 = time.time()
        b = [z**i for i in range(n)]
        C2 = msm(a, G); _ = inner(a, b)
        aa, bb2, GG = list(a), list(b), list(G)
        tr2 = Transcript("plain")
        while len(aa) > 1:
            m = len(aa) // 2
            L = msm(aa[:m], GG[m:]) + int(inner(aa[:m], bb2[m:])) * U
            R = msm(aa[m:], GG[:m]) + int(inner(aa[m:], bb2[:m])) * U
            tr2.absorb_point("L", L); tr2.absorb_point("R", R)
            x = tr2.challenge("x"); xi = x**-1
            aa = [aa[i] * x + aa[m + i] * xi for i in range(m)]
            bb2 = [bb2[i] * xi + bb2[m + i] * x for i in range(m)]
            GG = [int(xi) * GG[i] + int(x) * GG[m + i] for i in range(m)]
        tipa = time.time() - t0

        t0 = time.time()
        ok, cost, msg = lens_verify(U, tree0[-1][0], proof)
        tv = time.time() - t0
        assert ok, msg

        t0 = time.time()
        ok2, cl = linear_verify(G, U, proof)
        tnaive = time.time() - t0
        assert ok2

        pkb = proof_size_bytes(proof) / 1024.0
        rows.append((n, tsetup, tp, tipa, tv, tnaive, cost, cl, pkb))
        print(f"  n={n:>5}: setup(1-time) {tsetup:6.1f}s | prove {tp:6.1f}s "
              f"(plain IPA {tipa:5.1f}s, x{tp/tipa:3.1f}) | verify {tv:5.2f}s "
              f"vs naive {tnaive:6.2f}s | proof {pkb:6.1f} KB", flush=True)

    # tamper tests at the last size
    print("\n[tamper]  corrupted codeword layer  -> ", end="")
    bad_layers = [list(l) for l in proof["layers"]]
    bad_layers[1] = [P + G[0] for P in bad_layers[1]]
    okb, _, msgb = lens_verify(U, tree0[-1][0], proof, tampered_layers=bad_layers)
    print(f"REJECT ({msgb})" if not okb else "ACCEPT (!!)"); assert not okb

    print("[tamper]  wrong collapsed W         -> ", end="")
    bad = dict(proof)
    bad_layers = [list(l) for l in proof["layers"]]
    bad_layers[-1] = [bad_layers[-1][0] + G[0]] + bad_layers[-1][1:]
    okb, _, msgb = lens_verify(U, tree0[-1][0], proof, tampered_layers=bad_layers)
    print(f"REJECT ({msgb})" if not okb else "ACCEPT (!!)"); assert not okb

    print("\n  === summary ===")
    print(f"  {'n':>6} {'verify(s)':>10} {'naive(s)':>9} {'speedup':>8} "
          f"{'vfy smul':>9} {'naive smul':>11} {'proof':>9}")
    for (n, ts, tp, tipa, tv, tn, c, cl, pkb) in rows:
        print(f"  {n:>6} {tv:>9.2f}s {tn:>8.2f}s {tn/tv:>7.1f}x "
              f"{c.smul:>9} {cl.smul:>11} {pkb:>7.1f}KB")
    last = rows[-1]
    print(f"\n  VERDICT: at n = {last[0]}, Lens verifies in {last[4]:.2f}s vs "
          f"naive {last[5]:.2f}s ({last[5]/last[4]:.1f}x) with a "
          f"{last[8]:.0f} KB proof")
    print("  (Genesis at n=2048: 8379 KB proof — Lens is ~40x smaller; "
          "verifier is O(q*log n) smuls +")
    print("   O(q*log^2 n) hashes; prover ~2x plain IPA vs Genesis's ~8x.)")

main()
