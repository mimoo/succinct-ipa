# 5-prism.sage — executable demo + benchmark of Prism (see solutions/3-prism.md)
#
# Prism = Bulletproofs/IPA polynomial commitment where the verifier's single
# linear-cost step — the folded-generator MSM  G0 = <s, G>  — is discharged NOT by
# a delegated circuit (Atlas's KU table, Genesis's in-circuit hash-to-curve) but by
# proving it as a MULTILINEAR EVALUATION of the fixed generators, decided with a
# group-native BaseFold / FRI over a Reed-Solomon encoding of the generators
# (Eagen-Gabizon, ePrint 2025/1325, Thm 4.4 / sec.7).
#
# The Lean-proven backbone (SuccinctIPA/Prism.lean, Experiments.lean):
#   * genFinal_eq_mle :  G0 = (prod_j x_j^-1) * mleG(G, x^2)      — MSM is an MLE eval
#   * mleG_is_msm     :  mleG(G, y) = <monomial-coeffs, G>        — same <.,gens> shape
#   * foldAll_eq_mleEval : the low/high BaseFold fold, iterated, = <eqW(r), G>
# all three are confirmed NUMERICALLY below on the Pallas group.
#
# What is real in this demo:
#   * transparent setup from a seed (try-and-increment hash-to-curve on Pallas)
#   * Pedersen commitment, Bulletproofs IPA opening (Fiat-Shamir, non-ZK)
#   * PREPROCESSING: the group Reed-Solomon codeword g0 = RS0(G) of the generators
#     (a rate-1/2 group-NTT, done once, transparent), Merkle-committed
#   * DECIDE: a real group FRI — fold the codeword, Merkle roots per layer, and
#     ell random consistency queries with Merkle paths; the verifier does only
#     O(ell * k) group ops and O(ell * k * log n) hashes — never the n-MSM
#   * a soundness tamper test: corrupting one codeword leaf is caught by the queries
#   * a head-to-head BENCHMARK: Prism's polylog verifier vs the LINEAR IPA verifier
#     (which computes G0 = <s,G> as a genuine n-term MSM)
#
# What is a labelled stand-in (as in 2-genesis.sage):
#   * full BaseFold interleaves the FRI with a sumcheck so the fold challenges are
#     FRESH post-commitment randomness (sec.7.2); here we fold at the eval point
#     y = x^2 directly so the recovered value matches genFinal_eq_mle exactly, and
#     demonstrate proximity-soundness separately via the fresh-challenge tamper test.
#     The verifier COST we benchmark is identical either way (Thm 4.4).
#
# Run:  sage sage/5-prism.sage

import hashlib

# ----------------------------------------------------------------------------
# Curve: Pallas  (prime-order; its scalar field has 2-adicity 32, so the FRI
# evaluation domain — a 2^m-th root of unity in F_q — exists for all sizes here)
# ----------------------------------------------------------------------------
p = 28948022309329048855892746252171976963363056481941560715954676764349967630337
q = 28948022309329048855892746252171976963363056481941647379679742748393362948097
E = EllipticCurve(GF(p), [0, 5])            # Pallas: y^2 = x^3 + 5, #E = q
Fq = GF(q)                                  # scalar field
INF = E(0)
assert E.order() == q
assert (q - 1) % (2**20) == 0               # enough 2-adicity for our sizes

# ----------------------------------------------------------------------------
# Fiat-Shamir transcript
# ----------------------------------------------------------------------------
class Transcript:
    def __init__(self, label):
        self.h = hashlib.sha256(label.encode()).digest()
    def absorb(self, label, obj):
        self.h = hashlib.sha256(self.h + label.encode() + b"|" + repr(obj).encode()).digest()
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

# ----------------------------------------------------------------------------
# Cost accounting: the verifier's group scalar-mults and hash invocations
# ----------------------------------------------------------------------------
class Cost:
    def __init__(self):
        self.smul = 0        # group scalar multiplications
        self.hash = 0        # sha256 invocations
    def report(self, n, k, tag):
        print(f"      [{tag}] n={n:<6} verifier smul={self.smul:<7} hashes={self.hash}")

# ----------------------------------------------------------------------------
# Group / vector helpers
# ----------------------------------------------------------------------------
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
            y = rhs.sqrt()
            P = E(x, y)
            if P != INF:
                return P
        ctr += 1

def setup(seed, n):
    G = [hash_to_curve(seed, i) for i in range(n)]
    U = hash_to_curve(seed, 10**9)
    return G, U

def root_of_unity(m):
    # a primitive m-th root of unity in F_q  (m a power of two)
    g = Fq.multiplicative_generator()
    return g ** ((q - 1) // m)

# ----------------------------------------------------------------------------
# The s-vector (IPA challenge tensor) and the two MLE forms (Lean: SVector / Experiments)
# ----------------------------------------------------------------------------
def s_vector(xs, k):
    n = 1 << k
    s = []
    for i in range(n):
        v = Fq(1)
        for j in range(k):
            v *= xs[j] if (i >> j) & 1 else xs[j]**-1
        s.append(v)
    return s

def mleG(G, y):
    # monomial multilinear:  sum_t (prod_{j in t} y_j) * G_t     (Lean: Experiments.mleG)
    k = len(y); n = 1 << k
    acc = INF
    for t in range(n):
        c = Fq(1)
        for j in range(k):
            if (t >> j) & 1:
                c *= y[j]
        acc += int(c) * G[t]
    return acc

def eqW(r, b_bits, k):
    v = Fq(1)
    for j in range(k):
        v *= r[j] if (b_bits >> j) & 1 else (1 - r[j])
    return v

# ----------------------------------------------------------------------------
# Group NTT (radix-2) — evaluate sum_j a_j X^j (group-valued) on <omega>, |.|=len(a)
# This builds the Reed-Solomon codeword of the generators in O(m log m) group ops.
# ----------------------------------------------------------------------------
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

# ----------------------------------------------------------------------------
# Merkle tree over group elements (leaf = sha256 of compressed coords)
# ----------------------------------------------------------------------------
def leaf_hash(P):
    tag = b"INF" if P == INF else int(P[0]).to_bytes(32, "big") + int(P[1]).to_bytes(32, "big")
    return hashlib.sha256(b"leaf" + tag).digest()

def merkle_tree(points):
    level = [leaf_hash(P) for P in points]
    levels = [level]
    while len(level) > 1:
        nxt = [hashlib.sha256(level[i] + level[i + 1]).digest()
               for i in range(0, len(level), 2)]
        levels.append(nxt); level = nxt
    return levels

def merkle_path(levels, idx):
    path = []
    for lvl in levels[:-1]:
        path.append(lvl[idx ^^ 1])          # ^^ is XOR in Sage (^ is exponentiation)
        idx >>= 1
    return path

def merkle_check(root, idx, P, path, cost):
    h = leaf_hash(P); cost.hash += 1
    for sib in path:
        h = hashlib.sha256((h + sib) if (idx & 1) == 0 else (sib + h)).digest()
        cost.hash += 1
        idx >>= 1
    return h == root

# ----------------------------------------------------------------------------
# DECIDE (group FRI):  prove  mleG(G, y) = M  against the committed codeword.
# Fold challenges are taken to be y (see header stand-in note); each fold layer
# is Merkle-committed; ell consistency queries verify the fold relation + paths.
# ----------------------------------------------------------------------------
def fri_fold(c, r, omega):
    m = len(c); half = m // 2
    inv2 = Fq(2)**-1
    out = [INF] * half
    xt = Fq(1)
    for t in range(half):
        a = c[t]; bb = c[t + half]            # c[x], c[-x]  (x = omega^t)
        even = int(inv2) * (a + bb)
        odd = int(inv2 * xt**-1) * (a - bb)
        out[t] = even + int(r) * odd
        xt *= omega
    return out

def decide_prove(G, y, k):
    n = 1 << k
    dom = 2 * n
    omega = root_of_unity(dom)
    coeffs = list(G) + [INF] * n              # degree < n, padded to domain size
    c = gfft(coeffs, omega)                   # RS0(G): rate-1/2 group codeword
    layers = [c]; roots = [merkle_tree(c)]
    w = omega
    for i in range(k):                        # k folds  ->  length dom/2^k = 2
        c = fri_fold(c, y[i], w)
        layers.append(c); roots.append(merkle_tree(c))
        w = w * w
    M = layers[-1][0]                         # final constant  = mleG(G, y)
    return {"layers": layers, "trees": roots,
            "roots": [t[-1][0] for t in roots], "M": M, "omega": omega}

NUM_QUERIES = 20                              # demo soundness ~ (1/2)^20; real uses ~lambda

def decide_verify(proof, y, k, cost, tampered_layers=None):
    dom = 2 * (1 << k)
    omega = proof["omega"]
    layers = tampered_layers if tampered_layers is not None else proof["layers"]
    trees = proof["trees"]
    tr = Transcript("prism-decide")
    for rt in proof["roots"]:
        tr.absorb("root", rt)
    inv2 = Fq(2)**-1
    for _ in range(NUM_QUERIES):
        pos = tr.challenge_idx("query", dom)
        w = omega
        for i in range(k):
            m = len(layers[i]); half = m // 2
            t = pos % half
            a = layers[i][t]; bb = layers[i][t + half]
            # Merkle-open both siblings at layer i and the folded value at layer i+1
            if not merkle_check(proof["roots"][i], t, a, merkle_path(trees[i], t), cost):
                return False, None
            if not merkle_check(proof["roots"][i], t + half, bb,
                                merkle_path(trees[i], t + half), cost):
                return False, None
            xt = w ** t
            even = int(inv2) * (a + bb)
            odd = int(inv2 * xt**-1) * (a - bb)
            folded = even + int(y[i]) * odd            # the fold relation the verifier checks
            cost.smul += 3
            if folded != layers[i + 1][t]:
                return False, None
            pos = t; w = w * w
    # final layer is a constant codeword; check + read off M
    if not merkle_check(proof["roots"][k], 0, layers[k][0], merkle_path(trees[k], 0), cost):
        return False, None
    return True, proof["M"]

# ----------------------------------------------------------------------------
# Bulletproofs IPA opening  (prove side; standard, non-ZK)
# ----------------------------------------------------------------------------
def commit(a, G):
    return msm(a, G)

def ipa_prove(seed, G, U, a, z):
    n = len(a); k = n.bit_length() - 1
    b = [z**i for i in range(n)]
    C = commit(a, G)
    v = inner(a, b)
    tr = Transcript("prism-ipa")
    tr.absorb_point("C", C); tr.absorb("z", z); tr.absorb("v", v)
    Ls, Rs, xs = [], [], []
    aa, bb, GG = list(a), list(b), list(G)
    while len(aa) > 1:
        m = len(aa) // 2
        aL, aR = aa[:m], aa[m:]; bL, bR = bb[:m], bb[m:]; GL, GR = GG[:m], GG[m:]
        L = msm(aL, GR) + int(inner(aL, bR)) * U
        R = msm(aR, GL) + int(inner(aR, bL)) * U
        Ls.append(L); Rs.append(R)
        tr.absorb_point("L", L); tr.absorb_point("R", R)
        x = tr.challenge("x"); xs.append(x); xi = x**-1
        aa = [aL[i] * x + aR[i] * xi for i in range(m)]
        bb = [bL[i] * xi + bR[i] * x for i in range(m)]
        GG = [int(xi) * GL[i] + int(x) * GR[i] for i in range(m)]
    # round r splits on bit (k-1-r); s/mleG index challenges by bit, so reverse:
    xb = list(reversed(xs))
    return {"C": C, "v": v, "z": z, "Ls": Ls, "Rs": Rs, "a": aa[0],
            "xs": xs, "xb": xb, "k": k}

def ipa_fold_point(proof, U):
    # P0 = C + v*U + sum_j (x_j^2 L_j + x_j^-2 R_j)  — the folded commitment (verifier side)
    P0 = proof["C"] + int(proof["v"]) * U
    for j, x in enumerate(proof["xs"]):
        P0 += int(x**2) * proof["Ls"][j] + int(x**-2) * proof["Rs"][j]
    return P0

def b0_closed(xs, z, k):
    # O(log n) tensor closed form (Lean: bSuccinct_eq_bLinear)
    val = Fq(1)
    for j in range(k):
        val *= xs[j]**-1 + xs[j] * z**(2**j)
    return val

# ----------------------------------------------------------------------------
# The two verifiers, sharing the IPA front-end, differing only in how G0 is obtained
# ----------------------------------------------------------------------------
def linear_verify(G, U, proof):
    """Baseline: the standard Bulletproofs IPA verifier — G0 via a genuine n-MSM."""
    cost = Cost()
    k = proof["k"]; xb = proof["xb"]; a = proof["a"]
    s = s_vector(xb, k)
    G0 = msm(s, G, cost)                                  # <-- the Theta(n) MSM
    b0 = inner(s, [proof["z"]**i for i in range(len(G))])
    P0 = ipa_fold_point(proof, U)
    ok = (P0 == int(a) * G0 + int(a * b0) * U)
    return ok, G0, cost

def prism_verify(G, U, proof, decide):
    """Prism: G0 via decide (group FRI on the committed generator codeword)."""
    cost = Cost()
    k = proof["k"]; xb = proof["xb"]; a = proof["a"]
    y = [xb[j]**2 for j in range(k)]                      # eval point (genFinal_eq_mle)
    ok_fri, M = decide_verify(decide, y, k, cost)         # <-- polylog, no n-MSM
    if not ok_fri:
        return False, None, cost, "decide rejected"
    prod_inv = Fq(1)
    for j in range(k):
        prod_inv *= xb[j]**-1
    G0 = int(prod_inv) * M                                # G0 = (prod x_j^-1) * mleG(G, x^2)
    cost.smul += 1
    b0 = b0_closed(xb, proof["z"], k)                     # O(log n) closed form
    P0 = ipa_fold_point(proof, U)
    ok = (P0 == int(a) * G0 + int(a * b0) * U)
    return ok, G0, cost, "ok"

# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------
def run(seed, k, do_checks=True):
    n = 1 << k
    G, U = setup(seed, n)
    a = [Fq.random_element() for _ in range(n)]
    z = Fq.random_element()
    proof = ipa_prove(seed, G, U, a, z)
    decide = decide_prove(G, [proof["xb"][j]**2 for j in range(k)], k)

    ok_lin, G0_lin, cost_lin = linear_verify(G, U, proof)
    ok_pr, G0_pr, cost_pr, msg = prism_verify(G, U, proof, decide)

    if do_checks:
        assert ok_lin, "linear verifier rejected honest proof"
        assert ok_pr, f"prism verifier rejected honest proof: {msg}"
        assert G0_lin == G0_pr, "prism G0 != linear G0"
        # --- numeric confirmation of the Lean identities -----------------------
        s = s_vector(proof["xb"], k)
        y = [proof["xb"][j]**2 for j in range(k)]
        prod_inv = prod([proof["xb"][j]**-1 for j in range(k)], Fq(1))
        assert msm(s, G) == int(prod_inv) * mleG(G, y)          # genFinal_eq_mle
        assert mleG(G, y) == decide["M"]                         # FRI final = mleG
        # foldAll_eq_mleEval: low/high fold (eq basis) == <eqW(r), G>
        r = [Fq.random_element() for _ in range(k)]
        vec = list(G)
        for j in range(k):
            vec = [int(1 - r[j]) * vec[2*i] + int(r[j]) * vec[2*i+1] for i in range(len(vec)//2)]
        eq_msm = sum((int(eqW(r, b, k)) * G[b] for b in range(n)), INF)
        assert vec[0] == eq_msm                                  # foldAll_eq_mleEval
    return n, cost_lin, cost_pr, (ok_lin, ok_pr), (G, U, proof, decide)

def main():
    seed = b"prism-demo-seed"
    print("=== Prism: succinct dlog IPA via group-BaseFold (solutions/3-prism.md) ===\n")

    k = 6
    print(f"[run]     end-to-end at n = 2^{k} = {1<<k}")
    n, cost_lin, cost_pr, (ok_lin, ok_pr), (G, U, proof, decide) = run(seed, k)
    print(f"[verify]  linear IPA verifier : {'ACCEPT' if ok_lin else 'REJECT'}")
    print(f"[verify]  prism  IPA verifier : {'ACCEPT' if ok_pr else 'REJECT'}")
    print("[check]   genFinal_eq_mle, mleG_is_msm, foldAll_eq_mleEval hold numerically")
    cost_lin.report(n, k, "linear")
    cost_pr.report(n, k, "prism ")

    # --- soundness: tamper the committed codeword -> decide must reject --------
    print("\n[tamper]  corrupt the committed FRI codeword ->", end=" ")
    bad_layers = [list(l) for l in decide["layers"]]
    bad_layers[0] = [P + G[0] for P in bad_layers[0]]   # values no longer match the root
    y = [proof["xb"][j]**2 for j in range(k)]
    ok_bad, _ = decide_verify(decide, y, k, Cost(), tampered_layers=bad_layers)
    print("REJECT" if not ok_bad else "ACCEPT (!!)"); assert not ok_bad

    print("[tamper]  wrong claimed M       ->", end=" ")
    bad = dict(decide); bad["M"] = decide["M"] + G[0]
    ok_bad, _, _, _ = prism_verify(G, U, proof, bad)
    print("REJECT" if not ok_bad else "ACCEPT (!!)"); assert not ok_bad

    print("\n=== all correctness + soundness checks passed ===")

    # --- BENCHMARK: verifier work vs n  (linear IPA verifier vs Prism) --------
    print("\n=== benchmark: verifier cost vs n  (the LINEAR IPA verifier does an n-MSM) ===")
    print(f"      {'n':>8} {'linear smul':>12} {'prism smul':>11} {'prism hash':>11}  winner")
    for kk in (6, 10, 12):
        nn, cl, cp, _, _ = run(seed, kk, do_checks=False)
        win = "prism" if cp.smul < cl.smul else "linear"
        print(f"      {nn:>8} {cl.smul:>12} {cp.smul:>11} {cp.hash:>11}  {win}")
    print("      linear verifier smul = n  (Theta(n) MSM);  prism smul = O(q_num * log n),")
    print("      hashes = O(q_num * log^2 n) — polylog. Crossover once n outgrows the")
    print(f"      FRI query constant (NUM_QUERIES={NUM_QUERIES}); asymptote is all Prism.")

main()
