# 2-genesis.sage — executable demo of Genesis (see solutions/2-genesis.md)
#
# Genesis = Bulletproofs/IPA polynomial commitment where the verifier's single
# linear-cost step — the folded-generator MSM  G0 = <s, G>  — is not computed by
# the verifier but DELEGATED: the prover attaches a sumcheck certificate that
# walks the MSM's binary addition tree (divide and conquer), and the verifier
# does O(1) group operations per round.  Setup is transparent: publish a seed;
# the generators are G_i = HashToCurve(seed, i).
#
# What is real in this demo:
#   * setup from a seed (try-and-increment hash-to-curve on secp256k1)
#   * Pedersen commitment, Bulletproofs IPA opening (Fiat-Shamir, non-ZK)
#   * the delegation certificate: a GROUP-VALUED SUMCHECK over the hypercube,
#     round polys of degree 2 sent as evaluations at {0,1,2}; verifier checks
#     p(0)+p(1) == claim and folds with Lagrange — O(1) group ops per round
#   * the s-side terminal check via the O(log n) tensor closed form
#     (the Lean-proven identity `bSuccinct_eq_bLinear` / `sCoeff` tensor)
#   * cost accounting separating the verifier's polylog work from the one
#     delegated stage
#
# What is a stand-in (clearly labeled):
#   * the terminal generator-MLE evaluation Gtilde(r).  In full Genesis this is
#     certified by a GKR proof over the seed->generators derivation circuit
#     (input = seed alone; see solutions/2-genesis.md and SuccinctIPA/Genesis.lean
#     for the gate-level correctness lemmas).  Here an oracle computes it
#     directly and its cost is counted separately, NOT as verifier work.
#     Delegating it with *another* sumcheck would only reproduce the same
#     terminal problem — that regress is the Lean theorem `mleG_is_msm`
#     ("conservation of linear work"); GKR-over-the-derivation is the escape.
#
# Run:  sage sage/2-genesis.sage

import hashlib

# ----------------------------------------------------------------------------
# Curve: secp256k1 (any prime-order curve works; nothing curve-specific below)
# ----------------------------------------------------------------------------
p = 2**256 - 2**32 - 977
q = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
E = EllipticCurve(GF(p), [0, 7])
Fq = GF(q)                      # scalar field
INF = E(0)

# ----------------------------------------------------------------------------
# Fiat-Shamir transcript
# ----------------------------------------------------------------------------
class Transcript:
    def __init__(self, label):
        self.h = hashlib.sha256(label.encode()).digest()
    def absorb(self, label, obj):
        data = label.encode() + b"|" + repr(obj).encode()
        self.h = hashlib.sha256(self.h + data).digest()
    def absorb_point(self, label, P):
        self.absorb(label, "INF" if P == INF else (int(P[0]), int(P[1])))
    def challenge(self, label):
        while True:
            self.h = hashlib.sha256(self.h + label.encode()).digest()
            x = Fq(int.from_bytes(self.h, "big"))
            if x != 0:
                return x

# ----------------------------------------------------------------------------
# Setup — transparent: PUBLISH A SEED.  Generators are derived, not stored.
# ----------------------------------------------------------------------------
def hash_to_curve(seed, i):
    ctr = 0
    while True:
        d = hashlib.sha256(f"{seed}|gen|{i}|{ctr}".encode()).digest()
        x = GF(p)(int.from_bytes(d, "big"))
        rhs = x**3 + 7
        if rhs.is_square():
            y = rhs.sqrt()
            y = min(y, -y)      # deterministic branch
            return E(x, y)
        ctr += 1

def setup(seed, n):
    """In Genesis the setup IS the seed; materializing G is the prover's job
    (and, inside the full scheme, the delegated circuit's job)."""
    G = [hash_to_curve(seed, i + 1) for i in range(n)]
    U = hash_to_curve(seed, 0)
    return G, U

# ----------------------------------------------------------------------------
# Small helpers
# ----------------------------------------------------------------------------
def msm(scalars, points):
    acc = INF
    for s, P in zip(scalars, points):
        acc += int(s) * P
    return acc

def inner(u, v):
    return sum((a * b for a, b in zip(u, v)), Fq(0))

def s_vector(xs, k):
    """s_i = prod_j x_j^{+1 if bit, -1 else}, round j splitting the MSB first
    (the Lean `sCoeff`, indexed by bit-sets)."""
    n = 1 << k
    s = []
    for i in range(n):
        acc = Fq(1)
        for j in range(k):
            bit = (i >> (k - 1 - j)) & 1
            acc *= xs[j] if bit else xs[j]**-1
        s.append(acc)
    return s

# ----------------------------------------------------------------------------
# Prover — commit, IPA transcript, and the Genesis delegation certificate
# ----------------------------------------------------------------------------
def commit(G, a):
    return msm(a, G)

def ipa_prove(tr, G, U, a, b):
    """Standard BP inner-product argument for: C = <a,G> and <a,b> = v,
    run on P = C + v*U.  Returns (L_j, R_j) pairs and the final scalar."""
    a, b, Gv = list(a), list(b), list(G)
    Ls, Rs = [], []
    while len(a) > 1:
        m = len(a) // 2
        aL, aH = a[:m], a[m:]
        bL, bH = b[:m], b[m:]
        GL, GH = Gv[:m], Gv[m:]
        L = msm(aL, GH) + int(inner(aL, bH)) * U
        R = msm(aH, GL) + int(inner(aH, bL)) * U
        tr.absorb_point("L", L); tr.absorb_point("R", R)
        x = tr.challenge("x"); xi = x**-1
        a  = [x * aL[i] + xi * aH[i] for i in range(m)]
        b  = [xi * bL[i] + x * bH[i] for i in range(m)]
        Gv = [int(xi) * GL[i] + int(x) * GH[i] for i in range(m)]
        Ls.append(L); Rs.append(R)
    return Ls, Rs, a[0], Gv[0]

def sumcheck_prove(tr, s, Gvec, Q):
    """Genesis delegation certificate for the claim  Q = sum_i s_i * G_i.
    Group-valued sumcheck over {0,1}^k: summand stilde(b)*Gtilde(b) is
    degree <= 2 per variable, so each round sends p(0), p(1), p(2)."""
    S, GV = list(s), list(Gvec)
    tr.absorb_point("Q", Q)
    rounds, rs = [], []
    while len(S) > 1:
        m = len(S) // 2
        SL, SH = S[:m], S[m:]
        GL, GH = GV[:m], GV[m:]
        P0 = msm(SL, GL)                                   # p(0)
        P1 = msm(SH, GH)                                   # p(1)
        S2 = [2 * SH[i] - SL[i] for i in range(m)]         # linear ext. at X=2
        G2 = [2 * GH[i] - GL[i] for i in range(m)]
        P2 = msm(S2, G2)                                   # p(2)
        for lbl, P in (("p0", P0), ("p1", P1), ("p2", P2)):
            tr.absorb_point(lbl, P)
        r = tr.challenge("r")
        S  = [(1 - r) * SL[i] + r * SH[i] for i in range(m)]
        GV = [GL[i] + int(r) * (GH[i] - GL[i]) for i in range(m)]
        rounds.append((P0, P1, P2)); rs.append(r)
    return rounds

def prove(seed, G, U, a, z):
    """Open the commitment at z: prove a_hat(z) = v."""
    n = len(a); k = n.bit_length() - 1
    b = [z**i for i in range(n)]
    v = inner(a, b)
    C = commit(G, a)

    tr = Transcript("genesis-demo")
    tr.absorb("seed", seed); tr.absorb_point("C", C)
    tr.absorb("z", int(z)); tr.absorb("v", int(v))

    Ls, Rs, a_final, G_final = ipa_prove(tr, G, U, a, b)

    # the deferred claim: Q = <s, G>  (prover computes it; verifier will not)
    xs = replay_ipa_challenges(seed, C, z, v, Ls, Rs)
    s = s_vector(xs, k)
    Q = msm(s, G)
    assert Q == G_final, "internal: folded generator != <s,G>"

    rounds = sumcheck_prove(tr, s, G, Q)
    return {"C": C, "v": v, "Ls": Ls, "Rs": Rs, "a_final": a_final,
            "Q": Q, "rounds": rounds}

def replay_ipa_challenges(seed, C, z, v, Ls, Rs):
    tr = Transcript("genesis-demo")
    tr.absorb("seed", seed); tr.absorb_point("C", C)
    tr.absorb("z", int(z)); tr.absorb("v", int(v))
    xs = []
    for L, R in zip(Ls, Rs):
        tr.absorb_point("L", L); tr.absorb_point("R", R)
        xs.append(tr.challenge("x"))
    return xs

# ----------------------------------------------------------------------------
# Verifier — polylog online work; the one delegated stage is a labeled oracle
# ----------------------------------------------------------------------------
class Cost:
    def __init__(self):
        self.smul = 0; self.gadd = 0; self.field = 0; self.oracle_smul = 0
    def report(self, n, k):
        print(f"      verifier group scalar-mults : {self.smul}   (polylog; n = {n})")
        print(f"      verifier group additions    : {self.gadd}")
        print(f"      verifier field ops (approx) : {self.field}")
        print(f"      [oracle] Gtilde(r) smuls    : {self.oracle_smul}   "
              f"<- delegated in full Genesis (GKR over seed->G derivation)")

def generator_mle_oracle(G, rs, cost):
    """THE GENESIS STAND-IN.  Full Genesis certifies this value with a GKR
    proof over the derivation circuit seed -> (G_i) -> fold — whose input is
    the O(log n)-sized (seed, challenges), so the verifier's own input-MLE
    check is trivial (Lean: `genesis_reduction` + gate lemmas
    `double_and_add_step`, `square_and_multiply_step`, `sqrt_exp_correct`).
    Here we evaluate directly and book the cost to the oracle, not the
    verifier."""
    GV = list(G)
    for r in rs:
        m = len(GV) // 2
        GV = [GV[i] + int(r) * (GV[m + i] - GV[i]) for i in range(m)]
        cost.oracle_smul += m
    return GV[0]

def verify(seed, U, G_for_oracle, z, proof, n):
    k = n.bit_length() - 1
    C, v = proof["C"], proof["v"]
    Ls, Rs, a_f, Q = proof["Ls"], proof["Rs"], proof["a_final"], proof["Q"]
    cost = Cost()

    tr = Transcript("genesis-demo")
    tr.absorb("seed", seed); tr.absorb_point("C", C)
    tr.absorb("z", int(z)); tr.absorb("v", int(v))

    # --- IPA challenges + folded commitment:  O(log n) group ops -------------
    xs = []
    P0 = C + int(v) * U; cost.smul += 1; cost.gadd += 1
    for L, R in zip(Ls, Rs):
        tr.absorb_point("L", L); tr.absorb_point("R", R)
        x = tr.challenge("x"); xs.append(x)
        P0 += int(x**2) * L + int(x**-2) * R
        cost.smul += 2; cost.gadd += 2

    # --- b0 via the O(log n) closed form (Lean: bSuccinct_eq_bLinear) --------
    b0 = Fq(1)
    for j in range(k):
        b0 *= xs[j]**-1 + xs[j] * z**(2**(k - 1 - j))
        cost.field += 4

    # --- delegation certificate: sumcheck for  Q = <s, G> --------------------
    tr.absorb_point("Q", Q)
    claim = Q
    rs = []
    inv2 = Fq(2)**-1
    for (R0, R1, R2) in proof["rounds"]:
        if R0 + R1 != claim:                       # the round check
            return False, cost, "sumcheck round check failed"
        cost.gadd += 1
        for lbl, P in (("p0", R0), ("p1", R1), ("p2", R2)):
            tr.absorb_point(lbl, P)
        r = tr.challenge("r"); rs.append(r)
        l0 = (r - 1) * (r - 2) * inv2              # Lagrange on {0,1,2}
        l1 = -r * (r - 2)
        l2 = r * (r - 1) * inv2
        claim = int(l0) * R0 + int(l1) * R1 + int(l2) * R2
        cost.smul += 3; cost.gadd += 2; cost.field += 8

    # --- terminal checks ------------------------------------------------------
    # s-side: tensor closed form, O(log n)  (Lean: the sCoeff tensor identity)
    s_at_r = Fq(1)
    for j in range(k):
        s_at_r *= (1 - rs[j]) * xs[j]**-1 + rs[j] * xs[j]
        cost.field += 5
    # G-side: the ONE delegated stage (see generator_mle_oracle docstring)
    G_at_r = generator_mle_oracle(G_for_oracle, rs, cost)
    if claim != int(s_at_r) * G_at_r:
        return False, cost, "sumcheck final check failed"
    cost.smul += 1

    # --- final IPA equation:  P0 == a*Q + (a*b0)*U ----------------------------
    if P0 != int(a_f) * Q + int(a_f * b0) * U:
        return False, cost, "final IPA equation failed"
    cost.smul += 2; cost.gadd += 1
    return True, cost, "ok"

# ----------------------------------------------------------------------------
# Demo
# ----------------------------------------------------------------------------
def run_size(k, seed):
    """Run one honest prove/verify at size n = 2^k; return verifier cost."""
    n = 1 << k
    G, U = setup(seed, n)
    a = [Fq.random_element() for _ in range(n)]
    z = Fq.random_element()
    proof = prove(seed, G, U, a, z)
    ok, cost, _ = verify(seed, U, G, z, proof, n)
    assert ok
    return cost

def main():
    k = 6; n = 1 << k
    seed = "genesis-demo-seed-v1"
    print(f"=== Genesis demo ===  n = {n} (k = {k}), curve = secp256k1")

    print("[setup]   publish seed; derive generators (prover-side)")
    G, U = setup(seed, n)

    a = [Fq.random_element() for _ in range(n)]      # committed coefficients
    z = Fq.random_element()                          # evaluation point
    print("[commit]  C = <a, G>")
    print("[prove]   IPA transcript + sumcheck delegation certificate")
    proof = prove(seed, G, U, a, z)

    # numerical confirmation of the Lean identity bSuccinct_eq_bLinear
    xs = replay_ipa_challenges(seed, proof["C"], z, proof["v"],
                               proof["Ls"], proof["Rs"])
    s = s_vector(xs, k)
    closed = Fq(1)
    for j in range(k):
        closed *= xs[j]**-1 + xs[j] * z**(2**(k - 1 - j))
    naive = sum((s[i] * z**i for i in range(n)), Fq(0))
    assert closed == naive
    print("[check]   bSuccinct_eq_bLinear holds numerically  "
          "(O(log n) product == O(n) sum)")

    print("[verify]  ", end="")
    ok, cost, msg = verify(seed, U, G, z, proof, n)
    print("ACCEPT" if ok else f"REJECT ({msg})")
    assert ok
    cost.report(n, k)
    print(f"      proof size: {2 * len(proof['Ls'])} IPA group elts "
          f"+ {3 * len(proof['rounds'])} sumcheck group elts + 1 scalar")

    # --- soundness smoke tests ------------------------------------------------
    print("[tamper]  wrong claimed Q          ->", end=" ")
    bad = dict(proof); bad["Q"] = proof["Q"] + G[0]
    ok, _, msg = verify(seed, U, G, z, bad, n)
    print(f"REJECT ({msg})" if not ok else "ACCEPT (!!)"); assert not ok

    print("[tamper]  corrupted round poly     ->", end=" ")
    bad = dict(proof)
    r0 = list(proof["rounds"]); P0x, P1x, P2x = r0[0]
    r0[0] = (P0x + G[1], P1x, P2x); bad["rounds"] = r0
    ok, _, msg = verify(seed, U, G, z, bad, n)
    print(f"REJECT ({msg})" if not ok else "ACCEPT (!!)"); assert not ok

    print("[tamper]  wrong evaluation value v ->", end=" ")
    bad = dict(proof); bad["v"] = proof["v"] + 1
    ok, _, msg = verify(seed, U, G, z, bad, n)
    print(f"REJECT ({msg})" if not ok else "ACCEPT (!!)"); assert not ok

    print("=== all checks passed ===")

    # --- scaling: the verifier is sublinear, the naive verifier is not -------
    print("\n=== scaling (verifier group scalar-mults vs n) ===")
    print(f"      {'n':>6}  {'verifier smuls':>14}  {'naive verifier':>14}  "
          f"{'delegated stage':>15}")
    for kk in (4, 6, 8):
        c = run_size(kk, seed)
        nn = 1 << kk
        print(f"      {nn:>6}  {c.smul:>14}  {nn:>14}  {c.oracle_smul:>15}")
    print("      (verifier grows ~ 5*log2(n) + 4; naive = n; the delegated")
    print("       column is what full Genesis pushes into GKR-over-derivation)")

main()
