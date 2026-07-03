# 3-genesis-e2e.sage — END-TO-END Genesis on the Pallas curve.
#
# Everything is implemented: the verifier NEVER touches the n generators.
# The single linear step of the Bulletproofs verifier — the folded-generator
# MSM  Q = <s, G>  — is certified by a layered-sumcheck (GKR-style) proof over
# a circuit that includes the DERIVATION OF THE GENERATORS FROM THE SEED:
#
#     seed --(algebraic hash)--> x-candidates
#          --(Legendre select via in-circuit exponentiation)--> curve x
#          --(constant-time Tonelli-Shanks sqrt, in-circuit)--> curve point
#          --(k-round fold, double-and-add with PUBLIC challenge bits,
#             complete Renes-Costello-Batina point formulas)--> Q
#
# The circuit input is ONLY (seed, IPA challenges): the verifier's terminal
# input-MLE check is a closed form of O(log n) size.  This is the Genesis
# endpoint (Lean: `genesis_reduction`, `double_and_add_step`,
# `square_and_multiply_step`, `sqrt_exp_correct`; spec: solutions/2-genesis.md).
#
# Pasta makes the two-field problem dissolve for the fold: each fold layer
# multiplies by ONE public scalar (an IPA challenge or its inverse), so its
# bits are public layer structure — no non-native arithmetic in the circuit.
#
# Honest demo notes:
#   * the hash is a toy algebraic sponge (x^5 rounds), not Poseidon;
#   * hash-to-curve uses a 4-candidate Legendre window; the setup retries the
#     seed until every index has a valid candidate (a production system uses
#     iso-SWU); the Legendre tests and the sqrt run IN-CIRCUIT;
#   * proof size / verifier time are dominated by lambda = 255 (bit-length),
#     not by n: the verifier scales polylog in n but the constants are those
#     of an unoptimized single-threaded Sage GKR.  At demo sizes the naive
#     verifier is faster in absolute terms — the demo shows the architecture
#     and the asymptotics, not a competitive implementation.
#
# Run:  sage sage/3-genesis-e2e.sage
import hashlib, time

# ============================================================ Pallas
p = 28948022309329048855892746252171976963363056481941560715954676764349967630337
q = 28948022309329048855892746252171976963363056481941647379679742748393362948097
Fp = GF(p)          # base field  (circuit / GKR field)
Fq = GF(q)          # scalar field (IPA field)
E  = EllipticCurve(Fp, [0, 5])
INF = E(0)
B3 = Fp(15)         # 3*b for RCB formulas

S2AD = 32                                    # 2-adicity of p-1
M_ODD = (p - 1) >> S2AD                      # odd part m
QNR = Fp(5)                                  # deterministic non-residue
ZGEN = QNR**M_ODD                            # generator of the 2-Sylow, order 2^32
ZPOW = [ZGEN**(2**j) for j in range(S2AD)]   # ZPOW[j] = z^(2^j)
INV2 = Fp(1) / 2
E1BITS_EXP = (M_ODD + 1) // 2                # exponent for v = g^((m+1)/2)
E2BITS_EXP = M_ODD                           # exponent for w = g^m
NROUNDS = 8
RC = [Fp(int(hashlib.sha256(f"genesis-rc|{t}".encode()).hexdigest(), 16))
      for t in range(NROUNDS)]

def bits_msb(x, width):
    return [int(c) for c in Integer(x).binary().zfill(width)]

E1BITS = bits_msb(E1BITS_EXP, 224)
E2BITS = bits_msb(E2BITS_EXP, 224)

# ============================================================ transcript
class Transcript:
    def __init__(self, label):
        self.h = hashlib.sha256(label.encode()).digest()
    def absorb(self, label, obj):
        self.h = hashlib.sha256(self.h + label.encode() + b"|" +
                                repr(obj).encode()).digest()
    def absorb_point(self, label, P):
        self.absorb(label, "INF" if P == INF else (int(P[0]), int(P[1])))
    def _chal(self, label, F):
        while True:
            self.h = hashlib.sha256(self.h + label.encode()).digest()
            x = F(int.from_bytes(self.h, "big"))
            if x != 0:
                return x
    def chal_q(self, label): return self._chal(label, Fq)
    def chal_p(self, label): return self._chal(label, Fp)

# ============================================================ native primitives
def rcb_add(X1, Y1, Z1, X2, Y2, Z2):
    """Complete projective addition, a=0, b3=15 (RCB'15 Alg. 7). Ring-generic."""
    t0 = X1*X2; t1 = Y1*Y2; t2 = Z1*Z2
    t3 = X1+Y1; t4 = X2+Y2; t3 = t3*t4
    t4 = t0+t1; t3 = t3-t4; t4 = Y1+Z1
    X3 = Y2+Z2; t4 = t4*X3; X3 = t1+t2
    t4 = t4-X3; X3 = X1+Z1; Y3 = X2+Z2
    X3 = X3*Y3; Y3 = t0+t2; Y3 = X3-Y3
    X3 = t0+t0; t0 = X3+t0; t2 = B3*t2
    Z3 = t1+t2; t1 = t1-t2; Y3 = B3*Y3
    X3 = t4*Y3; t2 = t3*t1; X3 = t2-X3
    Y3 = Y3*t0; t1 = t1*Z3; Y3 = t1+Y3
    t0 = t0*t3; Z3 = Z3*t4; Z3 = Z3+t0
    return X3, Y3, Z3

def from_proj(X, Y, Z):
    return INF if Z == 0 else E(X / Z, Y / Z)

def toy_hash(h):
    for t in range(NROUNDS):
        u = h + RC[t]
        h = u**5
    return h

def derive_native(seed_fe, i):
    """Reference derivation — must match the circuit gate-for-gate."""
    h = toy_hash(seed_fe + i)
    cands = [h + c for c in range(4)]
    gs = [x**3 + 5 for x in cands]
    vs = [g**E1BITS_EXP for g in gs]         # g^((m+1)/2)
    ws = [g**E2BITS_EXP for g in gs]         # g^m
    ls = [w**(2**(S2AD - 1)) for w in ws]    # Legendre symbol = w^(2^31)
    qs = [(1 + l) * INV2 for l in ls]
    sels, acc = [], Fp(1)
    for c in range(4):
        sels.append(qs[c] * acc); acc *= (1 - qs[c])
    if sum(sels) != 1:
        return None                          # no QR candidate: reject seed
    x = sum(sels[c] * cands[c] for c in range(4))
    v = sum(sels[c] * vs[c] for c in range(4))
    w = sum(sels[c] * ws[c] for c in range(4))
    for K in range(S2AD - 1, 0, -1):         # constant-time Tonelli-Shanks
        t = w**(2**(K - 1))
        b = (1 - t) * INV2
        w = w * (1 + b * (ZPOW[S2AD - K] - 1))
        v = v * (1 + b * (ZPOW[S2AD - 1 - K] - 1))
    assert v * v == x**3 + 5
    return (x, v)

def setup(seed_str, n):
    """Transparent setup = publish a seed (retried so every index derives)."""
    ctr = 0
    while True:
        seed_fe = Fp(int(hashlib.sha256(f"{seed_str}|{ctr}".encode())
                         .hexdigest(), 16))
        pts = [derive_native(seed_fe, i) for i in range(n)]
        U = derive_native(seed_fe, n)
        if all(pt is not None for pt in pts) and U is not None:
            G = [E(x, y) for (x, y) in pts]
            return seed_fe, G, E(U[0], U[1])
        ctr += 1

def msm(scalars, points):
    acc = INF
    for s, P in zip(scalars, points):
        acc += int(s) * P
    return acc

def inner(u, v):
    return sum((a * b for a, b in zip(u, v)), Fq(0))

# ============================================================ IPA (Bulletproofs)
def ipa_prove(tr, G, U, a, b):
    a, b, Gv = list(a), list(b), list(G)
    Ls, Rs, xs = [], [], []
    while len(a) > 1:
        m = len(a) // 2
        aL, aH = a[:m], a[m:]; bL, bH = b[:m], b[m:]
        GL, GH = Gv[:m], Gv[m:]
        L = msm(aL, GH) + int(inner(aL, bH)) * U
        R = msm(aH, GL) + int(inner(aH, bL)) * U
        tr.absorb_point("L", L); tr.absorb_point("R", R)
        x = tr.chal_q("x"); xi = x**-1
        a  = [x * aL[i] + xi * aH[i] for i in range(m)]
        b  = [xi * bL[i] + x * bH[i] for i in range(m)]
        Gv = [int(xi) * GL[i] + int(x) * GH[i] for i in range(m)]
        Ls.append(L); Rs.append(R); xs.append(x)
    return Ls, Rs, xs, a[0]

def s_vector(xs, k):
    n = 1 << k
    s = []
    for i in range(n):
        acc = Fq(1)
        for j in range(k):
            acc *= xs[j] if (i >> (k - 1 - j)) & 1 else xs[j]**-1
        s.append(acc)
    return s

# ============================================================ GKR engine
def eq_array(pt):
    # pt[0] is the MSB: each concatenation makes the processed coordinate the
    # new top bit, so process in reverse to leave pt[0] on top.
    arr = [Fp(1)]
    for c in reversed(pt):
        arr = [a * (1 - c) for a in arr] + [a * c for a in arr]
    return arr

def eq_point(pt, r):
    v = Fp(1)
    for c, y in zip(pt, r):
        v *= c * y + (1 - c) * (1 - y)
    return v

def fold_at(arr, e):
    m = len(arr) // 2
    if e == 0: return arr[:m]
    if e == 1: return arr[m:]
    return [arr[i] + e * (arr[m + i] - arr[i]) for i in range(m)]

def interp(vals, r):
    D = len(vals) - 1
    tot = Fp(0)
    for j in range(D + 1):
        num, den = Fp(1), Fp(1)
        for l in range(D + 1):
            if l != j:
                num *= r - l; den *= Fp(j - l)
        tot += vals[j] * num / den
    return tot

class Builder:
    """Builds the layered circuit; with arrays (prover) or specs only (verifier).
    A boundary is a set of named columns of length 2^nv.  Steps:
      simd : every output column is f(deps at same index) of the previous
             boundary — the wiring is the identity, so the sumcheck kernel
             is a plain eq and the verifier evaluates everything in O(1).
      split: halve nv, mapping out -> (src, msb_bit); claim transfer only."""
    def __init__(self, nv, inputs, prover):
        self.nv = nv; self.prover = prover
        self.cur = dict(inputs)
        self.steps = []
    def simd(self, outs):
        # outs: list of (name, deps, f, deg)
        step = {"kind": "simd", "nv": self.nv, "outs": outs}
        if self.prover:
            alldeps = sorted({d for (_, deps, _, _) in outs for d in deps})
            step["in_arrays"] = {d: self.cur[d] for d in alldeps}
            n = 1 << self.nv
            new = {}
            for (nm, deps, f, dg) in outs:
                new[nm] = [f({d: self.cur[d][i] for d in deps})
                           for i in range(n)]
            self.cur = new
        else:
            self.cur = {nm: None for (nm, _, _, _) in outs}
        self.steps.append(step)
    def split(self, mapping):
        step = {"kind": "split", "map": mapping}
        if self.prover:
            m = 1 << (self.nv - 1)
            new = {}
            for out, (src, bit) in mapping.items():
                arr = self.cur[src]
                new[out] = arr[m:] if bit else arr[:m]
            self.cur = new
        else:
            self.cur = {out: None for out in mapping}
        self.nv -= 1
        self.steps.append(step)

def ident(name):
    return (name, [name], (lambda d, _n=name: d[_n]), 1)

def gkr_prove(steps, out_claims, tr, debug=False):
    claims = {c: list(v) for c, v in out_claims.items()}
    proof = []
    widx = -1
    for step in reversed(steps):
        widx += 1
        if step["kind"] == "split":
            new = {}
            for out, (src, bit) in step["map"].items():
                for (pt, val) in claims.get(out, []):
                    new.setdefault(src, []).append(((Fp(bit),) + pt, val))
            claims = new
            proof.append(None)
            continue
        nv = step["nv"]; n = 1 << nv
        outs = [o for o in step["outs"] if claims.get(o[0])]
        tr.absorb("cl", [(nm, [int(v) for (_, v) in claims[nm]])
                         for (nm, _, _, _) in outs])
        rho = tr.chal_p("rho")
        weights, wacc, combined = [], Fp(1), Fp(0)
        for (nm, deps, f, dg) in outs:
            for (pt, val) in claims[nm]:
                weights.append((nm, pt, wacc))
                combined += wacc * val
                wacc *= rho
        alldeps = sorted({d for (_, deps, _, _) in outs for d in deps})
        arrs = {d: list(step["in_arrays"][d]) for d in alldeps}
        kern = {nm: [Fp(0)] * n for (nm, _, _, _) in outs}
        for (nm, pt, w) in weights:
            ea = eq_array(pt)
            K = kern[nm]
            for i in range(n):
                K[i] += w * ea[i]
        if debug:
            tot = Fp(0)
            for i in range(n):
                vals = {d: arrs[d][i] for d in alldeps}
                for (nm, deps, f, dg) in outs:
                    tot += kern[nm][i] * f(vals)
            assert tot == combined, (
                f"witness/claim mismatch @walk={widx} nv={nv} "
                f"outs={[nm for (nm, _, _, _) in outs]} "
                f"claims={{ {', '.join(f'{nm}:{len(claims[nm])}' for (nm, _, _, _) in outs)} }} "
                f"dropped={[c for c in claims if c not in {o[0] for o in step['outs']}]}")
        D = 1 + max(dg for (_, _, _, dg) in outs)
        polys, rvec = [], []
        for _ in range(nv):
            Svals = []
            for e in range(D + 1):
                fa = {d: fold_at(arrs[d], e) for d in alldeps}
                fk = {nm: fold_at(kern[nm], e) for (nm, _, _, _) in outs}
                m = len(fa[alldeps[0]]) if alldeps else len(fk[outs[0][0]])
                tot = Fp(0)
                for i in range(m):
                    vals = {d: fa[d][i] for d in alldeps}
                    for (nm, deps, f, dg) in outs:
                        tot += fk[nm][i] * f(vals)
                Svals.append(tot)
            tr.absorb("poly", [int(x) for x in Svals])
            r = tr.chal_p("r")
            rvec.append(r)
            arrs = {d: fold_at(arrs[d], r) for d in alldeps}
            kern = {nm: fold_at(kern[nm], r) for (nm, _, _, _) in outs}
            polys.append(Svals)
        finals = {d: arrs[d][0] for d in alldeps}
        tr.absorb("fin", sorted((d, int(v)) for d, v in finals.items()))
        proof.append({"polys": polys, "finals": finals})
        rpt = tuple(rvec)
        claims = {d: [(rpt, finals[d])] for d in alldeps}
    return proof, claims

def gkr_verify(steps, out_claims, proof, tr):
    claims = {c: list(v) for c, v in out_claims.items()}
    pi = 0
    ops = 0
    widx = -1
    for step in reversed(steps):
        widx += 1
        entry = proof[pi]; pi += 1
        if step["kind"] == "split":
            new = {}
            for out, (src, bit) in step["map"].items():
                for (pt, val) in claims.get(out, []):
                    new.setdefault(src, []).append(((Fp(bit),) + pt, val))
            claims = new
            continue
        nv = step["nv"]
        outs = [o for o in step["outs"] if claims.get(o[0])]
        tr.absorb("cl", [(nm, [int(v) for (_, v) in claims[nm]])
                         for (nm, _, _, _) in outs])
        rho = tr.chal_p("rho")
        weights, wacc, claim = [], Fp(1), Fp(0)
        for (nm, deps, f, dg) in outs:
            for (pt, val) in claims[nm]:
                weights.append((nm, pt, wacc))
                claim += wacc * val
                wacc *= rho
        D = 1 + max(dg for (_, _, _, dg) in outs)
        rvec = []
        for polys in entry["polys"]:
            if polys[0] + polys[1] != claim:
                return False, ops, f"round check failed @walk={widx}"
            tr.absorb("poly", [int(x) for x in polys])
            r = tr.chal_p("r")
            rvec.append(r)
            claim = interp(polys, r)
            ops += (D + 1)**2
        finals = entry["finals"]
        tr.absorb("fin", sorted((d, int(v)) for d, v in finals.items()))
        rpt = tuple(rvec)
        tot = Fp(0)
        for (nm, deps, f, dg) in outs:
            K = Fp(0)
            for (nm2, pt, w) in weights:
                if nm2 == nm:
                    K += w * eq_point(pt, rpt)
                    ops += nv
            tot += K * f(finals)
            ops += 10
        if tot != claim:
            return False, ops, f"final layer check failed @walk={widx}"
        claims = {d: [(rpt, finals[d])] for d in sorted(finals)}
    return claims, ops, "ok"

# ============================================================ the Genesis circuit
def rcb_fs(pref_a, pref_b):
    """The three RCB output coordinates as f's over named columns."""
    def mk(idx):
        def f(d, pa=pref_a, pb=pref_b, ix=idx):
            return rcb_add(d[pa + "X"], d[pa + "Y"], d[pa + "Z"],
                           d[pb + "X"], d[pb + "Y"], d[pb + "Z"])[ix]
        return f
    return mk(0), mk(1), mk(2)

def build_circuit(k, seed_fe, xs, prover):
    """The full delegated computation: seed -> generators -> Q = <s,G>.
    Input boundary: single column h0 with closed form seed + index."""
    nv = k; n = 1 << k
    if prover:
        inputs = {"h0": [seed_fe + i for i in range(n)]}
    else:
        inputs = {"h0": None}
    B = Builder(nv, inputs, prover)

    # ---- stage 1: toy hash -------------------------------------------------
    h = "h0"
    for t in range(NROUNDS):
        rc = RC[t]
        B.simd([("u2", [h], (lambda d, _h=h, _rc=rc: (d[_h] + _rc)**2), 2),
                ident(h)])
        B.simd([("u4", ["u2"], (lambda d: d["u2"]**2), 2), ident(h)])
        B.simd([("h", ["u4", h],
                 (lambda d, _h=h, _rc=rc: d["u4"] * (d[_h] + _rc)), 2)])
        h = "h"

    # ---- stage 2: candidates and g_c = x_c^3 + 5 ---------------------------
    B.simd([(f"sq{c}", ["h"], (lambda d, _c=c: (d["h"] + _c)**2), 2)
            for c in range(4)] + [ident("h")])
    B.simd([(f"g{c}", [f"sq{c}", "h"],
             (lambda d, _c=c: d[f"sq{_c}"] * (d["h"] + _c) + 5), 2)
            for c in range(4)] + [ident("h")])

    # ---- stage 3: exponent chains v_c = g^((m+1)/2), w_c = g^m -------------
    B.simd([(f"v{c}", [], (lambda d: Fp(1)), 0) for c in range(4)] +
           [(f"w{c}", [], (lambda d: Fp(1)), 0) for c in range(4)] +
           [ident(f"g{c}") for c in range(4)] + [ident("h")])
    carry = [ident(f"g{c}") for c in range(4)] + [ident("h")]
    for t in range(224):
        B.simd([(f"v{c}", [f"v{c}"], (lambda d, _c=c: d[f"v{_c}"]**2), 2)
                for c in range(4)] +
               [(f"w{c}", [f"w{c}"], (lambda d, _c=c: d[f"w{_c}"]**2), 2)
                for c in range(4)] + carry)
        if E1BITS[t] or E2BITS[t]:
            outs = []
            for c in range(4):
                if E1BITS[t]:
                    outs.append((f"v{c}", [f"v{c}", f"g{c}"],
                                 (lambda d, _c=c: d[f"v{_c}"] * d[f"g{_c}"]), 2))
                else:
                    outs.append(ident(f"v{c}"))
                if E2BITS[t]:
                    outs.append((f"w{c}", [f"w{c}", f"g{c}"],
                                 (lambda d, _c=c: d[f"w{_c}"] * d[f"g{_c}"]), 2))
                else:
                    outs.append(ident(f"w{c}"))
            B.simd(outs + carry)

    # ---- stage 4: Legendre symbols l_c = w_c^(2^31) ------------------------
    carry2 = ([ident(f"v{c}") for c in range(4)] +
              [ident(f"w{c}") for c in range(4)] + [ident("h")])
    B.simd([(f"l{c}", [f"w{c}"], (lambda d, _c=c: d[f"w{_c}"]**2), 2)
            for c in range(4)] + carry2)
    for _ in range(S2AD - 2):
        B.simd([(f"l{c}", [f"l{c}"], (lambda d, _c=c: d[f"l{_c}"]**2), 2)
                for c in range(4)] + carry2)

    # ---- stage 5: select first QR candidate --------------------------------
    def qf(l): return (1 + l) * INV2
    sel_fs = [
        ("s0", ["l0"], (lambda d: qf(d["l0"])), 1),
        ("s1", ["l0", "l1"],
         (lambda d: qf(d["l1"]) * (1 - qf(d["l0"]))), 2),
        ("s2", ["l0", "l1", "l2"],
         (lambda d: qf(d["l2"]) * (1 - qf(d["l1"])) * (1 - qf(d["l0"]))), 3),
        ("s3", ["l0", "l1", "l2", "l3"],
         (lambda d: qf(d["l3"]) * (1 - qf(d["l2"])) * (1 - qf(d["l1"]))
                    * (1 - qf(d["l0"]))), 4),
    ]
    B.simd(sel_fs + carry2)
    B.simd([("xs", [f"s{c}" for c in range(4)] + ["h"],
             (lambda d: sum(d[f"s{c}"] * (d["h"] + c) for c in range(4))), 2),
            ("vv", [f"s{c}" for c in range(4)] + [f"v{c}" for c in range(4)],
             (lambda d: sum(d[f"s{c}"] * d[f"v{c}"] for c in range(4))), 2),
            ("ww", [f"s{c}" for c in range(4)] + [f"w{c}" for c in range(4)],
             (lambda d: sum(d[f"s{c}"] * d[f"w{c}"] for c in range(4))), 2)])

    # ---- stage 6: constant-time Tonelli-Shanks sqrt ------------------------
    for K in range(S2AD - 1, 0, -1):
        if K > 1:
            B.simd([("t", ["ww"], (lambda d: d["ww"]**2), 2),
                    ident("ww"), ident("vv"), ident("xs")])
            for _ in range(K - 2):
                B.simd([("t", ["t"], (lambda d: d["t"]**2), 2),
                        ident("ww"), ident("vv"), ident("xs")])
            tdep = "t"
        else:
            tdep = "ww"
        z1, z2 = ZPOW[S2AD - K], ZPOW[S2AD - 1 - K]
        B.simd([("ww", ["ww", tdep],
                 (lambda d, _t=tdep, _z=z1:
                  d["ww"] * (1 + (1 - d[_t]) * INV2 * (_z - 1))), 2),
                ("vv", ["vv", tdep],
                 (lambda d, _t=tdep, _z=z2:
                  d["vv"] * (1 + (1 - d[_t]) * INV2 * (_z - 1))), 2),
                ident("xs")])

    # ---- stage 7: to projective; k rounds of the IPA generator fold --------
    B.simd([("X", ["xs"], (lambda d: d["xs"]), 1),
            ("Y", ["vv"], (lambda d: d["vv"]), 1),
            ("Z", [], (lambda d: Fp(1)), 0)])
    for j in range(k):
        sA = int(xs[j]**-1)      # scalar for the low half
        sB = int(xs[j])          # scalar for the high half
        B.split({"AX": ("X", 0), "AY": ("Y", 0), "AZ": ("Z", 0),
                 "BX": ("X", 1), "BY": ("Y", 1), "BZ": ("Z", 1)})
        base_carry = [ident(c + a) for c in "AB" for a in "XYZ"]
        B.simd([("PAX", [], (lambda d: Fp(0)), 0),
                ("PAY", [], (lambda d: Fp(1)), 0),
                ("PAZ", [], (lambda d: Fp(0)), 0),
                ("PBX", [], (lambda d: Fp(0)), 0),
                ("PBY", [], (lambda d: Fp(1)), 0),
                ("PBZ", [], (lambda d: Fp(0)), 0)] + base_carry)
        bA, bB = bits_msb(sA, 255), bits_msb(sB, 255)
        dblA = rcb_fs("PA", "PA"); dblB = rcb_fs("PB", "PB")
        addA = rcb_fs("PA", "A");  addB = rcb_fs("PB", "B")
        pa_deps = ["PAX", "PAY", "PAZ"]; pb_deps = ["PBX", "PBY", "PBZ"]
        a_deps = pa_deps + ["AX", "AY", "AZ"]
        b_deps = pb_deps + ["BX", "BY", "BZ"]
        for t in range(255):
            B.simd([("PAX", pa_deps, dblA[0], 4),
                    ("PAY", pa_deps, dblA[1], 4),
                    ("PAZ", pa_deps, dblA[2], 4),
                    ("PBX", pb_deps, dblB[0], 4),
                    ("PBY", pb_deps, dblB[1], 4),
                    ("PBZ", pb_deps, dblB[2], 4)] + base_carry)
            if bA[t] or bB[t]:
                outs = []
                if bA[t]:
                    outs += [("PAX", a_deps, addA[0], 4),
                             ("PAY", a_deps, addA[1], 4),
                             ("PAZ", a_deps, addA[2], 4)]
                else:
                    outs += [ident("PAX"), ident("PAY"), ident("PAZ")]
                if bB[t]:
                    outs += [("PBX", b_deps, addB[0], 4),
                             ("PBY", b_deps, addB[1], 4),
                             ("PBZ", b_deps, addB[2], 4)]
                else:
                    outs += [ident("PBX"), ident("PBY"), ident("PBZ")]
                B.simd(outs + base_carry)
        comb = rcb_fs("PA", "PB")
        cdeps = pa_deps + pb_deps
        B.simd([("X", cdeps, comb[0], 4),
                ("Y", cdeps, comb[1], 4),
                ("Z", cdeps, comb[2], 4)])
    return B

def input_closed_form(seed_fe, nv, pt):
    """MLE of h0[i] = seed + i at pt (MSB-first) — the Genesis input check."""
    idx = Fp(0)
    for t, c in enumerate(pt):
        idx += c * 2**(nv - 1 - t)
    return seed_fe + idx

# ============================================================ protocol
def prove(seed_fe, G, U, a, z, k, quiet=False):
    n = 1 << k
    b = [z**i for i in range(n)]
    v = inner(a, b)
    C = msm(a, G)
    tr = Transcript("genesis-e2e")
    tr.absorb("seed", int(seed_fe)); tr.absorb_point("C", C)
    tr.absorb("z", int(z)); tr.absorb("v", int(v))
    Ls, Rs, xs, a_final = ipa_prove(tr, G, U, a, b)

    # deferred claim Q = <s, G>, certified by the circuit
    s = s_vector(xs, k)
    Q = msm(s, G)
    t0 = time.time()
    B = build_circuit(k, seed_fe, xs, prover=True)
    QX, QY, QZ = B.cur["X"][0], B.cur["Y"][0], B.cur["Z"][0]
    assert from_proj(QX, QY, QZ) == Q, "circuit output != <s,G>"
    if not quiet:
        print(f"          circuit: {len(B.steps)} layers; witness "
              f"built+checked ({time.time()-t0:.1f}s)")
    tr.absorb("Qproj", (int(QX), int(QY), int(QZ)))
    out_claims = {"X": [((), QX)], "Y": [((), QY)], "Z": [((), QZ)]}
    t0 = time.time()
    gkr, in_claims = gkr_prove(B.steps, out_claims, tr, debug=False)
    for (pt, val) in in_claims["h0"]:
        assert val == input_closed_form(seed_fe, k, pt)
    if not quiet:
        print(f"          delegation certificate built ({time.time()-t0:.1f}s)")
    return {"C": C, "v": v, "Ls": Ls, "Rs": Rs, "a_final": a_final,
            "Qproj": (QX, QY, QZ), "gkr": gkr, "layers": len(B.steps)}

def verify(seed_fe, U, z, proof, k):
    """Verifier: NEVER touches the n generators.  Work = O(log n) group ops
    (IPA) + O(lambda * log n) field ops (certificate walk) + O(log n) input
    closed form.  U is re-derived from the seed: O(1)."""
    C, v = proof["C"], proof["v"]
    Ls, Rs, a_f = proof["Ls"], proof["Rs"], proof["a_final"]
    QX, QY, QZ = proof["Qproj"]
    tr = Transcript("genesis-e2e")
    tr.absorb("seed", int(seed_fe)); tr.absorb_point("C", C)
    tr.absorb("z", int(z)); tr.absorb("v", int(v))

    xs = []
    P0 = C + int(v) * U
    for L, R in zip(Ls, Rs):
        tr.absorb_point("L", L); tr.absorb_point("R", R)
        x = tr.chal_q("x"); xs.append(x)
        P0 += int(x**2) * L + int(x**-2) * R

    b0 = Fq(1)
    for j in range(k):
        b0 *= xs[j]**-1 + xs[j] * z**(2**(k - 1 - j))

    if QZ == 0:
        return False, "Z = 0"
    if QY**2 * QZ != QX**3 + 5 * QZ**3:
        return False, "Q not on curve"
    Q = from_proj(QX, QY, QZ)
    if P0 != int(a_f) * Q + int(a_f * b0) * U:
        return False, "final IPA equation failed"

    tr.absorb("Qproj", (int(QX), int(QY), int(QZ)))
    B = build_circuit(k, seed_fe, xs, prover=False)
    out_claims = {"X": [((), QX)], "Y": [((), QY)], "Z": [((), QZ)]}
    res, ops, msg = gkr_verify(B.steps, out_claims, proof["gkr"], tr)
    if res is False:
        return False, f"certificate: {msg}"
    for col, cl in res.items():
        if col != "h0":
            return False, "unexpected input column"
        for (pt, val) in cl:
            if val != input_closed_form(seed_fe, k, pt):
                return False, "input closed-form check failed"
    return True, f"ok ({ops} certificate field ops)"

# ============================================================ demo
def main():
    set_random_seed(42)
    k = 2; n = 1 << k
    print(f"=== Genesis end-to-end on Pallas ===  n = {n} (k = {k})")
    print("[setup]   searching seed (transparent: setup = the seed itself)")
    seed_fe, G, U = setup("genesis-e2e-demo", n)
    print(f"          seed = {int(seed_fe) % 10**12}... "
          f"(generators derived, never sent to verifier)")

    a = [Fq.random_element() for _ in range(n)]
    z = Fq.random_element()
    print("[prove]   IPA + full delegation certificate "
          "(derivation + fold circuits)")
    t0 = time.time()
    proof = prove(seed_fe, G, U, a, z, k)
    tprove = time.time() - t0

    ngkr = sum(sum(len(P) for P in e["polys"]) + len(e["finals"])
               for e in proof["gkr"] if e)
    print(f"          proof: {2*len(proof['Ls'])} IPA group elts + "
          f"{ngkr} certificate field elts   (prover {tprove:.1f}s)")

    print("[verify]  ", end="")
    t0 = time.time()
    ok, msg = verify(seed_fe, U, z, proof, k)
    tver = time.time() - t0
    print(("ACCEPT" if ok else "REJECT") + f"  ({msg}, {tver:.1f}s)")
    assert ok
    print("          verifier work: O(log n) group ops + O(lambda*log n) "
          "field ops -- INDEPENDENT of which/how-many generators")

    print("[tamper]  wrong Q (off-curve coords)    -> ", end="")
    bad = dict(proof)
    bad["Qproj"] = (proof["Qproj"][0] + 1, proof["Qproj"][1], proof["Qproj"][2])
    ok, msg = verify(seed_fe, U, z, bad, k)
    print(f"REJECT ({msg})" if not ok else "ACCEPT (!!)")
    assert not ok

    print("[tamper]  wrong Q (on-curve, Q' = 2Q)   -> ", end="")
    bad = dict(proof)
    Qpt = from_proj(*proof["Qproj"])
    Q2 = 2 * Qpt
    bad["Qproj"] = (Q2[0], Q2[1], Fp(1))
    ok, msg = verify(seed_fe, U, z, bad, k)
    print(f"REJECT ({msg})" if not ok else "ACCEPT (!!)")
    assert not ok

    print("[tamper]  corrupted certificate poly    -> ", end="")
    bad = dict(proof)
    gk = [dict(e) if e else None for e in proof["gkr"]]
    for e in gk:                    # tamper the first verified step

        if e:
            e["polys"] = [[x + 1 for x in e["polys"][0]]] + e["polys"][1:] \
                         if e["polys"] else e["polys"]
            if not e["polys"]:
                e["finals"] = {d: v + 1 for d, v in e["finals"].items()}
            break
    bad["gkr"] = gk
    ok, msg = verify(seed_fe, U, z, bad, k)
    print(f"REJECT ({msg})" if not ok else "ACCEPT (!!)")
    assert not ok

    print("[tamper]  wrong evaluation value v      -> ", end="")
    bad = dict(proof); bad["v"] = proof["v"] + 1
    ok, msg = verify(seed_fe, U, z, bad, k)
    print(f"REJECT ({msg})" if not ok else "ACCEPT (!!)")
    assert not ok

    print("=== end-to-end Genesis: all checks passed ===")

    # scaling: verifier cost is lambda-dominated and ~flat in n
    print("\n=== scaling (honest run per size) ===")
    print(f"      {'n':>4}  {'layers':>7}  {'cert elts':>10}  "
          f"{'prover(s)':>9}  {'verify(s)':>9}")
    for kk in (2, 3):
        nn = 1 << kk
        seed2, G2, U2 = setup("genesis-e2e-demo", nn)
        a2 = [Fq.random_element() for _ in range(nn)]
        z2 = Fq.random_element()
        t0 = time.time(); pr = prove(seed2, G2, U2, a2, z2, kk, quiet=True)
        tp = time.time() - t0
        t0 = time.time(); ok2, _ = verify(seed2, U2, z2, pr, kk)
        tv = time.time() - t0
        assert ok2
        nl = pr["layers"]
        ne = sum(sum(len(P) for P in e["polys"]) + len(e["finals"])
                 for e in pr["gkr"] if e)
        print(f"      {nn:>4}  {nl:>7}  {ne:>10}  {tp:>9.1f}  {tv:>9.1f}")
    print("      (verifier scales with lambda*log n, NOT with n; the naive")
    print("       Bulletproofs verifier is Theta(n) group ops)")
    print("    demo notes: toy hash, 4-candidate Legendre window, lambda=255")
    print("    grind; the architecture is the point -- verifier input is the")
    print("    seed + challenges only, generators never leave the prover")

main()
