# Prism — Succinct dlog IPA by folding a Reed–Solomon encoding of the generators

*Successor to Genesis (`2-genesis.md`). Named for how it works: the generators are refracted once into their Reed–Solomon **spectrum** (a codeword), and the verifier's linear MSM is discharged by **folding that spectrum down** — FRI/BaseFold, run natively over the group. Genesis grew `G` from a seed inside a delegated circuit; Prism never puts a circuit around curve arithmetic at all. This is the Eagen–Gabizon "group variant of BaseFold" (ePrint 2025/1325, Thm 4.4 / §5–§7) instantiated in this repo's single-proof, preprocessing-allowed setting, where it strictly dominates Genesis.*

**Abstract.** Same target as Atlas and Genesis: a polynomial commitment over an ordinary prime-order group with $\mathrm{polylog}(n)$ proof and *online* verifier — **no pairing, no unknown-order group, no recursion**. The change from Genesis: instead of *delegating* the folded-generator MSM $G_0 = \langle \mathbf{s}, \mathbf{G}\rangle$ to a GKR circuit that re-derives $\mathbf{G}$ and does curve arithmetic in-circuit, we recognize $G_0$ as a *multilinear evaluation of the fixed generator polynomial* (`genFinal_eq_mle`) and prove that evaluation directly with a **group-valued BaseFold**: a sumcheck interleaved with an FRI-style proximity test over the "group Reed–Solomon code" $\mathsf{RS}_0(\mathbf{G})$. Setup is a one-time, transparent, near-linear RS encoding of the (public) generators — no galactic Kedlaya–Umans table (Atlas), no in-circuit hash-to-curve and no two-field problem (Genesis). Every component is fully analyzed in 2025/1325; nothing is left as "unwritten composition."

## The one idea

Genesis and Atlas both attack the *same* object — the terminal evaluation this repo already isolated:

$$G_0 = \langle \mathbf{s}, \mathbf{G}\rangle = \Big(\textstyle\prod_j x_j^{-1}\Big)\cdot \mathsf{MLE}_{\mathbf G}(x_1^2,\dots,x_k^2) \qquad (\texttt{genFinal\_eq\_mle}).$$

The MSM *is* a multilinear evaluation of the public generator tensor. The three solutions differ only in **how the terminal generator-MLE evaluation is discharged**:

| | discharge of $\mathsf{MLE}_{\mathbf G}$ | cost / footprint |
|---|---|---|
| **Atlas** | Kedlaya–Umans preprocessed evaluation | $n^{1+\varepsilon}$ table, *galactic* constants |
| **Genesis** | re-derive $\mathbf G$ from seed inside a GKR circuit | $10^2$–$10^3\times$ MSM prover, **two-field problem** |
| **Prism** | **fold a Reed–Solomon encoding of $\mathbf G$ (BaseFold/FRI over $\mathbb G$)** | $O(n)$-smul prover, small constants, **fully proven** |

> **Encode the generators once; prove $\mathsf{MLE}_{\mathbf G}(r)$ by folding the encoding.** The IPA opening is reduced by a *sumcheck argument* to a single claim $G(r)=W$ about the fixed generator polynomial; that claim is decided by a group-native BaseFold against a preprocessed codeword $g_0 = \mathsf{RS}_0(\mathbf G)$. The verifier never re-runs curve arithmetic and never views $\mathbf G$ except through a binding commitment to its codeword.

This does not contradict the digest lower bound (`no_lossy_digest_verifier`). That bound kills a verifier whose entire view of $\mathbf G$ is a **linear, lossy** digest $D\mathbf G$ and whose verdict is a *fixed function* of it. Prism's verifier is **prover-aided** (the "add prover help" escape named in `LowerBound.lean` itself): it runs an interactive FRI argument in which the prover opens the codeword at random points. And the commitment it holds is a *binding, non-linear* Merkle root of $\mathsf{RS}_0(\mathbf G)$ — injective in $\mathbf G$, hence not lossy, and not linear. Neither hypothesis of the lower bound is met.

## What runs (all native group / field operations — no circuit around a curve)

| Stage | Realization | Cost | Repo / paper anchor |
|---|---|---|---|
| Opening → single MLE claim | **sumcheck argument** on $A(\mathbf X)=\hat f(\mathbf X)G(\mathbf X)+\mathbf{eq}(\mathbf X,z)\hat f(\mathbf X)P'$, degree 2 | $2k$ verifier smul; $3k\,\mathbb G+1\,\mathbb F$ proof | 2025/1325 §5 (Thm 5.1); engine: `sum_split`, `msm_split`, `sumcheck_round_complete` |
| Preprocess generators | $g_0=\mathsf{RS}_0(\mathbf G)$: evaluate $f_0(X)=\sum_j G_j P_j(X)$ on $D_0$, Merkle-commit | one-time $\tilde O(n)$, transparent | 2025/1325 §7.1 (encoding chosen so *folding = multilinear eval*: $f_k\equiv\hat G(r)$) |
| Decide the MLE claim | **BaseFold over $\mathbb G$**: interleave a sumcheck on $G(\mathbf X)\mathbf{eq}(r,\mathbf X)$ with FRI folding $g_i=\mathsf{fold}_{r_i}(g_{i-1})$ + $\ell=O(\lambda)$ consistency queries | $O(\lambda k)$ verifier smul, $O(\lambda k^2)$ RO; $O(\lambda k^2)$-hash proof | 2025/1325 §7.2 (Thm 7.3, RBR soundness); proximity: Lemma 7.2 over $\mathbb G$ |
| FS compilation | Merkle + Fiat–Shamir, IOP → ROM argument | — | 2025/1325 Thm 2.3 (BCS16); same ROM Genesis already needs |

## Protocol

**Setup (transparent, one-time preprocessing).** Publish $\mathsf{seed}$. Define $\mathbf G=(\mathsf{H2C}(\mathsf{seed},i))_{i<n}$ and $P=\mathsf{H2C}(\mathsf{seed},0)$. Compute $g_0=\mathsf{RS}_0(\mathbf G)$ — the group Reed–Solomon codeword of the generators on the evaluation domain $D_0$ of §7.1 — and publish its Merkle root. This is a **deterministic public function of the seed**: anyone can recompute $g_0$ and check the root, so it adds no trust (transparent), and it is near-linear with FFT-grade constants (Atlas's $n^{1+\varepsilon}$ galactic table is gone). Cost $\tilde O(n)$, amortized over every opening under this seed, forever.

**Commit** (claim later $\hat a(z)=v$): $C=\langle \mathbf a,\mathbf G\rangle=\sum_i a_i G_i$ — one group element, Pedersen (identical to Genesis; homomorphic; compatible with existing Bulletproofs commitments).

**Open:**
1. **reduce.** $\mathbf V$ sends $\alpha$; set $P'=\alpha P$, $C':=C+vP'$. Run the sumcheck on $A(\mathbf X)=\hat f(\mathbf X)G(\mathbf X)+\mathbf{eq}(\mathbf X,z)\hat f(\mathbf X)P'$ with target $C'$, degree bound $2$; $\mathbf P$ finally sends $a:=\hat f(r)$. This *both* proves the opening and outputs a single claim $(r,W)$ meaning $G(r)=W$, where $W=(V-a\,\mathbf{eq}(r,z)P')/a$. Proof: $3k$ group + $1$ field.
2. **decide.** Run $\mathsf{BaseFold}_{\mathbb G}(r,W)$ against the preprocessed $g_0$: FS'd sumcheck on $G(\mathbf X)\mathbf{eq}(r,\mathbf X)$ + FRI folding of $g_0$ with $\ell=O(\lambda)$ queries, each answered with Merkle openings. Proof: $O(\lambda\log^2 n)$ hashes.

**Verify** (all online, polylog):

| # | Check | Cost |
|---|---|---|
| 1 | FS challenges | $O(\log n)$ hashes |
| 2 | reduce round checks $A_i(r_i)=A_{i+1}(0)+A_{i+1}(1)$, base $A_1(0)+A_1(1)=C'$, and $aG(r)+ab_0 P'=W\!\Leftrightarrow\! G(r)=W$ with $b_0=\mathbf{eq}(r,z)$ | $2k=O(\log n)$ smul |
| 3 | decide sumcheck round checks + final $g_k\equiv c$, $c\cdot\mathbf{eq}(r,v)=A_k(r_k)$ | $O(\lambda\log n)$ smul |
| 4 | decide FRI consistency: $\ell=O(\lambda)$ queries $\times\,k$ layers, $\mathsf{consistent}_{g,r}(q_i)$ + Merkle path checks | $O(\lambda\log^2 n)$ hashes |

Total online: $O(\lambda\log n)$ scalar mults $+\ O(\lambda\log^2 n)$ hashes — **succinct**. Proof: $O(\log n)$ group $+\ O(\lambda\log^2 n)$ hashes — **succinct**.

## Security sketch

- **Completeness.** reduce: honest $a=\hat f(r)$ and sumcheck completeness (`sumcheck_round_complete` is the round identity). decide: the §7.1 encoding is chosen so the correct FRI folding of $\mathsf{RS}_0(\mathbf G)$ lands on the multilinear evaluation, $f_k\equiv\hat G(r_1,\dots,r_k)$; BaseFold then accepts the true $W$ (2025/1325 §7.1, Thm 7.3 completeness).
- **Soundness.** (i) **reduce is knowledge-sound under DLA** (Thm 5.1): the ACK21 tree extractor pulls a witness $a$ with $\mathsf{com}(a)=C$, $\hat a(z)=v$, or else a nontrivial dlog relation among $\{G_i\}$ — i.e. a break of Pedersen binding (this repo's `pedersen_binding` / `schnorr_extract` / `IPAExtractor` are the analogous objects). (ii) **decide is round-by-round sound with error $\max\{(n{+}2)/p,\,2^{-\lambda}\}$** (Thm 7.3), resting on the group-code proximity gap (Lemma 7.2) — **unconditional** proximity, no group assumption beyond what the ROM already gives (mirrors this repo's `Delegation.lean`: the certificate is a *proof*, not an argument). (iii) FS/Merkle compilation to the ROM (Thm 2.3), the same model Genesis already assumes.
- **Consistency with the repo's lower bound.** `no_lossy_digest_verifier` requires a *linear lossy* digest and a verdict that is a fixed function of it. Prism's verifier is interactive (prover-aided FRI) and its digest is a *binding non-linear* Merkle root of the full codeword — neither hypothesis applies. Prism is the "add prover help" escape, not a violation.

## Costs

| Item | Genesis | **Prism** |
|---|---|---|
| Setup | publish a seed (no preprocessing) | seed + one-time transparent $\tilde O(n)$ RS-encode & Merkle root |
| Commitment | 1 group element | 1 group element |
| Proof | $O(\log n)$ grp + polylog fld | $O(\log n)$ grp + $O(\lambda\log^2 n)$ hash |
| Verifier online | polylog, small constants | $O(\lambda\log n)$ smul + $O(\lambda\log^2 n)$ hash |
| **Prover** | **$10^2$–$10^3\times$ raw MSM** (in-circuit H2C, point decompress, double-and-add, MSM tree; **two-field emulation**) | **$O(n)$ scalar mults** ($\sim$ a few $\times$ MSM: reduce $O(n)$ + decide $\approx 4n$); **no circuit, no non-native arithmetic** |
| Two-field problem | **yes — main open engineering** | **none** |
| End-to-end soundness proof | **not written out** (BP extraction $\circ$ FS'd GKR) | **complete in 2025/1325** (Thm 5.1, 7.3, 2.3) |

## Honest caveats

- **Fatter (still succinct) proof.** The win is paid in proof shape: FRI queries make the proof $O(\lambda\log^2 n)$ hashes and the verifier do $O(\lambda\log^2 n)$ hashing — concretely kilobytes and a heavier polylog than Genesis's slim $O(\log n)$-group transcript. Small verifier + small proof are both met, but Prism trades Genesis's slimmer proof for a much lighter prover and a real security proof. This is the intended dial, not a regression against the stated goal.
- **Preprocessing reintroduced (accepted).** Genesis's headline was *zero* preprocessing; Prism needs the one-time RS encoding. It is transparent (public, recomputable, no trapdoor) and near-linear (not Atlas's galactic table), and it is amortized over all openings under a seed.
- **Group-native FRI machinery.** Folding runs over $\mathbb G$ (Reed–Solomon over the module $\mathbb G^n$); codewords are group elements ($\sim 2\times$ field-codeword size, and you hash group elements). For curves with a smooth $2^k$-subgroup (Pasta) plain FRI domains suffice; for curves without one (Grumpkin) use the ECFFT domains $\{D_i\}$/maps $\{\psi_i\}$ of §7.1 (BSCKL22). A small, worked-out generalization — not a conceptual barrier.
- **Provenance.** The cryptographic core is Eagen–Gabizon's group-BaseFold, not new here. Prism's contribution is recognizing it discharges *this repo's* terminal obligation (`genFinal_eq_mle`) strictly better than Atlas/Genesis in the single-proof, preprocessing-allowed regime, and that it stays clear of the repo's own impossibility (`no_lossy_digest_verifier`).

## Comparison

| Scheme | Proof | Verifier | Transparent | Assumptions | Recursion | Prover | Practical constants |
|---|---|---|---|---|---|---|---|
| Bulletproofs | $O(\log n)$ | $\Theta(n)$ | yes | dlog | no | linear | yes |
| Hyrax | $O(\sqrt n)$ | $O(\sqrt n)$ | yes | dlog | no | linear | yes |
| Dory | $O(\log n)$ | $O(\log n)$ | yes | SXDH | no | linear | yes |
| DARK | $O(\log n)$ | polylog | yes | unknown order | no | linear | slow ops |
| Halo / Nova | $O(\log n)$ am. | per-step $O(\log n)$ + one decider | yes | dlog | **yes** | linear | yes |
| Atlas | $O(\log n)$+polylog | polylog | yes | dlog | no | linear | **galactic** |
| Genesis | $O(\log n)$+polylog | polylog | yes | dlog | no | **$10^2$–$10^3\times$ MSM** | implementable |
| **Prism** | $O(\log n)$ grp + $O(\lambda\log^2 n)$ hash | $O(\lambda\log^2 n)$ | yes (1-time preproc.) | dlog + ROM | no | **$O(n)$ smul, small const.** | **implementable, no two-field** |

## What the Lean scaffolding already gives, and what a formalization would add

Reusable as-is: `genFinal_eq_mle` (the reduction target — MSM as MLE evaluation), `sum_split`/`msm_split`/`sumcheck_round_complete`/`disagreement_is_root`/`cheating_caught` (the sumcheck engine both `reduce` and `decide` run on), `pedersen_binding`/`schnorr_extract`/`IPAExtractor` (binding + the extractor `reduce`'s knowledge-soundness bottoms out in), and `no_lossy_digest_verifier` (the impossibility Prism is shown to sidestep). New objects a paper-grade Lean layer would need: the group Reed–Solomon code and its fold map, the encoding property $f_k\equiv\hat G(r)$, and the proximity-gap lemma over $\mathbb G$ (Lemma 7.2) — the genuinely new surface, replacing Genesis's in-circuit curve gadgets (`RcbAdd`, `SquareMulStep`, …) entirely.
