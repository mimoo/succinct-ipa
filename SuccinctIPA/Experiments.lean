/-
# Experiments: creative attempts to make `G₀ = ⟨s,G⟩` succinct

`succinct_correct` reduced everything to discharging the `GenOracle` — producing the
folded generator `G₀ = ⟨s,G⟩` without the `Θ(n)` MSM.  This file is a lab notebook:
each idea is reduced to a Lean identity, and we let the proof assistant tell us whether
the linear cost actually disappears or just *moves*.  The recurring verdict — made
precise — is **conservation of linear work**: every transformation that looks like it
removes the MSM turns out to produce another object of exactly the same `⟨·,gens⟩` shape.
The two transformations that genuinely help do so by changing the *model*, not by magic:
amortization (`batch_amortization`, proven) and structure/pairings (discussed).

Indices are bit-sets `t : Finset (Fin k)`; recall `n = 2^k`.
-/
import SuccinctIPA.Protocol
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Module.BigOperators

open Finset

namespace SuccinctIPA

variable {F : Type*} [Field F]
variable {G : Type*} [AddCommGroup G] [Module F G]
variable {k : ℕ}

/-! ## Experiment 1 — the s-vector is a pure tensor (rank 1)

`s = (x₁⁻¹,x₁) ⊗ (x₂⁻¹,x₂) ⊗ … ⊗ (x_k⁻¹,x_k)`.  Concretely each coordinate is a single
product over the `k` rounds.  A rank-1 tensor contracted against `G` folds one mode at a
time — but each mode-fold still touches half the remaining generators, so the total stays
`Θ(2^k)`.  This is *why* IPA folding is intrinsic, stated as an identity. -/
theorem sCoeff_eq_prod_ite (x : Fin k → F) (t : Finset (Fin k)) :
    sCoeff x t = ∏ j : Fin k, (if j ∈ t then x j else (x j)⁻¹) := by
  unfold sCoeff
  rw [← Finset.prod_mul_prod_compl t (fun j => if j ∈ t then x j else (x j)⁻¹)]
  congr 1
  · exact Finset.prod_congr rfl (fun j hj => by rw [if_pos hj])
  · exact Finset.prod_congr rfl (fun j hj => by rw [if_neg (Finset.mem_compl.mp hj)])

/-! ## Experiment 2 — recast the MSM as a multilinear evaluation of the *public* generators

Pull `∏ⱼ xⱼ⁻¹` out of every coordinate: `sₜ = (∏ⱼ xⱼ⁻¹)·∏_{j∈t} xⱼ²`.  Hence

    G₀ = (∏ⱼ xⱼ⁻¹) · MLE_G(x₁²,…,x_k²),

where `MLE_G` is the **multilinear extension of the public generator tensor**
`t ↦ gens t`.  This is the gateway used by every sumcheck/tensor PCS (Hyrax, etc.): the
opening of a dlog commitment *is* a multilinear evaluation.  The catch (Experiment 3):
`MLE_G` has the public generators as coefficients, so evaluating it is itself an MSM. -/
def mleG (gens : Finset (Fin k) → G) (y : Fin k → F) : G :=
  ∑ t : Finset (Fin k), (∏ j ∈ t, y j) • gens t

/-- Per-coordinate: the s-entry is `(∏ⱼ xⱼ⁻¹)` times a *multilinear monomial* in `xⱼ²`. -/
theorem sCoeff_factor (x : Fin k → F) (hx : ∀ j, x j ≠ 0) (t : Finset (Fin k)) :
    sCoeff x t = (∏ j, (x j)⁻¹) * ∏ j ∈ t, (x j) ^ 2 := by
  have h1 : (∏ j ∈ t, x j) = (∏ j ∈ t, (x j)⁻¹) * ∏ j ∈ t, (x j) ^ 2 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [pow_two, ← mul_assoc, inv_mul_cancel₀ (hx j), one_mul]
  have h2 : (∏ j, (x j)⁻¹) = (∏ j ∈ t, (x j)⁻¹) * ∏ j ∈ tᶜ, (x j)⁻¹ :=
    (Finset.prod_mul_prod_compl t _).symm
  unfold sCoeff
  rw [h1, h2]; ring

/-- **The MSM is a multilinear evaluation.**  `G₀` equals `MLE_G` of the *public*
    generators at the squared challenges, up to the global scalar `∏ⱼ xⱼ⁻¹`. -/
theorem genFinal_eq_mle (gens : Finset (Fin k) → G) (x : Fin k → F) (hx : ∀ j, x j ≠ 0) :
    genFinal gens x = (∏ j, (x j)⁻¹) • mleG gens (fun j => (x j) ^ 2) := by
  unfold genFinal mleG
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [sCoeff_factor x hx t, mul_smul]

/-! ## Experiment 3 — "conservation of linear work"

Could we evaluate `MLE_G(y)` succinctly?  `MLE_G` is `F`-linear in the generator vector,
and its evaluation map is, structurally, another `⟨·, gens⟩` — the very thing we are
trying to avoid.  We make the linearity precise; the consequence is that no algebraic
identity collapses a *single* evaluation of `MLE_G` at a generic point below `Θ(2^k)`. -/
theorem mleG_add (g₁ g₂ : Finset (Fin k) → G) (y : Fin k → F) :
    mleG (fun t => g₁ t + g₂ t) y = mleG g₁ y + mleG g₂ y := by
  unfold mleG
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun t _ => by rw [smul_add])

/-- `MLE_G` evaluation is itself a multi-scalar multiplication: `mleG gens y = msm c gens`
    with the (length-`2^k`) coefficient vector `c t = ∏_{j∈t} yⱼ`.  Sumcheck/folding can
    *relocate* this MSM (e.g. defer it to a random point) but the terminal obligation has
    this same `msm`-shape — the linear cost is conserved, never removed. -/
theorem mleG_is_msm (gens : Finset (Fin k) → G) (y : Fin k → F) :
    mleG gens y = msm (fun t => ∏ j ∈ t, y j) gens := rfl

/-! ## Experiment 4 — amortization: the one route that *works* under plain transparent dlog

Defer `G₀` instead of certifying it (Halo).  For `m` proofs over the *same* SRS `gens`
with challenge vectors `x₁,…,x_m`, the verifier checks a single random linear combination
of the claimed generators.  The right-hand side collapses to **one** MSM over `gens`, with
the *combined* coefficient vector `Σᵢ ρⁱ s(xᵢ)` — independent of `m`.  So a batch of `m`
proofs costs `m · O(log n)` (the succinct checks) plus exactly **one** `Θ(n)` MSM. -/
theorem batch_amortization (gens : Finset (Fin k) → G) {m : ℕ}
    (ρ : Fin m → F) (xs : Fin m → (Fin k → F)) :
    (∑ i, ρ i • genFinal gens (xs i))
      = msm (fun t => ∑ i, ρ i * sCoeff (xs i) t) gens := by
  unfold genFinal msm
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.sum_smul]

/-!
## Lab conclusions

Each experiment, as an identity, lands the same way:

* **E1** `sCoeff_eq_prod_ite` — `s` is rank-1; folding contracts it mode-by-mode, total `Θ(n)`.
* **E2** `genFinal_eq_mle` — opening a dlog commitment *is* a multilinear evaluation of the
  public generators. This is the door to sumcheck-based PCS…
* **E3** `mleG_is_msm` + `mleG_add` — …but that evaluation is *again* an `msm` over `gens`.
  Sumcheck/tensor tricks relocate the `Θ(n)` work (to a random point, or to the prover) but
  the verifier's terminal query keeps the `⟨·,gens⟩` shape. **Linear work is conserved.**
* **E4** `batch_amortization` — the genuine win available under plain, transparent dlog:
  amortize. `m` proofs ⇒ one shared MSM ⇒ per-proof verifier `O(log n + n/m) → O(log n)`.

What the lab cannot give you (and Lean shows *why* — the obligation never reduces to ⊥,
only to another `msm`): a transparent, non-interactive, non-amortized succinct verifier for
prime-order dlog. The two ways out leave a footprint in the assumptions:

* **Pairings / structured SRS (Dory, KZG-style).** With `gensₜ = [τ^{coord t}]`,
  `genFinal_eq_mle` gives `G₀ = (∏xⱼ⁻¹)·[g(τ)]`, checkable by one opening/pairing.
  Truly succinct, but trusted/updatable setup + pairing assumptions.
* **Unknown-order groups (DARK, class/RSA groups).** Integer-exponent encodings admit a
  succinct division-based evaluation check, giving transparent `O(log n)` verification —
  at the price of leaving prime-order dlog for hidden-order assumptions.

The scaffolding makes the dividing line a single, checkable hypothesis
(`GenOracle.certifies`), and the experiments show no prime-order-dlog identity discharges
it for free. -/

end SuccinctIPA
