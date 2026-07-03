/-
# Pre-proof recursion — Nova folding: the light-prover scheme

The complaint about Halo-style accumulation is real: it is **post-proof recursion** — every
step *produces a full proof*, and the next step must additionally prove "I verified the
previous proof."  The prover pays proof-generation at every step.

**Nova** (Kothapalli–Setty–Tzialla) inverts this: **fold first, prove once**.  Two *unproven*
computation claims (relaxed R1CS instances) are folded into one by a random challenge.  The
per-step prover computes **one cross-term vector `T` and one Pedersen commitment to it** — a
couple of native MSMs, *no FFTs, no proof generation, no verifier-in-circuit*.  The per-step
verifier folds commitments with O(1) group ops.  Only at the very end of the whole chain is a
single (Bulletproofs/Spartan-style) proof produced for the one accumulated claim.  Prime-order,
transparent, Pedersen-only — **no pairing, no unknown-order group**.

Why *relaxed* R1CS?  Plain R1CS `(Az)∘(Bz) = Cz` is quadratic, so a random linear combination
of two satisfying instances is *not* satisfying — the cross terms break it.  Nova's fix is to
absorb the cross terms into an explicit **error vector `E`** and a scalar `u`:

    (Az) ∘ (Bz) = u • (Cz) + E.

Then folding *works*: `z' = z₁ + r·z₂`, `u' = u₁ + r·u₂`, `E' = E₁ + r·T + r²·E₂`, where the
cross-term `T` depends only on the two instances (`nova_fold` — completeness, proven).  The
map is quadratic in `r`, so validity at **three** distinct challenges pins all coefficients —
that is the knowledge-soundness core (`quadratic_vanish`, proven), the degree-2 analogue of
the accumulator's `fold_sound`.

Cost table per step (the point of the whole file):
  * prover:   compute `T`, commit `T̄ = ⟨T, gens⟩` — O(n) *native group ops*, **no proving**;
  * verifier: `u' = u₁+r·u₂`, `x' = x₁+r·x₂`, `Ē' = Ē₁ + r·T̄ + r²·Ē₂` — **O(1) group ops**
    (commitments fold homomorphically: `msm_add_smul`).
  * end of chain: **one** proof, once.
-/
import SuccinctIPA.Accumulation
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.LinearCombination

open Finset

namespace SuccinctIPA

variable {F : Type*} [Field F]

/-- Pointwise (Hadamard) product of vectors. -/
def had {κ : Type*} (v w : κ → F) : κ → F := fun i => v i * w i

variable {ι κ : Type*}

/-- **The Nova folding identity (completeness).**  If two relaxed R1CS instances
    `(z₁,u₁,E₁)` and `(z₂,u₂,E₂)` are satisfying, then their `r`-fold is satisfying with the
    error `E' = E₁ + r·T + r²·E₂`, where the cross-term
    `T = (Az₁)∘(Bz₂) + (Az₂)∘(Bz₁) − u₁·Cz₂ − u₂·Cz₁`
    is computable by the prover from the two instances alone — **no proof is generated**.
    (`A,B,C` are the R1CS matrices, modelled as linear maps.) -/
theorem nova_fold
    (A B C : (ι → F) →ₗ[F] (κ → F))
    (z₁ z₂ : ι → F) (u₁ u₂ : F) (E₁ E₂ : κ → F) (r : F)
    (h₁ : had (A z₁) (B z₁) = u₁ • C z₁ + E₁)
    (h₂ : had (A z₂) (B z₂) = u₂ • C z₂ + E₂) :
    had (A (z₁ + r • z₂)) (B (z₁ + r • z₂))
      = (u₁ + r * u₂) • C (z₁ + r • z₂)
        + (E₁
           + r • (had (A z₁) (B z₂) + had (A z₂) (B z₁) - u₁ • C z₂ - u₂ • C z₁)
           + (r * r) • E₂) := by
  funext i
  have p₁ := congrFun h₁ i
  have p₂ := congrFun h₂ i
  simp only [had, map_add, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
             smul_eq_mul] at p₁ p₂ ⊢
  linear_combination p₁ + (r * r) * p₂

/-- **The knowledge-soundness core: 3-challenge extraction.**  The folded defect is
    *quadratic* in the challenge, `d(r) = d₀ + r·d₁ + r²·d₂`.  If it vanishes at **three**
    distinct challenges, every coefficient is zero — in particular `d₀` and `d₂`, the two
    original instances' defects.  (Degree-2 analogue of `MSMClaim.fold_sound`; with `d₁` the
    cross-term this is exactly why a rewinding extractor with 3 transcripts recovers valid
    witnesses for both folded instances.) -/
theorem quadratic_vanish {M : Type*} [AddCommGroup M] [Module F M]
    (d₀ d₁ d₂ : M) (r₁ r₂ r₃ : F)
    (h12 : r₁ ≠ r₂) (h13 : r₁ ≠ r₃) (h23 : r₂ ≠ r₃)
    (h₁ : d₀ + r₁ • d₁ + (r₁ * r₁) • d₂ = 0)
    (h₂ : d₀ + r₂ • d₁ + (r₂ * r₂) • d₂ = 0)
    (h₃ : d₀ + r₃ • d₁ + (r₃ * r₃) • d₂ = 0) :
    d₀ = 0 ∧ d₁ = 0 ∧ d₂ = 0 := by
  -- eliminate d₀ between pairs, divide by the (nonzero) challenge differences
  have pair : ∀ (a b : F), (d₀ + a • d₁ + (a * a) • d₂ = 0) →
      (d₀ + b • d₁ + (b * b) • d₂ = 0) → a ≠ b →
      d₁ + (a + b) • d₂ = 0 := by
    intro a b ha hb hab
    have hsub : (a - b) • d₁ + (a * a - b * b) • d₂ = 0 := by
      have h : (d₀ + a • d₁ + (a * a) • d₂) - (d₀ + b • d₁ + (b * b) • d₂) = 0 := by
        rw [ha, hb, sub_zero]
      calc (a - b) • d₁ + (a * a - b * b) • d₂
          = (d₀ + a • d₁ + (a * a) • d₂) - (d₀ + b • d₁ + (b * b) • d₂) := by
            rw [sub_smul, sub_smul]; abel
        _ = 0 := h
    have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hfac : (a - b) • (d₁ + (a + b) • d₂) = 0 := by
      rw [smul_add, smul_smul, show (a - b) * (a + b) = a * a - b * b from by ring]
      exact hsub
    have := congrArg (fun v => (a - b)⁻¹ • v) hfac
    simpa [smul_smul, ← mul_assoc, inv_mul_cancel₀ hne] using this
  have f12 := pair r₁ r₂ h₁ h₂ h12
  have f32 := pair r₃ r₂ h₃ h₂ (Ne.symm h23)
  -- eliminate d₁ between the two, divide by r₁ − r₃
  have hd₂ : d₂ = 0 := by
    have hsub : (r₁ - r₃) • d₂ = 0 := by
      have h : (d₁ + (r₁ + r₂) • d₂) - (d₁ + (r₃ + r₂) • d₂) = 0 := by
        rw [f12, f32, sub_zero]
      calc (r₁ - r₃) • d₂
          = ((r₁ + r₂) - (r₃ + r₂)) • d₂ := by
            rw [show (r₁ + r₂) - (r₃ + r₂) = r₁ - r₃ from by ring]
        _ = (r₁ + r₂) • d₂ - (r₃ + r₂) • d₂ := sub_smul _ _ _
        _ = (d₁ + (r₁ + r₂) • d₂) - (d₁ + (r₃ + r₂) • d₂) := by abel
        _ = 0 := h
    have hne : r₁ - r₃ ≠ 0 := sub_ne_zero.mpr h13
    have := congrArg (fun v => (r₁ - r₃)⁻¹ • v) hsub
    simpa [smul_smul, inv_mul_cancel₀ hne] using this
  have hd₁ : d₁ = 0 := by
    have := f12
    rw [hd₂, smul_zero, add_zero] at this
    exact this
  have hd₀ : d₀ = 0 := by
    have := h₁
    rw [hd₁, hd₂, smul_zero, smul_zero, add_zero, add_zero] at this
    exact this
  exact ⟨hd₀, hd₁, hd₂⟩

/-- **The verifier's fold is O(1) group ops.**  The Pedersen commitments to witness and error
    fold homomorphically — `⟨w₁ + r·w₂, gens⟩ = ⟨w₁,gens⟩ + r·⟨w₂,gens⟩` — so the verifier
    updates `Ē' = Ē₁ + r·T̄ + r²·Ē₂` and `w̄' = w̄₁ + r·w̄₂` from the *commitments alone*,
    never touching a generator.  (This is `msm_add_smul`, restated in Nova's role.) -/
theorem nova_commitment_fold {n : Type*} [Fintype n]
    {G : Type*} [AddCommGroup G] [Module F G]
    (gens : n → G) (w₁ w₂ : n → F) (r : F) :
    msm (fun i => w₁ i + r * w₂ i) gens = msm w₁ gens + r • msm w₂ gens :=
  msm_add_smul w₁ w₂ r gens

end SuccinctIPA
