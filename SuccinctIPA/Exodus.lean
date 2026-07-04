/-
# Exodus — Genesis without the λ-grind: Pedersen-committed advice
  (`solutions/5-exodus.md`; the FRI-free, hash-free small-proof point)

Genesis's certificate is already an information-theoretic sumcheck — no FRI, no Merkle
trees, hashing only as Fiat–Shamir.  Its cost problem (megabyte proofs, ~8× prover) has a
single cause: every non-algebraic operation (field inversion, square root, branch
selection, scalar multiplication) is computed by a **λ-deep chain** of squaring layers,
and the proof pays per layer.

Exodus deletes the chains with the classic move Genesis had to avoid: **nondeterministic
advice**, made sound without hashes by committing the advice vectors with **Pedersen over
the same generator basis `G`** (dlog binding — `pedersen_binding`) and opening them at the
sumcheck endpoints with IPA instances whose *own* terminal MSMs random-linear-combine into
the one delegated MSM claim (`Experiments.batch_amortization` — the regress bottoms out).

The λ-deep operations become one-layer checks; this file proves their soundness atoms:

  * `advice_inverse_sound`  — `t·d = 1` pins `t = d⁻¹` (kills the 380-layer inversion chain);
  * `advice_sqrt_sound`     — `y² = g` pins `y` up to sign (kills the ~1200-layer CT-TS
    chain; sign flexibility is harmless by the binding argument recorded in the spec);
  * `advice_branch_sound`   — `s(s−1) = 0` and `y² = s·g₁ + (1−s)·g₂` force the prover into
    exactly one of the two SWU branches with a genuine root (kills the Legendre chains);
  * `advice_batch_two`      — two MSM claims over the same basis merge under a random
    scalar into one (the two-claim instance of `batch_amortization`, stated in the form the
    opening-merge uses; soundness direction is `MSMClaim.fold_sound`).
-/
import SuccinctIPA.Accumulation
import SuccinctIPA.Experiments
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

open Finset

namespace SuccinctIPA

variable {F : Type*} [Field F]

/-- **Inversion by advice.**  The one-layer check `t·d = 1` replaces the 255-layer
    `d^(p-2)` chain: any satisfying advice `t` *is* the inverse. -/
theorem advice_inverse_sound (t d : F) (h : t * d = 1) : d ≠ 0 ∧ t = d⁻¹ := by
  have hd : d ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    exact one_ne_zero h.symm
  refine ⟨hd, ?_⟩
  field_simp
  exact h

/-- **Square roots by advice.**  The one-layer check `y² = g` replaces the constant-time
    Tonelli–Shanks circuit: any satisfying advice is a genuine root (and `g` is thereby
    proven square).  The residual `±y` freedom only lets a prover pick among finitely many
    valid SRS variants, each individually binding (see spec). -/
theorem advice_sqrt_sound (y g : F) (h : y ^ 2 = g) :
    IsSquare g ∧ ∀ y' : F, y' ^ 2 = g → y' = y ∨ y' = -y := by
  constructor
  · exact ⟨y, by rw [← h]; ring⟩
  · intro y' h'
    have hz : (y' - y) * (y' + y) = 0 := by
      have : y' ^ 2 - y ^ 2 = 0 := by rw [h, h', sub_self]
      calc (y' - y) * (y' + y) = y' ^ 2 - y ^ 2 := by ring
        _ = 0 := this
    rcases mul_eq_zero.mp hz with h1 | h2
    · exact Or.inl (sub_eq_zero.mp h1)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h2)

/-- **Branch selection by advice.**  A boolean advice `s` with the fused check
    `y² = s·g₁ + (1−s)·g₂` forces the prover into exactly one SWU branch, with a genuine
    root for the branch it picked — replacing the in-circuit Legendre chains entirely. -/
theorem advice_branch_sound (s g1 g2 y : F)
    (hs : s * (s - 1) = 0) (hy : y ^ 2 = s * g1 + (1 - s) * g2) :
    (s = 1 ∧ y ^ 2 = g1) ∨ (s = 0 ∧ y ^ 2 = g2) := by
  rcases mul_eq_zero.mp hs with h0 | h1
  · right
    refine ⟨h0, ?_⟩
    rw [hy, h0]
    ring
  · left
    have hs1 : s = 1 := by linear_combination h1
    refine ⟨hs1, ?_⟩
    rw [hy, hs1]
    ring

/-- **The opening-merge bottoms out.**  Two MSM claims over the *same* basis (the main
    delegated claim and a batched advice-opening claim) merge under a verifier scalar `μ`
    into a single MSM claim — so committing advice with Pedersen-over-`G` adds openings
    but never a second delegation.  (Two-claim form of `batch_amortization`; the soundness
    converse — validity at two distinct `μ` forces both — is `MSMClaim.fold_sound`.) -/
theorem advice_batch_two {ι : Type*} [Fintype ι]
    {G : Type*} [AddCommGroup G] [Module F G]
    (gens : ι → G) (s₁ s₂ : ι → F) (μ : F) :
    msm s₁ gens + μ • msm s₂ gens = msm (fun i => s₁ i + μ * s₂ i) gens :=
  (msm_add_smul s₁ s₂ μ gens).symm

end SuccinctIPA
