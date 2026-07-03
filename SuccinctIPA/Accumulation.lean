/-
# Making it happen, route 1 — accumulation (Halo / Halo2), prime-order, transparent

The experiments showed the linear MSM `G₀ = ⟨s,G⟩` cannot be *removed* under prime-order
dlog.  But it can be *deferred*.  This is the idea behind Halo's recursive accumulation,
and it gives a genuinely **succinct per-step verifier** for unboundedly many proofs.

Model the deferred obligation as an `MSMClaim`: a coefficient vector `s` together with a
claimed value `Q`, which is *valid* iff `Q = ⟨s,gens⟩`.  Checking validity is the `Θ(n)`
"decider".  The accumulation verifier never runs it; it only **folds** two claims with a
random challenge `α`, and — crucially — the fold of the claimed values is `Q₁ + α•Q₂`,
which touches *neither* `s` *nor* `gens`: **O(1) group operations per step**.

Two theorems make this rigorous:

* `fold_valid` — *completeness*: folding two valid claims gives a valid claim.
* `fold_sound` — *knowledge soundness*: if a fold is valid for two distinct challenges,
  **both** input claims were valid.  (Same shape as the Schnorr extractor.)

Consequence: a chain of `m` proofs is verified by `m·O(log n)` succinct steps that fold
their MSM claims into one accumulator, plus a **single** `Θ(n)` decider run once, ever.
That is what a deployed "succinct" dlog verifier (Halo2) actually does.
-/
import SuccinctIPA.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

open Finset

namespace SuccinctIPA

variable {ι : Type*} {F : Type*} {G : Type*}
  [Fintype ι] [Field F] [AddCommGroup G] [Module F G]

/-- `msm` is linear: a random-linear-combination of two coefficient vectors gives the
    same combination of their MSMs.  This single fact powers the whole fold. -/
lemma msm_add_smul (a b : ι → F) (α : F) (gens : ι → G) :
    msm (fun i => a i + α * b i) gens = msm a gens + α • msm b gens := by
  unfold msm
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by rw [add_smul, mul_smul])

/-- A deferred multi-scalar-multiplication claim. -/
structure MSMClaim (ι F G : Type*) where
  s : ι → F
  Q : G

namespace MSMClaim

variable {ι F G : Type*} [Fintype ι] [Field F] [AddCommGroup G] [Module F G]

/-- The (expensive, `Θ(n)`) decider predicate: the claimed value is the true MSM. -/
def Valid (c : MSMClaim ι F G) (gens : ι → G) : Prop := c.Q = msm c.s gens

/-- The claim's defect; zero exactly when valid.  Linear in the claim, which is the key. -/
def defect (c : MSMClaim ι F G) (gens : ι → G) : G := c.Q - msm c.s gens

/-- The accumulation **fold**.  Note `Q` is combined as `Q₁ + α•Q₂` — no `gens`, no MSM:
    the per-step verifier work is O(1) group operations. -/
def fold (c₁ c₂ : MSMClaim ι F G) (α : F) : MSMClaim ι F G :=
  ⟨fun i => c₁.s i + α * c₂.s i, c₁.Q + α • c₂.Q⟩

theorem valid_iff_defect (c : MSMClaim ι F G) (gens : ι → G) :
    c.Valid gens ↔ c.defect gens = 0 := by
  unfold Valid defect; exact sub_eq_zero.symm

/-- The defect folds linearly in `α` — the heart of both completeness and soundness. -/
theorem fold_defect (c₁ c₂ : MSMClaim ι F G) (α : F) (gens : ι → G) :
    (c₁.fold c₂ α).defect gens = c₁.defect gens + α • c₂.defect gens := by
  show (c₁.Q + α • c₂.Q) - msm (fun i => c₁.s i + α * c₂.s i) gens
      = (c₁.Q - msm c₁.s gens) + α • (c₂.Q - msm c₂.s gens)
  rw [msm_add_smul, smul_sub]; abel

/-- **Completeness of accumulation.**  Folding two valid claims gives a valid claim — and
    the fold did only `Q₁ + α•Q₂`, never an MSM. -/
theorem fold_valid {c₁ c₂ : MSMClaim ι F G} (gens : ι → G) (α : F)
    (h₁ : c₁.Valid gens) (h₂ : c₂.Valid gens) : (c₁.fold c₂ α).Valid gens := by
  rw [valid_iff_defect] at h₁ h₂ ⊢
  rw [fold_defect, h₁, h₂, smul_zero, add_zero]

/-- **Knowledge soundness of accumulation.**  If the folded claim is valid for two
    distinct challenges, then *both* input claims were valid.  So an accumulator that
    passes the (single, final) decider certifies every proof folded into it. -/
theorem fold_sound {c₁ c₂ : MSMClaim ι F G} (gens : ι → G) {α₁ α₂ : F} (hne : α₁ ≠ α₂)
    (h₁ : (c₁.fold c₂ α₁).Valid gens) (h₂ : (c₁.fold c₂ α₂).Valid gens) :
    c₁.Valid gens ∧ c₂.Valid gens := by
  rw [valid_iff_defect, fold_defect] at h₁ h₂
  have hd2 : (α₁ - α₂) • c₂.defect gens = 0 := by
    have e : (α₁ - α₂) • c₂.defect gens
           = (c₁.defect gens + α₁ • c₂.defect gens)
             - (c₁.defect gens + α₂ • c₂.defect gens) := by rw [sub_smul]; abel
    rw [e, h₁, h₂, sub_zero]
  have hne' : α₁ - α₂ ≠ 0 := sub_ne_zero.mpr hne
  have hc2 : c₂.defect gens = 0 := by
    have := congrArg (fun y => (α₁ - α₂)⁻¹ • y) hd2
    simpa [smul_smul, inv_mul_cancel₀ hne', one_smul, smul_zero] using this
  have hc1 : c₁.defect gens = 0 := by
    rw [hc2, smul_zero, add_zero] at h₁; exact h₁
  exact ⟨(valid_iff_defect c₁ gens).mpr hc1, (valid_iff_defect c₂ gens).mpr hc2⟩

end MSMClaim
end SuccinctIPA
