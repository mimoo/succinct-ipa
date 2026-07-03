/-
# Better than Bulletproofs — Dory: polylog proof **and** polylog verifier, transparent

Bulletproofs: `O(log n)` proof, `O(n)` verifier.  Dory (Lee, TCC 2021) keeps the `O(log n)`
proof and makes the verifier `O(log n)` too — **transparent (no trusted setup)**.  It is a
*dlog* construction: it lives in a bilinear group, where dlog-style assumptions (SXDH) hold.

The wall for prime-order dlog was: to make the verifier sublinear you must compress the
`√n` generator-folds, i.e. **commit to a vector of group elements and fold it homomorphically**
— impossible without a bilinear map (`structured_breaks_binding`).  A pairing
`e : G₁ × G₂ → T` is exactly that bilinear map.  Define the **inner-pairing-product**

    ipp(G, H) = Σ_i e(G_i, H_i)   ∈ T,

a *binding, bilinear* commitment to the generator vector `G`.  Bilinearity makes it
**foldable**: when the prover folds `G ↦ G_lo + x·G_hi` and `H ↦ H_lo + x⁻¹·H_hi`, the
commitment decomposes into four sub-products (`ipp_fold`).  The two *diagonal* ones
`ipp(G_lo,H_lo), ipp(G_hi,H_hi)` depend only on the public setup `G, H` — **precomputable,
transparent** — and the two cross-terms are sent by the prover (O(1) each).  So the verifier
folds the generator commitment in **O(1) per round**, `log n` rounds, never touching the
`Θ(n)` MSM.  Result: `O(log n)` proof and `O(log n)` verifier.

We model the pairing as an `F`-bilinear map `e : G₁ →ₗ[F] G₂ →ₗ[F] T` and prove the bilinearity
of `ipp` in each fold argument (`ipp_add/smul_left/right`), the fold decomposition
(`ipp_fold`), and the bridge to our linear-cost `msm` (`msm_pairing`).
-/
import SuccinctIPA.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Tactic.Abel

open Finset

namespace SuccinctIPA

variable {F : Type*} [Field F]
  {G₁ G₂ T : Type*}
  [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup T]  [Module F T]
  {I : Type*} [Fintype I]
  (e : G₁ →ₗ[F] G₂ →ₗ[F] T)

/-- The **inner-pairing-product**: a binding, bilinear commitment to a generator vector. -/
def ipp (G : I → G₁) (H : I → G₂) : T := ∑ i, e (G i) (H i)

@[simp] theorem ipp_add_left (G G' : I → G₁) (H : I → G₂) :
    ipp e (fun i => G i + G' i) H = ipp e G H + ipp e G' H := by
  unfold ipp
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_add, LinearMap.add_apply])

@[simp] theorem ipp_smul_left (x : F) (G : I → G₁) (H : I → G₂) :
    ipp e (fun i => x • G i) H = x • ipp e G H := by
  unfold ipp
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_smul, LinearMap.smul_apply])

@[simp] theorem ipp_add_right (G : I → G₁) (H H' : I → G₂) :
    ipp e G (fun i => H i + H' i) = ipp e G H + ipp e G H' := by
  unfold ipp
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_add])

@[simp] theorem ipp_smul_right (y : F) (G : I → G₁) (H : I → G₂) :
    ipp e G (fun i => y • H i) = y • ipp e G H := by
  unfold ipp
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_smul])

/-- **The fold decomposition — the engine of Dory's `O(log n)` verifier.**  Folding the
    generators `a ↦ a + x·b` and the right vector `c ↦ c + y·d` splits the commitment into
    four sub-products.  `ipp e a c` and `ipp e b d` are the *diagonals* (public setup ⇒
    precomputed); `ipp e b c, ipp e a d` are the prover's two cross-terms.  The verifier
    checks the new commitment with O(1) work — no `Θ(n)` MSM.  (Dory takes `y = x⁻¹`, so the
    cross challenges cancel; the identity holds for any `x, y`.) -/
theorem ipp_fold (a b : I → G₁) (c d : I → G₂) (x y : F) :
    ipp e (fun i => a i + x • b i) (fun i => c i + y • d i)
      = ipp e a c + y • ipp e a d + x • ipp e b c + (x * y) • ipp e b d := by
  simp only [ipp_add_left, ipp_smul_left, ipp_add_right, ipp_smul_right, smul_add, smul_smul]
  rw [mul_comm y x]
  abel

/-- **One Dory reduction round — the complete protocol step.**  The verifier holds a claim
    `C = ipp(G,H)`.  The prover sends the two cross-terms `L = ipp(G_hi,H_lo)` and
    `R = ipp(G_lo,H_hi)`; the diagonal `ipp(G_lo,H_lo)+ipp(G_hi,H_hi)` is *precomputed* from
    the public setup.  On challenge `x` the verifier forms the new claim
    `C' = diagonal + x·L + x⁻¹·R` in **O(1) group ops**, and `C' = ipp(G',H')` for the folded
    half-length vectors.  `log₂ n` such rounds ⇒ **O(log n) proof and O(log n) verifier** —
    a Bulletproofs-shaped IPA whose verifier is logarithmic. -/
theorem dory_round (G_lo G_hi : I → G₁) (H_lo H_hi : I → G₂) (x : F) (hx : x ≠ 0) :
    ipp e (fun i => G_lo i + x • G_hi i) (fun i => H_lo i + x⁻¹ • H_hi i)
      = (ipp e G_lo H_lo + ipp e G_hi H_hi)
        + x • ipp e G_hi H_lo + x⁻¹ • ipp e G_lo H_hi := by
  rw [ipp_fold, mul_inv_cancel₀ hx, one_smul]
  abel

/-- **Bridge to the linear cost.**  Pairing the very MSM that made the IPA verifier linear
    against a fixed `h` turns it into a scalar combination of the *precomputable* pairings
    `e(G_i, h)`.  Dory's fold then collapses this to `O(log n)` — the MSM the prime-order
    verifier had to compute is, with a pairing, checked logarithmically. -/
theorem msm_pairing (s : I → F) (G : I → G₁) (h : G₂) :
    e (msm s G) h = ∑ i, s i • e (G i) h := by
  have step : e (msm s G) h = (e.flip h) (msm s G) := by rw [LinearMap.flip_apply]
  rw [step]
  unfold msm
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_smul, LinearMap.flip_apply])

end SuccinctIPA
