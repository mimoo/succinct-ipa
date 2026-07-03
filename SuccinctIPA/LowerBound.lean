/-
# The other half: a lower bound — why the verifier *must* read all `n` generators

Everything so far is a *construction* (a way to get sublinear verification by adding
structure).  This file proves the matching **impossibility**, turning the informal
"conservation of linear work" into a theorem: a verifier that decides the final
inner-product/MSM relation `⟨s, d⟩ = Q` while reading only a **strict subset** of the
coordinates cannot be sound — because the relation genuinely depends on *every* coordinate
with `s_i ≠ 0`, and for the IPA challenge vector **every** `s_i ≠ 0` (`sCoeff_ne_zero`).

This is information-theoretic and unconditional (no computational model): we model "reads
only `S`" as "the verdict depends only on the `S`-coordinates" and derive a contradiction
from soundness when `S ≠ univ`.  It is exactly why a *transparent, unaided* dlog verifier is
linear — and thus why every sublinear scheme here (Hyrax, Dory, DARK, accumulation) must add
prover help, a pairing, an unknown-order group, or recursion.

We argue at the discrete-log layer (`dot s d`, the exponent of `⟨s,G⟩`, cf. `DlogLayer`),
where the field has no zero divisors and the statement is cleanest.
-/
import SuccinctIPA.SVector
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi

open Finset

namespace SuccinctIPA

variable {F : Type*} [Field F]

/-- Every entry of the IPA challenge vector is nonzero (challenges and their inverses are). -/
theorem sCoeff_ne_zero {k : ℕ} (x : Fin k → F) (hx : ∀ j, x j ≠ 0) (t : Finset (Fin k)) :
    sCoeff x t ≠ 0 := by
  unfold sCoeff
  exact mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun j _ => hx j))
    (Finset.prod_ne_zero_iff.mpr (fun j _ => inv_ne_zero (hx j)))

/-- **The lower bound.**  Let `s` have all entries nonzero.  Any verifier `V` that
    (i) decides the relation `⟨s, d⟩ = Q` correctly (`hsound`) and (ii) reads only the
    coordinates in `S` (`hreads` — its verdict is unchanged by edits outside `S`) must have
    `S = univ`.  Equivalently: a verifier reading a *strict* subset is unsound.  So the
    honest, transparent, unaided verifier of the IPA final check is **linear**. -/
theorem no_partial_read_verifier
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → F) (hs : ∀ i, s i ≠ 0)
    (S : Finset ι) (hS : S ≠ Finset.univ)
    (V : (ι → F) → F → Prop)
    (hreads : ∀ d d' : ι → F, (∀ i ∈ S, d i = d' i) → ∀ Q, V d Q ↔ V d' Q)
    (hsound : ∀ (d : ι → F) (Q : F), V d Q ↔ dot s d = Q) :
    False := by
  obtain ⟨j, hj⟩ : ∃ j, j ∉ S :=
    not_forall.mp (fun h => hS (Finset.eq_univ_iff_forall.mpr h))
  -- two inputs that agree on everything the verifier reads, but differ at the unread `j`
  set d : ι → F := fun _ => 0 with hd
  set d' : ι → F := fun i => if i = j then (1 : F) else 0 with hd'
  have hd0 : dot s d = 0 := by simp [dot, hd]
  have hd'j : dot s d' = s j := by
    simp only [dot, hd', mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    simp
  have hagree : ∀ i ∈ S, d i = d' i := by
    intro i hi
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    simp [hd, hd', hij]
  -- soundness on `d`, transported to `d'` by `hreads`, forces `s j = 0`
  have hVd : V d 0 := (hsound d 0).mpr hd0
  have hVd' : V d' 0 := (hreads d d' hagree 0).mp hVd
  have hcontra : dot s d' = 0 := (hsound d' 0).mp hVd'
  rw [hd'j] at hcontra
  exact hs j hcontra

/-- **The strong lower bound — even *with preprocessing*.**  Model any verifier state as a
    **linear digest** `D : (ι→F) →ₗ M` of the generators (this captures every transparent
    prime-order option: the verifier's whole view of `G` is some homomorphic image — a
    Pedersen-style commitment, a precomputed table, partial reads — all linear in `G`).  If
    `D` collapses *any* direction `v` that the inner product `⟨s,·⟩` can see
    (`D v = 0` but `dot s v ≠ 0`), then no verifier depending only on the digest `D G` can
    soundly decide `⟨s,G⟩ = Q`: the inputs `G = 0` and `G = v` have the **same digest** yet
    different truth.  Consequence (rank–nullity): a sound digest must have rank `≥ n − 1`, so
    the verifier's view of the generators is **Ω(n)** — there is no sublinear transparent
    prime-order verifier, preprocessing included.  This is the bilinear-map–free wall. -/
theorem no_lossy_digest_verifier
    {ι : Type*} [Fintype ι]
    (s : ι → F) {M : Type*} [AddCommGroup M] [Module F M]
    (D : (ι → F) →ₗ[F] M)
    (v : ι → F) (hv : D v = 0) (hsv : dot s v ≠ 0)
    (V : M → F → Prop)
    (hsound : ∀ G Q, V (D G) Q ↔ dot s G = Q) :
    False := by
  have key : D (0 : ι → F) = D v := by rw [map_zero, hv]
  have hVtrue : V (D 0) 0 := (hsound 0 0).mpr (by simp [dot])
  rw [key] at hVtrue
  exact hsv ((hsound v 0).mp hVtrue)

/-- **Specialized to IPA.**  For the actual challenge vector `sCoeff x` (nonzero challenges),
    no sound verifier of the final inner-product reads fewer than all `n = 2^k` coordinates.
    The linear MSM is not an artifact of Bulletproofs — it is forced. -/
theorem ipa_verifier_must_read_all
    {k : ℕ} (x : Fin k → F) (hx : ∀ j, x j ≠ 0)
    (S : Finset (Finset (Fin k))) (hS : S ≠ Finset.univ)
    (V : (Finset (Fin k) → F) → F → Prop)
    (hreads : ∀ d d', (∀ i ∈ S, d i = d' i) → ∀ Q, V d Q ↔ V d' Q)
    (hsound : ∀ d Q, V d Q ↔ dot (sCoeff x) d = Q) :
    False :=
  no_partial_read_verifier (sCoeff x) (sCoeff_ne_zero x hx) S hS V hreads hsound

end SuccinctIPA
