/-
# One layer under: the discrete-log / exponent structure

Everywhere above, the generators `gens : ι → G` were opaque points.  Go beneath the group
abstraction.  `G` is cyclic of prime order, so every generator is `g_i = d_i • g` for a
**secret discrete-log vector** `d : ι → F` (the `d_i` are exactly what the dlog assumption
hides).  Under this lens the `Θ(n)` MSM is, in the exponent, a *single scalar inner product*
against `d`:

    ⟨s, G⟩  =  ⟨s, d⟩ • g.

So the IPA verifier's linear check is really `⟨s, d⟩ = r` against a **hidden** vector `d`,
i.e. a multilinear evaluation of the secret dlogs.  This is the bedrock explanation of every
result in the journal, and it pincers the problem:

* **Structured secret dlogs ⇒ succinct.**  If `d_i = τ^i`, then `⟨s,d⟩ = Σ s_i τ^i` is a
  polynomial evaluation (`msm_structured_srs`); for the IPA tensor `s` this collapses to the
  single succinct scalar `bSuccinct` (`genFinal_structured`, closing the loop with the very
  first identity).  This is the KZG / structured-SRS layer.
* **But public structure ⇒ broken binding.**  Geometric *public* generators carry an
  explicit dlog relation `τ·g_i − g_{i+1} = 0`, so they are not binding
  (`structured_breaks_binding`).

Hence succinctness needs the dlogs simultaneously *structured* (so `⟨s,d⟩` compresses) and
*hidden* (so binding survives) — a trapdoor (`τ` secret = trusted setup), or a pairing to
evaluate the hidden structure, or hidden-order groups.  No transparent prime-order escape,
and now we can see *why* at the level of the discrete logs.
-/
import SuccinctIPA.Soundness
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel

open Finset

namespace SuccinctIPA

variable {F : Type*} [Field F] {G : Type*} [AddCommGroup G] [Module F G]

/-- **The MSM is a hidden inner product.**  With generators `g_i = d_i • g` for a secret
    dlog vector `d`, the multi-scalar multiplication collapses, in the exponent, to the
    single scalar `⟨s,d⟩`. -/
theorem msm_eq_dlog_inner {ι : Type*} [Fintype ι] (g : G) (d s : ι → F) :
    msm s (fun i => d i • g) = dot s d • g := by
  unfold msm dot
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl (fun i _ => smul_smul (s i) (d i) g)

/-- **Structured (geometric) secret dlogs turn the MSM into a polynomial evaluation.**
    `d_i = τ^i` ⇒ `⟨s, G⟩ = (Σ s_i τ^i) • g`.  This is the KZG/structured-SRS mechanism. -/
theorem msm_structured_srs (g : G) (τ : F) {n : ℕ} (s : Fin n → F) :
    msm s (fun i => τ ^ (i : ℕ) • g) = (∑ i, s i * τ ^ (i : ℕ)) • g := by
  simp only [msm_eq_dlog_inner, dot]

variable {k : ℕ}

/-- **The loop closes.**  When the generator dlogs are the structured vector `z^{coord t}`,
    the folded generator is the single succinct scalar `bSuccinct(x,z)` times `g` — the same
    `O(log n)` quantity from the opening identity (`bSuccinct_eq_bLinear`).  Structured dlogs
    make `G₀` succinct outright. -/
theorem genFinal_structured (g : G) (z : F) (x : Fin k → F) :
    genFinal (fun t => z ^ (coord t) • g) x = bSuccinct x z • g := by
  show msm (sCoeff x) (fun t => z ^ coord t • g) = bSuccinct x z • g
  rw [msm_eq_dlog_inner, bSuccinct_eq_bLinear]
  rfl

/-- **Public structure destroys binding.**  Geometric generators `g_i = τ^i • g` satisfy the
    nontrivial dlog relation `τ·g₀ − g₁ = 0`, witnessed by the coefficient vector `(τ, -1)`.
    So a publicly-structured generator set is *not* binding — which is exactly why the
    structured SRS must keep `τ` behind a trapdoor.  (Shown for `n = 2`; it extends.) -/
theorem structured_breaks_binding (g : G) (τ : F) (hτ : τ ≠ 0) :
    ¬ NoDLogRelation F (fun i : Fin 2 => τ ^ (i : ℕ) • g) := by
  intro h
  have hc : msm (![τ, -1] : Fin 2 → F) (fun i : Fin 2 => τ ^ (i : ℕ) • g) = 0 := by
    unfold msm
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
               Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul]
    abel
  have hzero := h _ hc
  have hτ0 : τ = 0 := by
    have := congrFun hzero 0
    simpa using this
  exact hτ hτ0

end SuccinctIPA
