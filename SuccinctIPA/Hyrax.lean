/-
# Making it happen, route 3 — Hyrax: a transparent, prime-order, **sub-linear** verifier

This is the construction that most directly answers "a succinct (non-linear) verifier" for
plain dlog, with **no recursion, no pairing, no trusted setup, prime order** — the price is
`O(√n)` rather than `O(log n)`, and a `√n`-sized commitment.

Idea (Wahby–Tzialla–Shelat–Thaler–Walfish, "Hyrax").  Reshape the `n` generators into a
`√n × √n` grid `gens : I × J → G`.  The IPA challenge vector `s` is a **full tensor**
(proved earlier: `sCoeff_eq_prod_ite`), so over any split of the rounds it factors as a
rank-1 product `s(i,j) = a_i · b_j`.  A rank-1 coefficient lets the size-`n` MSM be done as a
`√n`-sized **outer** MSM over `√n` **row commitments**:

    ⟨s, G⟩  =  ⟨a, R⟩,     where  R_i = ⟨b, gens(i, ·)⟩   (the i-th row commitment).

If the prover supplies the `√n` row commitments `R` (this is the polynomial commitment —
`√n` group elements instead of `1`), the **verifier computes only the outer `√n`-term MSM**
`⟨a, R⟩`, plus `√n` work to bind `R` to the evaluation.  Total verifier work: `O(√n)`.
Sub-linear, transparent, prime-order.  This is a real, deployed answer.

`msm_product_split` is the exact algebraic identity the verifier relies on; `sCoeff_factors`
discharges the rank-1 hypothesis for the actual IPA challenge vector.
-/
import SuccinctIPA.Experiments
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

open Finset

namespace SuccinctIPA

variable {F : Type*} [Field F] {G : Type*} [AddCommGroup G] [Module F G]

/-- **The √n split (Fubini for a rank-1 MSM).**  A multi-scalar multiplication over a grid
    `I × J` whose coefficient is a product `a_i · b_j` equals the `|I|`-term *outer* MSM over
    the `|J|`-term *row* MSMs.  With `|I| = |J| = √n`, the verifier — given the rows — does
    `√n` work instead of `n`. -/
theorem msm_product_split {I J : Type*} [Fintype I] [Fintype J]
    (a : I → F) (b : J → F) (gens : I × J → G) :
    msm (fun p => a p.1 * b p.2) gens
      = msm a (fun i => msm b (fun j => gens (i, j))) := by
  unfold msm
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [mul_smul])

/-- Concrete balanced reshape: `n = m²`, verifier's outer MSM has `m = √n` terms. -/
theorem hyrax_sqrt_split {m : ℕ} (a b : Fin m → F) (gens : Fin m × Fin m → G) :
    msm (fun p => a p.1 * b p.2) gens
      = msm a (fun i => msm b (fun j => gens (i, j))) :=
  msm_product_split a b gens

variable {k : ℕ}

/-- **The IPA challenge vector really is rank-1 over any split.**  For any bipartition of the
    `k` rounds into `S` and `Sᶜ`, the s-coefficient factors as a product of a part depending
    only on the `S`-bits of `t` and a part depending only on the `Sᶜ`-bits — exactly the
    `a_i · b_j` shape `msm_product_split` needs.  (Balanced `|S| = k/2` gives `√n × √n`.) -/
theorem sCoeff_factors (x : Fin k → F) (S : Finset (Fin k)) (t : Finset (Fin k)) :
    sCoeff x t
      = (∏ j ∈ S, (if j ∈ t then x j else (x j)⁻¹))
        * (∏ j ∈ Sᶜ, (if j ∈ t then x j else (x j)⁻¹)) := by
  rw [sCoeff_eq_prod_ite]
  exact (Finset.prod_mul_prod_compl S _).symm

/-!
## Where this sits, and how far it goes

* **Hyrax** (`msm_product_split`, one split): transparent, prime-order, non-recursive,
  verifier `O(√n)`, commitment `O(√n)`.  A genuine sub-linear dlog verifier.

* **Iterating the split `c` times** (`c`-fold tensor reshape `n = m^c`): the verifier does
  `c` rounds of `m = n^{1/c}` work → `O(c · n^{1/c})`.  Choosing `c = log n` drives this to
  `O(log n)` *terms* — this is exactly the Bulletproofs round structure.  The catch that
  keeps Bulletproofs' verifier linear is that it **folds** the intermediate row commitments
  (the verifier must recompute them: `Θ(n)`) instead of having the prover **send** them
  (Hyrax: `√n` of them).  Send-vs-fold is precisely the commitment-size ↔ verifier-time
  trade, and `msm_product_split` is the hinge.

* So the landscape of transparent prime-order dlog verifiers is a dial, not a wall:
  `n` (Bulletproofs, `O(1)` commitment) … `√n` (Hyrax, `√n` commitment) … and `O(log n)`
  only once you either send `O(n/log n)`-ish data, recurse (accumulation), or change the
  group.  "Succinct (non-linear)" is achievable transparently **today** at `√n`; strictly
  logarithmic transparent prime-order non-recursive remains the wall the experiments hit. -/

end SuccinctIPA
