/-
# The s-vector and the succinctness identity

In a `k`-round IPA over a vector of length `n = 2^k`, the verifier's final check
refers to a scalar vector `s ∈ Fⁿ` built from the round challenges `x₁,…,x_k`:

    s_i = Π_j  (x_j   if bit j of i is set, else x_j⁻¹).

Two facts about `s` govern succinctness:

* `s` is the coefficient vector of the degree-(n−1) polynomial
      g(X) = Π_j (x_j⁻¹ + x_j · X^{2^{j-1}}),
  so the inner product `⟨s, (z⁰,…,z^{n-1})⟩ = g(z)` can be evaluated in `O(k) = O(log n)`
  time — even though writing `s` out takes `Θ(n)`.  **This is what makes the `b₀` part of
  the verifier succinct, and it is what we prove below.**

* The multi-scalar multiplication `⟨s, G⟩ = Σ s_i Gᵢ` has *no* such shortcut for
  unstructured generators `G` — that is the linear cost, isolated in `Protocol.lean`.

We index the `n = 2^k` coordinates by subsets `t : Finset (Fin k)` (a bit-vector
of length `k`), which sidesteps `Nat.testBit` bookkeeping: the integer coordinate
is `Σ_{j∈t} 2^j` and the set bits are exactly the elements of `t`.
-/
import SuccinctIPA.Basic
import Mathlib.Tactic.Ring

open Finset

namespace SuccinctIPA

variable {F : Type*} [Field F]
variable {k : ℕ}

/-- The s-vector entry for the coordinate whose set bits are `t`:
    a factor `x j` for every round `j ∈ t`, and `x j⁻¹` for every round `j ∉ t`. -/
def sCoeff (x : Fin k → F) (t : Finset (Fin k)) : F :=
  (∏ j ∈ t, x j) * (∏ j ∈ tᶜ, (x j)⁻¹)

/-- The integer coordinate (in `0 … 2^k − 1`) named by the bit-set `t`. -/
def coord (t : Finset (Fin k)) : ℕ := ∑ j ∈ t, 2 ^ (j : ℕ)

/-- **Succinct (product) form** of the verifier's `b₀` scalar:
    `g(z) = Π_j (x_j⁻¹ + x_j · z^{2^{j-1}})`, computable in `O(k)`. -/
def bSuccinct (x : Fin k → F) (z : F) : F :=
  ∏ j : Fin k, ((x j)⁻¹ + x j * z ^ (2 ^ (j : ℕ)))

/-- **Linear (expanded) form** of `b₀`: `⟨s, (z^coord)⟩ = Σ_i s_i z^i`,
    the sum the naive linear-time verifier would evaluate. -/
def bLinear (x : Fin k → F) (z : F) : F :=
  ∑ t : Finset (Fin k), sCoeff x t * z ^ coord t

/-- **The succinctness identity.**  The `O(k)` product form and the `Θ(2^k)` expanded
    sum coincide.  Hence a verifier may compute `b₀` via `bSuccinct` (log-time) and get
    exactly the value the linear verifier would.  Proof: distribute the product of
    binomials (`Finset.prod_add`), then collect powers of `z`. -/
theorem bSuccinct_eq_bLinear (x : Fin k → F) (z : F) :
    bSuccinct x z = bLinear x z := by
  unfold bSuccinct bLinear
  -- Reorder each factor as `(z-term) + (inverse-term)` to match `Finset.prod_add`.
  have hcomm : ∀ j : Fin k,
      (x j)⁻¹ + x j * z ^ (2 ^ (j : ℕ)) = x j * z ^ (2 ^ (j : ℕ)) + (x j)⁻¹ := by
    intro j; ring
  simp only [hcomm]
  rw [Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  unfold sCoeff coord
  rw [Finset.compl_eq_univ_sdiff]
  ring
