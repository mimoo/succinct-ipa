/-
# Prism — folding a Reed–Solomon encoding of the generators computes the MLE
  (`solutions/3-prism.md`)

Prism discharges the linear MSM `G₀ = ⟨s,G⟩` not by delegating it to a circuit (Atlas's
Kedlaya–Umans table, Genesis's in-circuit seed derivation) but by proving it as a
**multilinear evaluation of the fixed generator polynomial** via a group-native BaseFold
(Eagen–Gabizon, ePrint 2025/1325, §7).  `Experiments.genFinal_eq_mle` already isolated the
key fact — the folded generator *is* an MLE of the public generators; here we verify the
**completeness core of `decide`**: the object BaseFold actually computes.

BaseFold/FRI works by *folding*: given a codeword indexed by the boolean cube, each round
`fold_{r₀}` collapses one variable by the low/high combination `(1-r₀)·low + r₀·high`
(the paper's `fold_x(f) = (1-x)f₀ + x f₁`, §7.1).  The encoding `RS₀(G)` is chosen precisely
so that folding tracks multilinear evaluation, i.e. after `k` rounds the codeword has
collapsed to the single group element `Ĝ(r₁,…,r_k)` (2025/1325 §7.1, "the crucial property
`f_k ≡ Ĥ(r₁,…,r_k)`").  This file proves that identity:

  * `foldStep`      — one BaseFold round `(1-r₀)·low + r₀·high`, over the group `G`.
  * `foldAll`       — the full `k`-round fold.
  * `foldAll_eq_mleEval` — **repeated folding = multilinear evaluation** `Ĝ(r)`.  This is the
    completeness backbone of `decide`: the honest prover's folded codeword lands exactly on
    the value `reduce` needs.
  * `prism_reduction` — a certificate `W = foldAll r gens` certifies the decide-claim
    `W = Ĝ(r)` (the Prism analogue of `Genesis.genesis_reduction`).
  * `mleEval_eq_msm` — the decide target keeps the `⟨·,gens⟩` shape (`Experiments.mleG_is_msm`):
    conservation of linear work still holds — Prism *relocates* the MSM into a committed
    codeword the prover folds, rather than removing it.  What buys succinctness is that the
    verifier checks the fold against a preprocessed commitment, doing only `O(λ log²n)` work.

The soundness half — that a codeword far from `RS₀(G)` is caught by the FRI consistency
queries (2025/1325 Lemma 7.2, Thm 7.3) — rests on Reed–Solomon proximity gaps; the *sumcheck*
half of BaseFold is exactly the round engine already proven in `Delegation.lean`
(`sumcheck_round_complete`, `disagreement_is_root`, `cheating_caught`).  We record the
completeness core here and cite the paper for the proximity analysis, as `2-genesis.md`
cites the GKR wiring analysis.
-/
import SuccinctIPA.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Abel

open Finset

namespace SuccinctIPA

variable {F : Type*} [Field F]
variable {G : Type*} [AddCommGroup G] [Module F G]
variable {k : ℕ}

/-- The multilinear `eq`-weight of a cube point `b` at evaluation point `r`:
    `∏_j (r_j if b_j else 1 - r_j)` — the Lagrange/interpolation weight the fold produces. -/
def eqW (r : Fin k → F) (b : Fin k → Bool) : F :=
  ∏ j, (bif b j then r j else 1 - r j)

/-- Multilinear extension (evaluation basis): the value at `r` of the MLE of the function
    `f` given by its values on the boolean cube.  For `f = gens` this is `Ĝ(r)` — the object
    `decide` proves, and (by `genFinal_eq_mle`) the folded generator `G₀` up to a scalar. -/
def mleEval (f : (Fin k → Bool) → G) (r : Fin k → F) : G :=
  ∑ b : Fin k → Bool, eqW r b • f b

/-- **One BaseFold/FRI fold round** over the group: collapse the first variable by
    `(1-r₀)·low + r₀·high` (the paper's `fold_{r₀}(f) = (1-r₀)f₀ + r₀ f₁`, §7.1).
    Well-defined for arbitrary group-valued functions, exactly as in 2025/1325 §7.1. -/
def foldStep (r₀ : F) (f : (Fin (k+1) → Bool) → G) : (Fin k → Bool) → G :=
  fun b => (1 - r₀) • f (Fin.cons false b) + r₀ • f (Fin.cons true b)

/-- The full `k`-round fold: apply `foldStep` once per variable, consuming `r₀, r₁, …`.
    After all rounds a single group element remains — the FRI codeword collapsed to a point. -/
def foldAll : (k : ℕ) → (Fin k → F) → ((Fin k → Bool) → G) → G
  | 0,   _, f => f (fun i => i.elim0)
  | k+1, r, f => foldAll k (Fin.tail r) (foldStep (r 0) f)

/-- Reindexing the cube: a length-`k+1` cube point is a first bit plus a length-`k` point.
    Definitionally `Fin.cons`, so it commutes with `foldStep`/`eqW` splitting. -/
def consEquivBool (k : ℕ) : (Bool × (Fin k → Bool)) ≃ (Fin (k+1) → Bool) where
  toFun p := Fin.cons p.1 p.2
  invFun c := (c 0, Fin.tail c)
  left_inv := by rintro ⟨c0, b⟩; simp [Fin.tail_cons]
  right_inv := by intro c; simp [Fin.cons_self_tail]

/-- The `eq`-weight factors along the first coordinate: this is why one fold round tracks
    one variable of the multilinear evaluation. -/
theorem eqW_cons (r : Fin (k+1) → F) (c0 : Bool) (b : Fin k → Bool) :
    eqW r (Fin.cons c0 b) = (bif c0 then r 0 else 1 - r 0) * eqW (Fin.tail r) b := by
  unfold eqW
  rw [Fin.prod_univ_succ, Fin.cons_zero]
  simp only [Fin.cons_succ]
  rfl

@[simp] theorem foldStep_apply (r₀ : F) (f : (Fin (k+1) → Bool) → G) (b : Fin k → Bool) :
    foldStep r₀ f b = (1 - r₀) • f (Fin.cons false b) + r₀ • f (Fin.cons true b) := rfl

/-- **The completeness core of Prism's `decide`.**  Iterating the BaseFold/FRI fold with
    challenges `r₁,…,r_k` over the (honest) generator codeword computes exactly the multilinear
    evaluation `Ĝ(r₁,…,r_k)`.  This is 2025/1325 §7.1's "crucial property `f_k ≡ Ĥ(r)`" — the
    guarantee that the honest prover's collapsed codeword equals the value `reduce` asks for. -/
theorem foldAll_eq_mleEval :
    ∀ (k : ℕ) (r : Fin k → F) (f : (Fin k → Bool) → G),
      foldAll k r f = mleEval f r := by
  intro k
  induction k with
  | zero =>
    intro r f
    simp only [foldAll, mleEval, Fintype.sum_unique, eqW, Finset.univ_eq_empty,
               Finset.prod_empty, one_smul]
    exact congrArg f (funext fun i => i.elim0)
  | succ k ih =>
    intro r f
    show foldAll k (Fin.tail r) (foldStep (r 0) f) = mleEval f r
    rw [ih]
    unfold mleEval
    rw [← Equiv.sum_comp (consEquivBool k) (fun c => eqW r c • f c),
        Fintype.sum_prod_type, Fintype.sum_bool]
    show ∑ b, eqW (Fin.tail r) b • foldStep (r 0) f b
        = (∑ b, eqW r (Fin.cons true b) • f (Fin.cons true b))
          + ∑ b, eqW r (Fin.cons false b) • f (Fin.cons false b)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [eqW_cons, eqW_cons, foldStep_apply, smul_add, smul_smul, smul_smul]
    simp only [cond_true, cond_false]
    rw [mul_comm (eqW (Fin.tail r) b) (1 - r 0), mul_comm (eqW (Fin.tail r) b) (r 0)]
    abel

/-- **The Prism reduction** (analogue of `Genesis.genesis_reduction`).  A certificate that the
    folded codeword equals `W` *is* a certificate for the decide-claim `W = Ĝ(r)`; the entire
    content is the fold-to-evaluation identity, so no proximity/soundness property is used for
    this completeness direction. -/
theorem prism_reduction (r : Fin k → F) (gens : (Fin k → Bool) → G) (W : G)
    (hcert : W = foldAll k r gens) : W = mleEval gens r := by
  rw [hcert, foldAll_eq_mleEval]

/-- **Conservation of linear work still holds.**  The decide target `Ĝ(r)` is again an `msm`
    over the public generators (`Experiments.mleG_is_msm`): folding does not *remove* the
    linear work, it relocates it into a committed codeword the prover folds.  Succinctness
    comes from the verifier checking that fold against a preprocessed commitment in
    `O(λ log²n)`, not from the algebra collapsing. -/
theorem mleEval_eq_msm (f : (Fin k → Bool) → G) (r : Fin k → F) :
    mleEval f r = msm (eqW r) f := rfl

/-- The fold is `F`-linear in the codeword (hence a Merkle commitment to `RS₀(G)` binds the
    evaluation).  Mirrors `Experiments.mleG_add`. -/
theorem mleEval_add (f g : (Fin k → Bool) → G) (r : Fin k → F) :
    mleEval (fun b => f b + g b) r = mleEval f r + mleEval g r := by
  unfold mleEval
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun b _ => by rw [smul_add])

end SuccinctIPA
