/-
# Lens — the IPA fold *is* an FRI fold: one transcript certifies both
  (`solutions/4-lens.md`; sits between Genesis and Prism)

Genesis certifies the folded-generator MSM with a circuit (fat proof, field-op verifier);
Prism certifies it with a separate sumcheck-reduce + BaseFold-decide over an RS-encoded
generator codeword (fresh challenges, extra rounds).  Lens merges the certificate into the
IPA itself, using two facts this repo already proved:

  * `genFinal_eq_mle` — `G₀ = (∏ⱼ xⱼ⁻¹) · MLE_G(x₁², …, x_k²)`;
  * the IPA generator fold is `x⁻¹·G_lo + x·G_hi = x⁻¹ · (G_lo + x²·G_hi)` —
    an **FRI fold by challenge `x²`** followed by a public scalar.

So the prover Merkle-commits the RS-encoded generator codeword once (transparent setup) and,
at each IPA round, commits the codeword **folded by that round's own challenge** `xⱼ²`.
Fiat–Shamir draws `xⱼ` *after* the round's root, so the fold challenge is fresh randomness —
exactly the commit-then-challenge order FRI soundness needs.  After `k` rounds the codeword
has collapsed to a single group element which — this file's theorems — equals `G₀` up to the
public scalar `∏ xⱼ⁻¹`.  The verifier does the ordinary IPA checks plus `O(λ)` per-round
fold spot-checks against the Merkle roots: no circuit, no separate decide, one transcript.

This file proves the **completeness core** (the algebra that makes the merged transcript
compute the right value):

  * `friFoldStep` / `friFoldAll` — the unnormalized `(1, α)`-fold FRI performs per round;
  * `lens_fold_factor` — one IPA fold = one FRI fold by `x²`, scaled by `x⁻¹`;
  * `friFoldAll_eq_monomialEval` — iterated FRI folding computes the monomial-basis
    multilinear evaluation `∑_b (∏ⱼ αⱼ^{bⱼ}) · f(b)`;
  * `lens_foldAll_eq_genFinal` — the collapsed codeword equals the IPA's folded generator
    `∑_b (∏ⱼ xⱼ^{±1}) · f(b)` — i.e. `G₀` on the cube (`sCoeff`'s tensor, cube-indexed);
  * `lens_reduction` — a certificate for the collapsed value is a certificate for `G₀`.

Soundness (that a committed word far from the code is caught by the spot-checks even though
the fold challenge doubles as the IPA challenge) is the paper-grade part: it is the standard
FRI round-by-round argument (2025/1325 Lemma 7.2 / Thm 7.3) with the single change that the
fold challenge `xⱼ²` is shared with the IPA — still drawn after the round's commitment, so
the proximity argument applies verbatim; the IPA extractor is unaffected (it rewinds on the
same `xⱼ`).  See `solutions/4-lens.md`.
-/
import SuccinctIPA.Prism

open Finset

namespace SuccinctIPA

variable {F : Type*} [Field F]
variable {G : Type*} [AddCommGroup G] [Module F G]
variable {k : ℕ}

/-- The tensor weight of the IPA generator fold, cube-indexed:
    `∏ⱼ (xⱼ if bⱼ else xⱼ⁻¹)` — `sCoeff` with bit-set replaced by boolean tuple. -/
def ipaW (x : Fin k → F) (b : Fin k → Bool) : F :=
  ∏ j, (bif b j then x j else (x j)⁻¹)

/-- The monomial weight `∏ⱼ αⱼ^{bⱼ}` — what iterated `(1, α)`-folding accumulates. -/
def monW (α : Fin k → F) (b : Fin k → Bool) : F :=
  ∏ j, (bif b j then α j else 1)

/-- **One FRI round** in unnormalized form: `f ↦ f_lo + α · f_hi`.  (Prism's `foldStep` is
    the `(1-r, r)` normalized variant; FRI itself uses this `(1, α)` form.) -/
def friFoldStep (α : F) (f : (Fin (k+1) → Bool) → G) : (Fin k → Bool) → G :=
  fun b => f (Fin.cons false b) + α • f (Fin.cons true b)

/-- The full `k`-round FRI fold. -/
def friFoldAll : (k : ℕ) → (Fin k → F) → ((Fin k → Bool) → G) → G
  | 0,   _, f => f (fun i => i.elim0)
  | k+1, α, f => friFoldAll k (Fin.tail α) (friFoldStep (α 0) f)

/-- **One IPA generator-fold round** on the cube: `f ↦ x⁻¹·f_lo + x·f_hi`. -/
def ipaFoldStep (x : F) (f : (Fin (k+1) → Bool) → G) : (Fin k → Bool) → G :=
  fun b => x⁻¹ • f (Fin.cons false b) + x • f (Fin.cons true b)

def ipaFoldAll : (k : ℕ) → (Fin k → F) → ((Fin k → Bool) → G) → G
  | 0,   _, f => f (fun i => i.elim0)
  | k+1, x, f => ipaFoldAll k (Fin.tail x) (ipaFoldStep (x 0) f)

/-- **The Lens identity, one round**: the IPA fold *is* the FRI fold by `x²`, rescaled by
    the public scalar `x⁻¹`.  This is what lets one committed transcript serve both roles. -/
theorem lens_fold_factor (x : F) (hx : x ≠ 0) (f : (Fin (k+1) → Bool) → G) :
    ipaFoldStep x f = fun b => x⁻¹ • friFoldStep (x^2) f b := by
  funext b
  unfold ipaFoldStep friFoldStep
  rw [smul_add, smul_smul]
  congr 2
  rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]

/-- The monomial weight factors along the first coordinate. -/
theorem monW_cons (α : Fin (k+1) → F) (c0 : Bool) (b : Fin k → Bool) :
    monW α (Fin.cons c0 b) = (bif c0 then α 0 else 1) * monW (Fin.tail α) b := by
  unfold monW
  rw [Fin.prod_univ_succ, Fin.cons_zero]
  simp only [Fin.cons_succ]
  rfl

/-- The IPA tensor weight factors along the first coordinate. -/
theorem ipaW_cons (x : Fin (k+1) → F) (c0 : Bool) (b : Fin k → Bool) :
    ipaW x (Fin.cons c0 b) = (bif c0 then x 0 else (x 0)⁻¹) * ipaW (Fin.tail x) b := by
  unfold ipaW
  rw [Fin.prod_univ_succ, Fin.cons_zero]
  simp only [Fin.cons_succ]
  rfl

/-- **Iterated FRI folding computes the monomial-basis multilinear evaluation.**  This is
    the coefficient-view counterpart of Prism's `foldAll_eq_mleEval`. -/
theorem friFoldAll_eq_monomialEval :
    ∀ (k : ℕ) (α : Fin k → F) (f : (Fin k → Bool) → G),
      friFoldAll k α f = ∑ b : Fin k → Bool, monW α b • f b := by
  intro k
  induction k with
  | zero =>
    intro α f
    simp only [friFoldAll, Fintype.sum_unique, monW, Finset.univ_eq_empty,
               Finset.prod_empty, one_smul]
    exact congrArg f (funext fun i => i.elim0)
  | succ k ih =>
    intro α f
    show friFoldAll k (Fin.tail α) (friFoldStep (α 0) f)
        = ∑ b : Fin (k+1) → Bool, monW α b • f b
    rw [ih,
        ← Equiv.sum_comp (consEquivBool k) (fun c => monW α c • f c),
        Fintype.sum_prod_type, Fintype.sum_bool]
    show ∑ b, monW (Fin.tail α) b • friFoldStep (α 0) f b
        = (∑ b, monW α (Fin.cons true b) • f (Fin.cons true b))
          + ∑ b, monW α (Fin.cons false b) • f (Fin.cons false b)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    show monW (Fin.tail α) b
          • (f (Fin.cons false b) + α 0 • f (Fin.cons true b))
        = monW α (Fin.cons true b) • f (Fin.cons true b)
          + monW α (Fin.cons false b) • f (Fin.cons false b)
    rw [monW_cons, monW_cons, smul_add, smul_smul]
    simp only [cond_true, cond_false, one_mul]
    rw [mul_comm (monW (Fin.tail α) b) (α 0)]
    abel

/-- **The collapsed codeword is the folded generator.**  Iterating the IPA fold computes
    exactly `∑_b (∏ⱼ xⱼ^{±1}) · f(b)` — the cube-indexed `genFinal`.  Combined with
    `lens_fold_factor`, the FRI transcript folded by `x₁², …, x_k²` and rescaled by the
    public `∏ xⱼ⁻¹` lands on `G₀`: the merged protocol is complete. -/
theorem lens_foldAll_eq_genFinal :
    ∀ (k : ℕ) (x : Fin k → F) (f : (Fin k → Bool) → G),
      ipaFoldAll k x f = ∑ b : Fin k → Bool, ipaW x b • f b := by
  intro k
  induction k with
  | zero =>
    intro x f
    simp only [ipaFoldAll, Fintype.sum_unique, ipaW, Finset.univ_eq_empty,
               Finset.prod_empty, one_smul]
    exact congrArg f (funext fun i => i.elim0)
  | succ k ih =>
    intro x f
    show ipaFoldAll k (Fin.tail x) (ipaFoldStep (x 0) f)
        = ∑ b : Fin (k+1) → Bool, ipaW x b • f b
    rw [ih,
        ← Equiv.sum_comp (consEquivBool k) (fun c => ipaW x c • f c),
        Fintype.sum_prod_type, Fintype.sum_bool]
    show ∑ b, ipaW (Fin.tail x) b • ipaFoldStep (x 0) f b
        = (∑ b, ipaW x (Fin.cons true b) • f (Fin.cons true b))
          + ∑ b, ipaW x (Fin.cons false b) • f (Fin.cons false b)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    show ipaW (Fin.tail x) b
          • ((x 0)⁻¹ • f (Fin.cons false b) + x 0 • f (Fin.cons true b))
        = ipaW x (Fin.cons true b) • f (Fin.cons true b)
          + ipaW x (Fin.cons false b) • f (Fin.cons false b)
    rw [ipaW_cons, ipaW_cons, smul_add, smul_smul, smul_smul]
    simp only [cond_true, cond_false]
    rw [mul_comm (ipaW (Fin.tail x) b) (x 0),
        mul_comm (ipaW (Fin.tail x) b) ((x 0)⁻¹)]
    abel

/-- **The Lens reduction**: a certificate that the (per-round-committed, spot-checked)
    collapsed codeword equals `W` is a certificate for the IPA's folded-generator claim. -/
theorem lens_reduction (x : Fin k → F) (gens : (Fin k → Bool) → G) (W : G)
    (hcert : W = ipaFoldAll k x gens) :
    W = ∑ b : Fin k → Bool, ipaW x b • gens b := by
  rw [hcert, lens_foldAll_eq_genFinal]

end SuccinctIPA
