/-
# Soundness

Completeness (`succinct_correct`) says the succinct verifier accepts the *honest*
transcripts.  Soundness is the other half: a *cheating* prover cannot make it accept a
false statement.  For dlog IPA this rests on:

* **Binding** of the Pedersen commitment, which is *exactly* the discrete-log relation
  assumption (`NoDLogRelation`).  Proven here (`pedersen_binding`).

* **Knowledge extraction** by rewinding / special soundness: from a small tree of
  accepting transcripts one reconstructs the witness.  The canonical primitive is the
  Schnorr / Σ-protocol extractor, proven here in full (`schnorr_extract`); IPA soundness
  is its `k`-fold recursive generalization (interface `IPAExtractor` below).

The payoff for *our* problem is `oracle_necessary`: we show formally that if the succinct
verifier trusts the prover's claimed `G₀` *without* the oracle's certificate, it accepts
statements with **no** witness — a concrete forgery.  So `GenOracle.certifies` is not a
convenience; soundness fails without it.  `soundness_transfer` then shows that *with* a
sound oracle, every soundness guarantee of the linear verifier carries over verbatim.
-/
import SuccinctIPA.Protocol
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

open Finset

namespace SuccinctIPA

variable {F : Type*} [Field F]
variable {G : Type*} [AddCommGroup G] [Module F G]

/-! ## Binding = the discrete-log relation assumption -/

section Binding
variable {ι : Type*} [Fintype ι]

/-- `msm` is linear in its scalar argument (the only algebra binding needs). -/
lemma msm_sub (a a' : ι → F) (gens : ι → G) :
    msm (fun i => a i - a' i) gens = msm a gens - msm a' gens := by
  unfold msm
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by rw [sub_smul])

/-- The **discrete-log relation assumption** for a generator vector: the only way to
    write the identity as an integer/scalar combination of the generators is trivially.
    This is precisely what makes the Pedersen commitment binding. -/
def NoDLogRelation (F : Type*) [Field F] {G : Type*} [AddCommGroup G] [Module F G]
    {ι : Type*} [Fintype ι] (gens : ι → G) : Prop :=
  ∀ c : ι → F, msm c gens = 0 → c = 0

/-- **Binding.**  Under the dlog-relation assumption, the Pedersen commitment is
    injective: a commitment determines its opening. -/
theorem pedersen_binding {gens : ι → G} (h : NoDLogRelation F gens)
    {a a' : ι → F} (he : pedersen gens a = pedersen gens a') : a = a' := by
  have hz : msm (fun i => a i - a' i) gens = 0 := by
    rw [msm_sub]; unfold pedersen at he; rw [he, sub_self]
  have hc := h _ hz
  funext i
  have := congrFun hc i
  simpa [sub_eq_zero] using this

end Binding

/-! ## Special soundness: the Schnorr extractor (proven), IPA as its recursion -/

/-- **Special soundness of the Schnorr identification of a dlog `w` with `P = w • g`.**
    Two accepting transcripts `(A, eᵢ, sᵢ)` sharing the first message `A` but with
    distinct challenges `e₁ ≠ e₂` let us *extract* the witness `w = (s₁−s₂)/(e₁−e₂)`.
    This is the atom from which IPA's `k`-round extractor is built by recursion. -/
theorem schnorr_extract (g P A : G) (e₁ e₂ s₁ s₂ : F) (he : e₁ ≠ e₂)
    (h₁ : s₁ • g = A + e₁ • P) (h₂ : s₂ • g = A + e₂ • P) :
    P = ((e₁ - e₂)⁻¹ * (s₁ - s₂)) • g := by
  have hsub : (s₁ - s₂) • g = (e₁ - e₂) • P := by
    rw [sub_smul, sub_smul, h₁, h₂]; abel
  have hne : e₁ - e₂ ≠ 0 := sub_ne_zero.mpr he
  calc
    P = (e₁ - e₂)⁻¹ • ((e₁ - e₂) • P) := by
          rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = (e₁ - e₂)⁻¹ • ((s₁ - s₂) • g) := by rw [hsub]
    _ = ((e₁ - e₂)⁻¹ * (s₁ - s₂)) • g := by rw [smul_smul]

/-- Interface for the full IPA knowledge extractor: from a `(2,2,…,2)`-tree of accepting
    transcripts it returns an opening, *provided* the generators satisfy the dlog-relation
    assumption (so the extracted opening is unique by `pedersen_binding`).  Discharging
    this is the content of the Bulletproofs soundness proof; we expose it as a hypothesis
    rather than re-deriving the multi-round forking here. -/
structure IPAExtractor {F : Type*} [Field F] {G : Type*} [AddCommGroup G] [Module F G]
    {k : ℕ} (gens : Finset (Fin k) → G) where
  binding : NoDLogRelation F gens
  /-- From an accepting final scalar `a` and folded commitment, an opening of the
      original statement.  (Signature kept abstract; the witness type is the opening.) -/
  extract : G → (Finset (Fin k) → F)
  sound : ∀ P₀ : G, pedersen gens (extract P₀) = P₀

/-! ## The oracle is necessary: a forgery, and the soundness transfer -/

variable {k : ℕ}

/-- The succinct verifier's check with the prover's claimed `Q` taken **on trust**
    (no certificate).  This is what you get if you drop `GenOracle.certifies`. -/
def RawSuccinctAccept (Q U P₀ : G) (x : Fin k → F) (z a : F) : Prop :=
  P₀ = a • Q + (a * bSuccinct x z) • U

/-- **The oracle is not optional.**  For any nonzero displacement `Δ` with `a • Δ ≠ 0`,
    there is a transcript the *uncertified* succinct verifier accepts, whose claimed
    generator `Q` is wrong (`Q ≠ G₀`) and which the linear (reference-correct) verifier
    **rejects**.  I.e. trusting `Q` without `GenOracle.certifies` breaks soundness. -/
theorem oracle_necessary
    {gens : Finset (Fin k) → G} {x : Fin k → F} {U : G} {z a : F}
    (Δ : G) (hΔ : a • Δ ≠ 0) :
    ∃ Q P₀ : G,
      RawSuccinctAccept Q U P₀ x z a ∧
      Q ≠ genFinal gens x ∧
      ¬ LinearAccept gens U P₀ x z a := by
  refine ⟨genFinal gens x + Δ,
          a • (genFinal gens x + Δ) + (a * bSuccinct x z) • U, rfl, ?_, ?_⟩
  · -- the claimed generator is wrong
    intro h
    apply hΔ
    have hΔ0 : Δ = 0 := by simpa using h
    rw [hΔ0, smul_zero]
  · -- yet the *true* (linear) verifier rejects it
    intro hc
    apply hΔ
    unfold LinearAccept at hc
    have hb := bSuccinct_eq_bLinear (F := F) x z
    have hsub := sub_eq_zero.mpr hc
    rw [show
        (a • (genFinal gens x + Δ) + (a * bSuccinct x z) • U)
          - (a • genFinal gens x + (a * bLinear x z) • U) = a • Δ
        from by rw [hb, smul_add]; abel] at hsub
    exact hsub

/-- **Soundness transfer.**  With a *sound* oracle (`GenOracle`, whose `certifies` holds),
    any soundness guarantee `R` enjoyed by the linear reference verifier is inherited by
    the succinct verifier — because by `succinct_correct` they accept exactly the same
    transcripts.  Instantiate `R` with "∃ a valid witness" to read it as knowledge soundness. -/
theorem soundness_transfer
    {gens : Finset (Fin k) → G} {x : Fin k → F}
    (Ω : GenOracle gens x) (U P₀ : G) (z a : F)
    (R : Prop) (hbase : LinearAccept gens U P₀ x z a → R) :
    SuccinctAccept Ω U P₀ z a → R :=
  fun h => hbase ((succinct_correct Ω U P₀ z a).mp h)

end SuccinctIPA
