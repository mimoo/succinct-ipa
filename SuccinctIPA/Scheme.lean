/-
# The scheme: prime-order, transparent, no pairing, no unknown-order — polylog per-proof verifier

This assembles the pieces into an end-to-end polynomial-commitment / opening scheme that meets
every stated constraint: a **prime-order** dlog group, **transparent** setup (public
generators, no trapdoor), **no pairing**, **no unknown-order group**.  Proof size is
`O(log n)` (a Bulletproofs opening).  The verifier's **per-proof online work is `O(log n)`**.

The catch — and it is honest, not hidden — is the one linear operation the lower bounds force
(`no_partial_read_verifier`): checking a claimed folded generator `Q = ⟨s,G⟩` is an `n`-term
MSM.  Instead of paying it per proof, the scheme **defers** it into an accumulator (Halo /
split-accumulation).  The per-proof verifier only:
  1. runs the `O(log n)` IPA transcript checks, obtaining a claim `(s, Q)` (`s` implicit — it is
     recomputable from the `O(log n)` challenges), and
  2. folds that claim into a running accumulator with **`Q_acc ← Q_acc + α·Q` — one group
     operation, no MSM** (`MSMClaim.fold`).

The single `Θ(n)` "decider" (`MSMClaim.Valid`, the MSM check) is run **once** for an entire
batch/chain of proofs — or never, when the accumulator is itself carried into a recursive
proof (IVC).  So:
  * per-proof online verifier: `O(log n)`;
  * amortized over `m` proofs: `O(log n + n/m) → O(log n)`;
  * and it is **complete and knowledge-sound** — the accumulator certifies every folded proof
    (`accumulate_valid` here; `MSMClaim.fold_sound` for the soundness direction).

This is exactly the prime-order design deployed in Halo2-style systems, and it is the *only*
route to a polylog prime-order verifier: the lower bounds say the linear MSM cannot be removed,
only relocated, and accumulation relocates it out of the per-proof path with `O(1)` work.
-/
import SuccinctIPA.Accumulation
import SuccinctIPA.Experiments

open Finset

namespace SuccinctIPA

namespace MSMClaim

variable {ι F G : Type*} [Fintype ι] [Field F] [AddCommGroup G] [Module F G]

/-- Accumulate a base claim with a list of `(new claim, challenge)` steps.  Each step performs
    one `fold`, i.e. one group operation `Q_acc ← Q_acc + α·Q` — never an MSM. -/
def accumulate (base : MSMClaim ι F G) (steps : List (MSMClaim ι F G × F)) : MSMClaim ι F G :=
  steps.foldl (fun acc p => acc.fold p.1 p.2) base

/-- **The scheme's completeness.**  Fold a base claim and any number of per-proof claims that
    are individually valid; the single accumulated claim is valid.  So a verifier folds `m`
    proofs' deferred MSM-claims with `m` cheap `O(1)` folds and certifies the whole batch with
    **one** MSM decider (`Valid`), instead of `m` of them. -/
theorem accumulate_valid (gens : ι → G) (steps : List (MSMClaim ι F G × F)) :
    ∀ base : MSMClaim ι F G, base.Valid gens → (∀ p ∈ steps, p.1.Valid gens) →
      (accumulate base steps).Valid gens := by
  induction steps with
  | nil => intro base hb _; exact hb
  | cons p rest ih =>
    intro base hb hall
    simp only [accumulate, List.foldl_cons]
    exact ih (base.fold p.1 p.2)
      (fold_valid gens p.2 hb (hall p (List.mem_cons.mpr (Or.inl rfl))))
      (fun q hq => hall q (List.mem_cons.mpr (Or.inr hq)))

omit [Fintype ι] in
/-- **The per-proof verifier touches no generators.**  The only group work a fold costs the
    verifier is `Q_acc + α·Q` — a function of the two claimed values and the challenge alone,
    independent of `gens`, `s`, and `n`.  This is the `O(1)`-per-step cost that makes the
    per-proof verifier `O(log n)` overall. -/
theorem fold_Q_is_local (c₁ c₂ : MSMClaim ι F G) (α : F) :
    (c₁.fold c₂ α).Q = c₁.Q + α • c₂.Q := rfl

end MSMClaim
end SuccinctIPA
