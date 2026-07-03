/-
# Succinct IPA — Basic algebraic setting

We model a discrete-log group as a vector space `G` over a scalar field `F`
(an `AddCommGroup` with a `Module F` structure — the additive notation matches
elliptic-curve point addition, and `•` is scalar multiplication `[a]·P`).

Nothing here assumes the discrete-log problem is *hard*: hardness is only needed
for *soundness* (knowledge-extraction), not for the *completeness* identities that
make a verifier succinct.  This file fixes notation for vectors, inner products and
multi-scalar multiplications (MSMs); the MSM is exactly the operation whose cost we
are trying to make sublinear.
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.BooleanAlgebra

open Finset

namespace SuccinctIPA

variable {F : Type*} [Field F]
variable {G : Type*} [AddCommGroup G] [Module F G]

/-- Scalar inner product `⟪a, b⟫ = Σ aᵢ bᵢ`. -/
def dot {ι : Type*} [Fintype ι] (a b : ι → F) : F :=
  ∑ i, a i * b i

/-- Multi-scalar multiplication `⟨a, P⟩ = Σ aᵢ • Pᵢ` — a single MSM.
    Computing one of these over `n` generators is the linear cost we want to avoid. -/
def msm {ι : Type*} [Fintype ι] (a : ι → F) (P : ι → G) : G :=
  ∑ i, a i • P i

/-- A Pedersen vector commitment `Com(a) = ⟨a, G⟩ (+ blinding)`.
    Here the blinding term is folded into `H` and left to the caller. -/
def pedersen {ι : Type*} [Fintype ι] (gens : ι → G) (a : ι → F) : G :=
  msm a gens

end SuccinctIPA
