import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Gadgets.Equality
import Clean.Gadgets.Boolean
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Genesis layer gadgets — formally verified circuits for the Genesis IPA verifier

These are the layer relations of the Genesis delegated circuit
(see `succinct-ipa/solutions/2-genesis.md` and `sage/3-genesis-e2e.sage`):

* `HashRound`      — one toy-hash round `out = (x + rc)^5`
* `SquareMulStep`  — one square-and-multiply step of a fixed-exponent chain,
                     with a *public* bit `b`: `out = acc² · base^b`
* `CondMulConst`   — one constant-time Tonelli–Shanks conditional step:
                     given `t ∈ {1,-1}`, `out = w · (1 + (1-t)/2 · (z-1))`,
                     i.e. `out = w` if `t = 1` else `w·z`
* `QrBit`          — Legendre symbol to selector bit: `q = (1+l)/2 ∈ {0,1}`
* `RcbAdd`         — complete projective point addition for `y² = x³ + b`
                     (Renes–Costello–Batina 2015, Algorithm 7, `a = 0`),
                     the point operation of the MSM fold

Each gadget's `Spec` is a plain Lean function (`hashRoundSpec`, `rcbSpec`, …);
the Sage implementation evaluates the *same* functions, and the `#eval` test
vectors at the bottom (over the Pallas base field) pin the two together.
Soundness = "any witness satisfying the constraints computes the spec";
completeness = "the honest witness satisfies the constraints".
-/

namespace Gadgets.Genesis

/-! ## Plain spec functions (mirrored verbatim by the Sage layers).
Defined over any commutative ring so they can be `#eval`-ed over
`ZMod pallasP` for the Lean↔Sage test vectors. -/

section Specs
variable {R : Type} [CommRing R] [DecidableEq R]

@[circuit_norm]
def hashRoundSpec (rc x : R) : R := (x + rc)^5

@[circuit_norm]
def squareMulSpec (b : Bool) (acc base : R) : R :=
  if b then acc^2 * base else acc^2

@[circuit_norm]
def condMulSpec (z w t : R) : R := if t = 1 then w else w * z

@[circuit_norm]
def qrBitSpec (l : R) : R := if l = 1 then 1 else 0

/-- Complete projective addition, `a = 0`, `b3 = 3b`
    (RCB'15 Alg. 7) — exactly the chain in `sage/3-genesis-e2e.sage`. -/
@[circuit_norm]
def rcbSpec (b3 x1 y1 z1 x2 y2 z2 : R) : R × R × R :=
  let t0 := x1 * x2
  let t1 := y1 * y2
  let t2 := z1 * z2
  let t3 := (x1 + y1) * (x2 + y2) - t0 - t1
  let t4 := (y1 + z1) * (y2 + z2) - t1 - t2
  let t5 := (x1 + z1) * (x2 + z2) - t0 - t2
  let b3t2 := b3 * t2
  let zz := t1 + b3t2
  let t1m := t1 - b3t2
  let yy := b3 * t5
  let x3 := t3 * t1m - t4 * yy
  let t0'3 := t0 + t0 + t0
  let y3 := yy * t0'3 + t1m * zz
  let z3 := zz * t4 + t0'3 * t3
  (x3, y3, z3)

end Specs

/-- Helper: in any commutative ring, `-1 = 1` forces `2 = 0` (char 2). -/
theorem two_eq_zero_of_neg_one_eq_one {R : Type} [CommRing R]
    (h : (-1 : R) = 1) : (2 : R) = 0 := by
  calc (2 : R) = 1 + 1 := by ring
    _ = -1 + 1 := by rw [h]
    _ = 0 := by ring

variable {F : Type} [FiniteField F] [DecidableEq F]

/-! ## Gadget 1: hash round `out = (x + rc)^5` -/

namespace HashRound

def main (rc : F) (x : Expression F) : Circuit F (Expression F) := do
  let u2 <== (x + rc) * (x + rc)
  let u4 <== u2 * u2
  let out <== u4 * (x + rc)
  return out

def circuit (rc : F) : FormalCircuit F field field where
  main := main rc
  Spec (x : F) (out : F) := out = hashRoundSpec rc x
  soundness := by
    intro offset env input_var input h_input h_assumptions h_constraints
    simp only [circuit_norm, main, hashRoundSpec] at *
    obtain ⟨h1, h2, h3⟩ := h_constraints
    rw [h_input] at *
    rw [h3, h2, h1]
    ring
  completeness := by
    simp_all only [circuit_norm, main]

end HashRound

/-! ## Gadget 2: square-and-multiply steps of a fixed-exponent chain.

The exponent's bits are *public structure*, so — exactly as in the Sage
circuit builder — a bit-0 step emits a `SquareStep` layer and a bit-1 step
emits a `SquareMulStep` layer.  No in-circuit branching. -/

namespace SquareStep

def main (input : Expression F) : Circuit F (Expression F) := do
  let sq <== input * input
  return sq

def circuit : FormalCircuit F field field where
  main := main
  Spec (acc : F) (out : F) := out = squareMulSpec false acc 1
  soundness := by
    intro offset env input_var input h_input h_assumptions h_constraints
    simp only [circuit_norm, main, squareMulSpec] at *
    rw [h_constraints, h_input]
    ring
  completeness := by
    simp_all only [circuit_norm, main]

end SquareStep

namespace SquareMulStep

def main (input : Expression F × Expression F) :
    Circuit F (Expression F) := do
  let sq <== input.1 * input.1
  let out <== sq * input.2
  return out

def circuit : FormalCircuit F fieldPair field where
  main := main
  Spec (input : F × F) (out : F) := out = squareMulSpec true input.1 input.2
  soundness := by
    rintro _ _ ⟨_, _⟩ ⟨_, _⟩ h_env h_assumptions h_hold
    simp only [circuit_norm, main, squareMulSpec] at h_env h_hold ⊢
    rcases h_env.symm with ⟨_, _⟩
    obtain ⟨h1, h2⟩ := h_hold
    simp_all only
    ring
  completeness := by
    simp_all only [circuit_norm, main]

end SquareMulStep

/-! ## Gadget 3: Tonelli–Shanks conditional multiply-by-constant

`t` is a ±1 test value; `b = (1-t)/2 ∈ {0,1}`; `out = w·(1 + b·(z-1))`.
Assumes `t ∈ {1,-1}` and characteristic ≠ 2. -/

namespace CondMulConst

/-- The circuit computes this closed form; `condMul_spec_ite` below gives it
its if-then-else meaning under the ±1 assumption. -/
@[circuit_norm]
def closedForm (z w t : F) : F := w * (1 + (1 - t) * (2 : F)⁻¹ * (z - 1))

/-- **Meaning of the closed form**: for `t ∈ {1,-1}` (and char ≠ 2) the
Tonelli–Shanks conditional step is exactly `if t = 1 then w else w·z`. -/
theorem condMul_spec_ite (z w t : F) (hpm : t = 1 ∨ t = -1)
    (h2 : (2 : F) ≠ 0) : closedForm z w t = condMulSpec z w t := by
  rcases hpm with h | h <;> subst h
  · unfold closedForm condMulSpec
    rw [if_pos rfl]
    ring
  · simp only [closedForm, condMulSpec,
      if_neg (show (-1 : F) ≠ 1 from
        fun hh => h2 (two_eq_zero_of_neg_one_eq_one hh))]
    have h21 : (1 - (-1 : F)) * (2 : F)⁻¹ = 1 := by
      rw [show (1 - (-1 : F)) = 2 from by ring, mul_inv_cancel₀ h2]
    calc w * (1 + (1 - (-1 : F)) * (2 : F)⁻¹ * (z - 1))
        = w * (1 + 1 * (z - 1)) := by rw [h21]
      _ = w * z := by ring

def main (z : F) (input : Expression F × Expression F) :
    Circuit F (Expression F) := do
  let b <== (1 - input.2) * ((2 : F)⁻¹ : F)
  let out <== input.1 * (1 + b * (z - 1))
  return out

def circuit (z : F) : FormalCircuit F fieldPair field where
  main := main z
  Spec (input : F × F) (out : F) := out = closedForm z input.1 input.2
  soundness := by
    rintro _ _ ⟨_, _⟩ ⟨_, _⟩ h_env h_assumptions h_hold
    simp only [circuit_norm, main, closedForm] at h_env h_hold ⊢
    rcases h_env.symm with ⟨_, _⟩
    obtain ⟨hb, hout⟩ := h_hold
    simp_all only
    ring
  completeness := by
    simp_all only [circuit_norm, main]

end CondMulConst

/-! ## Gadget 4: Legendre symbol to selector bit `q = (1+l)/2` -/

namespace QrBit

def main (input : Expression F) : Circuit F (Expression F) := do
  let q <== (1 + input) * ((2 : F)⁻¹ : F)
  return q

def circuit : FormalCircuit F field field where
  main := main
  Assumptions (l : F) := (l = 1 ∨ l = -1) ∧ (2 : F) ≠ 0
  Spec (l : F) (q : F) := q = qrBitSpec l
  soundness := by
    intro offset env input_var input h_input h_assumptions h_constraints
    simp only [circuit_norm, main, qrBitSpec] at *
    obtain ⟨hpm, h2⟩ := h_assumptions
    rw [h_input] at *
    rcases hpm with h1 | hm1
    · subst h1
      rw [if_pos rfl, h_constraints]
      rw [show (1 + (1 : F)) = 2 from by ring, mul_inv_cancel₀ h2]
    · subst hm1
      rw [if_neg (show (-1 : F) ≠ 1 from
            fun h => h2 (two_eq_zero_of_neg_one_eq_one h)),
          h_constraints]
      ring
  completeness := by
    simp_all only [circuit_norm, main]

end QrBit

/-! ## Gadget 5: complete projective point addition (RCB'15 Alg. 7, a = 0) -/

structure TwoPoints (F : Type) where
  x1 : F
  y1 : F
  z1 : F
  x2 : F
  y2 : F
  z2 : F
deriving ProvableStruct

namespace RcbAdd

def main (b3 : F) (input : Var TwoPoints F) :
    Circuit F (Var fieldTriple F) := do
  let { x1, y1, z1, x2, y2, z2 } := input
  let t0 <== x1 * x2
  let t1 <== y1 * y2
  let t2 <== z1 * z2
  let t3 <== (x1 + y1) * (x2 + y2)
  let t4 <== (y1 + z1) * (y2 + z2)
  let t5 <== (x1 + z1) * (x2 + z2)
  let t3' := t3 - t0 - t1
  let t4' := t4 - t1 - t2
  let t5' := t5 - t0 - t2
  let zz := t1 + b3 * t2
  let t1m := t1 - b3 * t2
  let x3a <== t3' * t1m
  let x3b <== t4' * (b3 * t5')
  let y3a <== (b3 * t5') * (t0 + t0 + t0)
  let y3b <== t1m * zz
  let z3a <== zz * t4'
  let z3b <== (t0 + t0 + t0) * t3'
  return (x3a - x3b, y3a + y3b, z3a + z3b)

def circuit (b3 : F) : FormalCircuit F TwoPoints fieldTriple where
  main := main b3
  Spec (input : TwoPoints F) (out : F × F × F) :=
    out = rcbSpec b3 input.x1 input.y1 input.z1 input.x2 input.y2 input.z2
  soundness := by
    circuit_proof_start
    obtain ⟨h0, h1, h2, h3, h4, h5, hxa, hxb, hya, hyb, hza, hzb⟩ := h_holds
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [h0, h1, h2, h3, h4, h5, hxa, hxb, hya, hyb, hza, hzb] <;>
      ring
  completeness := by
    simp_all only [circuit_norm, main]

end RcbAdd

/-! ## Test vectors over the Pallas base field

These pin the Lean-verified specs to the Sage implementation: the Sage
benchmark evaluates the same functions on the same inputs and asserts equal
outputs (`clean_vectors_check` in `sage/3-genesis-e2e.sage`). -/

def pallasP : ℕ :=
  28948022309329048855892746252171976963363056481941560715954676764349967630337

abbrev Fpal := ZMod pallasP

-- vector 1: hash round, rc = 7, x = 3  →  (3+7)^5 = 100000
#eval (hashRoundSpec (7 : Fpal) 3 : Fpal)
-- vector 2: square-and-multiply, b = true, acc = 5, base = 11  →  275
#eval (squareMulSpec true (5 : Fpal) 11 : Fpal)
-- vector 3: conditional multiply, z = 9, w = 4, t = -1  →  36
#eval (condMulSpec (9 : Fpal) 4 (-1) : Fpal)
-- vector 4: qr bit, l = -1  →  0
#eval (qrBitSpec (-1 : Fpal) : Fpal)
-- vector 5: RCB addition, b3 = 15, P = (1,2,1), Q = (3,4,1)
#eval (rcbSpec (15 : Fpal) 1 2 1 3 4 1)

end Gadgets.Genesis
