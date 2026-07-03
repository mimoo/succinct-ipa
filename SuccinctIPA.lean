/-
# Succinct verifiers for dlog inner-product-argument PCS

A Lean scaffolding that pins down what "a succinct verifier for an IPA-style,
discrete-log polynomial commitment" can and cannot be, and certifies one solution.

* `SuccinctIPA.Basic`    — group/field setting, inner products, the MSM (the costly op).
* `SuccinctIPA.SVector`  — the s-vector and the proven succinctness identity
                           `bSuccinct_eq_bLinear` (`O(log n)` product = `Θ(n)` sum).
* `SuccinctIPA.Protocol` — linear vs. succinct verifier, the generator-commitment oracle,
                           and `succinct_correct`: succinct ⇔ linear under the oracle.
-/
import SuccinctIPA.Basic
import SuccinctIPA.SVector
import SuccinctIPA.Protocol
import SuccinctIPA.Soundness
import SuccinctIPA.Experiments
import SuccinctIPA.Accumulation
import SuccinctIPA.DARK
import SuccinctIPA.DlogLayer
import SuccinctIPA.Hyrax
import SuccinctIPA.Dory
import SuccinctIPA.LowerBound
import SuccinctIPA.Scheme
import SuccinctIPA.Nova
import SuccinctIPA.Delegation
import SuccinctIPA.Genesis
import SuccinctIPA.Prism
