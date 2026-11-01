module DASHI.Physics.SeverityGuard.Synthetic.Concrete where

open import Agda.Builtin.Bool using (Bool; true; false)
open import UFTC_Lattice using (Code; Severity; normal; special)
open import DASHI.Physics.SeverityGuard.Core as SG

codeᵇ : Bool → Code
codeᵇ false = normal 0
codeᵇ true = special 4

safeThresholdᵇ : Severity
safeThresholdᵇ = 3

brokenThresholdᵇ : Severity
brokenThresholdᵇ = 4

policyᵇ : SG.SeverityPolicy Bool
policyᵇ =
  record
    { code = codeᵇ
    ; safeThreshold = safeThresholdᵇ
    ; brokenThreshold = brokenThresholdᵇ
    }
