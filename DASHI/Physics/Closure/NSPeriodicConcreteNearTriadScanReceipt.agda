module DASHI.Physics.Closure.NSPeriodicConcreteNearTriadScanReceipt where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Status mirror of the finite full linearized near-triad factor scan.
------------------------------------------------------------------------

nearScanCutoffCount nearScanSamplesPerCutoff : Nat
nearScanCutoffCount = 2
nearScanSamplesPerCutoff = 8

nearLowHighIntegerCandidate : Nat
nearLowHighIntegerCandidate = 1

nearHighLowIntegerCandidate : Nat
nearHighLowIntegerCandidate = 1

nearHighHighIntegerCandidate : Nat
nearHighHighIntegerCandidate = 1

nearHighHighCandidateRegression : nearHighHighIntegerCandidate ≡ 1
nearHighHighCandidateRegression = refl

finiteNearScanIsProductTheorem : Bool
finiteNearScanIsProductTheorem = false

nearCandidateConstantsCutoffUniform : Bool
nearCandidateConstantsCutoffUniform = false

universalNearAbsorptionFromFiniteScan : Bool
universalNearAbsorptionFromFiniteScan = false
