module DASHI.Physics.Closure.NSPeriodicConcreteProofProgramStatus where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Machine-readable mirror of the deterministic Python receipt.
------------------------------------------------------------------------

record FiniteProgramResults : Set where
  field
    farLowObservedDenominator : Nat
    farHighObservedDenominator : Nat
    nearResidualCoefficient : Nat
    farLowFitsOneEighth : Bool
    farHighFitsOneEighth : Bool
    nearScalarGridHasNoViolation : Bool
    staticFiveHalvesContractionRefuted : Bool
    sizeBoundaryCandidateStrict : Bool
    plateauEightClassifiedDiffuse : Bool
    hysteresisSwitchCount : Nat

open FiniteProgramResults public

finiteProgramResults : FiniteProgramResults
finiteProgramResults = record
  { farLowObservedDenominator = 128
  ; farHighObservedDenominator = 16
  ; nearResidualCoefficient = 64
  ; farLowFitsOneEighth = true
  ; farHighFitsOneEighth = true
  ; nearScalarGridHasNoViolation = true
  ; staticFiveHalvesContractionRefuted = true
  ; sizeBoundaryCandidateStrict = false
  ; plateauEightClassifiedDiffuse = true
  ; hysteresisSwitchCount = 1
  }

farLowReceiptRegression :
  farLowObservedDenominator finiteProgramResults ≡ 128
farLowReceiptRegression = refl

farHighReceiptRegression :
  farHighObservedDenominator finiteProgramResults ≡ 16
farHighReceiptRegression = refl

nearReceiptRegression :
  nearResidualCoefficient finiteProgramResults ≡ 64
nearReceiptRegression = refl

-- Finite and candidate results never discharge the universal analytic records.
officialCarrierInhabited : Bool
officialCarrierInhabited = false

universalFiveHalvesProved : Bool
universalFiveHalvesProved = false

universalDiniInwardnessProved : Bool
universalDiniInwardnessProved = false

universalAllDataCoverageProved : Bool
universalAllDataCoverageProved = false

unconditionalPeriodicGlobalRegularityProved : Bool
unconditionalPeriodicGlobalRegularityProved = false
