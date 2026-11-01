module DASHI.Analysis.RiemannAristotleNearCoreDeterminantTaperLeanReturnExact where

------------------------------------------------------------------------
-- KERNEL-CHECKED LEAN RETURN: LITERAL NEAR-CORE DETERMINANT TAPER
--
-- Records the checked source surface from
-- Zeta23Bridge/NearCoreDeterminantTaper.lean.  This is provenance/status only;
-- no Lean proof term is treated as an Agda proof.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record NearCoreDeterminantTaperLeanReturn : Set where
  constructor near-core-determinant-taper-lean-return
  field
    leanModule : String
    aggregateBuildJobs : String

    aggregateLeanBuildKernelChecked : Bool
    aggregateLeanBuildKernelCheckedIsTrue : aggregateLeanBuildKernelChecked ≡ true

    standardAxiomAuditOnly : Bool
    standardAxiomAuditOnlyIsTrue : standardAxiomAuditOnly ≡ true

    oneCellDeterminantIntegralKernelChecked : Bool
    oneCellDeterminantIntegralKernelCheckedIsTrue :
      oneCellDeterminantIntegralKernelChecked ≡ true

    wholeNearCoreSingleIntegralKernelChecked : Bool
    wholeNearCoreSingleIntegralKernelCheckedIsTrue :
      wholeNearCoreSingleIntegralKernelChecked ≡ true

    nearEnergyScalarizationKernelChecked : Bool
    nearEnergyScalarizationKernelCheckedIsTrue :
      nearEnergyScalarizationKernelChecked ≡ true

    finiteExponentialSumFormKernelChecked : Bool
    finiteExponentialSumFormKernelCheckedIsTrue :
      finiteExponentialSumFormKernelChecked ≡ true

    determinantFarRemainderKernelChecked : Bool
    determinantFarRemainderKernelCheckedIsTrue :
      determinantFarRemainderKernelChecked ≡ true

    offEnergyScalarConsumerKernelChecked : Bool
    offEnergyScalarConsumerKernelCheckedIsTrue :
      offEnergyScalarConsumerKernelChecked ≡ true

    balanceStrictInequalityNoGoKernelChecked : Bool
    balanceStrictInequalityNoGoKernelCheckedIsTrue :
      balanceStrictInequalityNoGoKernelChecked ≡ true

    scalarAnalyticBoundProved : Bool
    scalarAnalyticBoundProvedIsFalse : scalarAnalyticBoundProved ≡ false

    leanProofTransportedIntoAgda : Bool
    leanProofTransportedIntoAgdaIsFalse : leanProofTransportedIntoAgda ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

open NearCoreDeterminantTaperLeanReturn public

canonicalNearCoreDeterminantTaperLeanReturn : NearCoreDeterminantTaperLeanReturn
canonicalNearCoreDeterminantTaperLeanReturn =
  near-core-determinant-taper-lean-return
    "Zeta23Bridge/Zeta23Bridge/NearCoreDeterminantTaper.lean"
    "8885"
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
