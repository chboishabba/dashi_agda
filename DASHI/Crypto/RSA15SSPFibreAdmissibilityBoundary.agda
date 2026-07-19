module DASHI.Crypto.RSA15SSPFibreAdmissibilityBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Crypto.RSAFactorFibreCompatibilityCore as Compatibility
import DASHI.Crypto.RSAVulnerabilityBoundary as Vulnerability
open import DASHI.Foundations.FifteenSSPSurface using
  ( FifteenSSPSurface
  ; canonicalZeroFifteenSSPSurface
  )

------------------------------------------------------------------------
-- 15SSP factor-fibre admissibility boundary.
--
-- The formal result is two-part:
--
--   1. Local multiplicative compatibility is non-separating. In every
--      nonzero residue fibre, every candidate unit has a compatible
--      complement. Repeating that test over 15 SSP lanes does not recover a
--      hidden factor.
--
--   2. The current deterministic toy benchmark observes no factor signal on
--      unbiased semiprimes, while intentionally SSP-constrained prime sources
--      are detectable. The admitted interpretation is therefore
--      structured-source detection only, never a general RSA break.
------------------------------------------------------------------------

data BenchmarkDataset : Set where
  unbiasedSemiprimeDataset : BenchmarkDataset
  structuredPrimeSourceDataset : BenchmarkDataset

data ResidueBasisFamily : Set where
  ssp15Basis : ResidueBasisFamily
  nonSSP15ControlBasis : ResidueBasisFamily
  random15ControlBasis : ResidueBasisFamily

data FibreAdmissibilityVerdict : Set where
  noObservedSeparation : FibreAdmissibilityVerdict
  structuredSourceDetectorOnly : FibreAdmissibilityVerdict
  candidateFactorSeparator : FibreAdmissibilityVerdict

data PromotionObligation : Set where
  unbiasedFactorSignalObligation : PromotionObligation
  controlSuperiorityObligation : PromotionObligation
  searchIndependenceObligation : PromotionObligation
  scalingObligation : PromotionObligation
  complexityArgumentObligation : PromotionObligation
  independentReplicationObligation : PromotionObligation
  explicitFactorWitnessObligation : PromotionObligation

canonicalPromotionObligations : List PromotionObligation
canonicalPromotionObligations =
  unbiasedFactorSignalObligation
  ∷ controlSuperiorityObligation
  ∷ searchIndependenceObligation
  ∷ scalingObligation
  ∷ complexityArgumentObligation
  ∷ independentReplicationObligation
  ∷ explicitFactorWitnessObligation
  ∷ []

record BenchmarkAUCRow : Set where
  constructor mkBenchmarkAUCRow
  field
    dataset : BenchmarkDataset
    basis : ResidueBasisFamily
    lowDefectAUCPermille : Nat
    structuredScoreAUCPermille : Nat
    productCompatibilityAUCPermille : Nat
    sampleGroupCount : Nat

open BenchmarkAUCRow public

-- Rounded from the deterministic benchmark receipt produced by
-- scripts/rsa_ssp_fibre_separation_benchmark.py.
canonicalUnbiasedSSP15Row : BenchmarkAUCRow
canonicalUnbiasedSSP15Row =
  mkBenchmarkAUCRow
    unbiasedSemiprimeDataset
    ssp15Basis
    558
    541
    500
    50

canonicalStructuredSSP15Row : BenchmarkAUCRow
canonicalStructuredSSP15Row =
  mkBenchmarkAUCRow
    structuredPrimeSourceDataset
    ssp15Basis
    900
    1000
    500
    50

canonicalUnbiasedProductCompatibilityIsChance :
  productCompatibilityAUCPermille canonicalUnbiasedSSP15Row ≡ 500
canonicalUnbiasedProductCompatibilityIsChance = refl

canonicalStructuredProductCompatibilityIsChance :
  productCompatibilityAUCPermille canonicalStructuredSSP15Row ≡ 500
canonicalStructuredProductCompatibilityIsChance = refl

record SearchIndependenceReceipt : Set where
  constructor mkSearchIndependenceReceipt
  field
    usesTrialDivision : Bool
    usesTrialDivisionIsFalse : usesTrialDivision ≡ false

    usesSqrtWindowOrdering : Bool
    usesSqrtWindowOrderingIsFalse : usesSqrtWindowOrdering ≡ false

    usesPollardRho : Bool
    usesPollardRhoIsFalse : usesPollardRho ≡ false

    usesECM : Bool
    usesECMIsFalse : usesECM ≡ false

    usesGNFS : Bool
    usesGNFSIsFalse : usesGNFS ≡ false

    usesPrivateFactorOracleInScoring : Bool
    usesPrivateFactorOracleInScoringIsFalse :
      usesPrivateFactorOracleInScoring ≡ false

    usesStructuredPrimeGenerationForUnbiasedDataset : Bool
    usesStructuredPrimeGenerationForUnbiasedDatasetIsFalse :
      usesStructuredPrimeGenerationForUnbiasedDataset ≡ false

open SearchIndependenceReceipt public

canonicalSearchIndependenceReceipt : SearchIndependenceReceipt
canonicalSearchIndependenceReceipt =
  mkSearchIndependenceReceipt
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

record RSA15SSPFibreAdmissibilityBoundary : Set where
  constructor mkRSA15SSPFibreAdmissibilityBoundary
  field
    boundaryLabel : String
    publicSurfaceLabel : String
    hiddenFactorFibreLabel : String
    localCompatibilityTheoremLabel : String

    canonicalSSPSurface : FifteenSSPSurface
    rsaVulnerabilityBoundary : Vulnerability.RSAVulnerabilityBoundary

    unbiasedSSP15Row : BenchmarkAUCRow
    structuredSSP15Row : BenchmarkAUCRow
    searchIndependence : SearchIndependenceReceipt

    localProductCompatibilityIsNonSeparating : Bool
    localProductCompatibilityIsNonSeparatingIsTrue :
      localProductCompatibilityIsNonSeparating ≡ true

    unbiasedFactorFibreSeparationObserved : Bool
    unbiasedFactorFibreSeparationObservedIsFalse :
      unbiasedFactorFibreSeparationObserved ≡ false

    structuredPrimeSourceSignalObserved : Bool
    structuredPrimeSourceSignalObservedIsTrue :
      structuredPrimeSourceSignalObserved ≡ true

    verdict : FibreAdmissibilityVerdict
    verdictIsStructuredSourceDetectorOnly :
      verdict ≡ structuredSourceDetectorOnly

    promotionObligations : List PromotionObligation
    promotionObligationsAreCanonical :
      promotionObligations ≡ canonicalPromotionObligations

    factorSeparationPromotionGateDischarged : Bool
    factorSeparationPromotionGateDischargedIsFalse :
      factorSeparationPromotionGateDischarged ≡ false

    generalRSABreakPromoted : Bool
    generalRSABreakPromotedIsFalse :
      generalRSABreakPromoted ≡ false

    productionAdvisoryAuthorityPromoted : Bool
    productionAdvisoryAuthorityPromotedIsFalse :
      productionAdvisoryAuthorityPromoted ≡ false

    benchmarkStatement : String
    remainingGap : String

open RSA15SSPFibreAdmissibilityBoundary public

canonicalRSA15SSPFibreAdmissibilityBoundary :
  RSA15SSPFibreAdmissibilityBoundary
canonicalRSA15SSPFibreAdmissibilityBoundary =
  mkRSA15SSPFibreAdmissibilityBoundary
    "RSA 15SSP factor-fibre admissibility boundary"
    "public multiplication quotient n = p q"
    "hidden ordered factor fibre (p , q) above n"
    "DASHI.Crypto.RSAFactorFibreCompatibilityCore.localCompatibilityIsNonSeparating"
    canonicalZeroFifteenSSPSurface
    Vulnerability.canonicalRSAVulnerabilityBoundary
    canonicalUnbiasedSSP15Row
    canonicalStructuredSSP15Row
    canonicalSearchIndependenceReceipt
    true
    refl
    false
    refl
    true
    refl
    structuredSourceDetectorOnly
    refl
    canonicalPromotionObligations
    refl
    false
    refl
    false
    refl
    false
    refl
    "15SSP local product compatibility remains chance-level on unbiased semiprimes; intentionally SSP-constrained source structure is detected."
    "A promotion requires an unbiased factor-separating invariant computable from n alone, control superiority, non-leaky scaling, a complexity argument, explicit factor witnesses, and independent replication."

canonicalVerdictIsStructuredSourceDetectorOnly :
  verdict canonicalRSA15SSPFibreAdmissibilityBoundary
  ≡
  structuredSourceDetectorOnly
canonicalVerdictIsStructuredSourceDetectorOnly =
  verdictIsStructuredSourceDetectorOnly
    canonicalRSA15SSPFibreAdmissibilityBoundary

canonicalUnbiasedFactorSeparationIsBlocked :
  unbiasedFactorFibreSeparationObserved
    canonicalRSA15SSPFibreAdmissibilityBoundary
  ≡
  false
canonicalUnbiasedFactorSeparationIsBlocked =
  unbiasedFactorFibreSeparationObservedIsFalse
    canonicalRSA15SSPFibreAdmissibilityBoundary

canonicalGeneralRSABreakIsNotPromoted :
  generalRSABreakPromoted canonicalRSA15SSPFibreAdmissibilityBoundary
  ≡
  false
canonicalGeneralRSABreakIsNotPromoted =
  generalRSABreakPromotedIsFalse
    canonicalRSA15SSPFibreAdmissibilityBoundary

------------------------------------------------------------------------
-- No inhabitant is supplied. A future implementation can construct this
-- only after every admission gate is discharged with external evidence.
------------------------------------------------------------------------

record RSA15SSPFactorSeparationPromotionGate : Set where
  constructor mkRSA15SSPFactorSeparationPromotionGate
  field
    unbiasedFactorSignalObserved : Bool
    unbiasedFactorSignalObservedIsTrue :
      unbiasedFactorSignalObserved ≡ true

    beatsNonSSPAndRandomControls : Bool
    beatsNonSSPAndRandomControlsIsTrue :
      beatsNonSSPAndRandomControls ≡ true

    searchIndependenceVerified : Bool
    searchIndependenceVerifiedIsTrue :
      searchIndependenceVerified ≡ true

    scalingBeyondToySizesVerified : Bool
    scalingBeyondToySizesVerifiedIsTrue :
      scalingBeyondToySizesVerified ≡ true

    subGNFSComplexityArgumentSupplied : Bool
    subGNFSComplexityArgumentSuppliedIsTrue :
      subGNFSComplexityArgumentSupplied ≡ true

    explicitRecoveredFactorsVerified : Bool
    explicitRecoveredFactorsVerifiedIsTrue :
      explicitRecoveredFactorsVerified ≡ true

    independentlyReplicated : Bool
    independentlyReplicatedIsTrue :
      independentlyReplicated ≡ true
