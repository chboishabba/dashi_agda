{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound312Exact where

------------------------------------------------------------------------
-- ROUND312 / CURRENT SHORTEST CANONICAL B PHYSICAL CUT
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116SelectedJApplicabilityRound309Exact as R309
import DASHI.Physics.YangMills.BalabanPairwiseEuclideanSemanticsRound310Exact as R310
import DASHI.Physics.YangMills.BalabanPairwiseMassRateFromTransferCoordinateRound311Exact as R311
import DASHI.Physics.YangMills.BalabanPairwiseClusteringStandardMassGapRound305Exact as R305

record Round312Boundary : Set where
  constructor round312-boundary
  field
    currentPhysicalCutHasSixTypedCoordinates : Bool
    currentPhysicalCutHasSixTypedCoordinatesIsTrue :
      currentPhysicalCutHasSixTypedCoordinates ≡ true
    duplicateIndependentMassRateCoordinateRequired : Bool
    duplicateIndependentMassRateCoordinateRequiredIsFalse :
      duplicateIndependentMassRateCoordinateRequired ≡ false
    selectedJApplicabilityStillPhysical : Bool
    selectedJApplicabilityStillPhysicalIsTrue :
      selectedJApplicabilityStillPhysical ≡ true
    covarianceLimitAlgebraStillNewYMAnalysis : Bool
    covarianceLimitAlgebraStillNewYMAnalysisIsFalse :
      covarianceLimitAlgebraStillNewYMAnalysis ≡ false
    candidateMassPositivityStillPrimitive : Bool
    candidateMassPositivityStillPrimitiveIsFalse :
      candidateMassPositivityStillPrimitive ≡ false
    standardSpectralTransferIsNewYMAnalysis : Bool
    standardSpectralTransferIsNewYMAnalysisIsFalse :
      standardSpectralTransferIsNewYMAnalysis ≡ false

canonicalRound312Boundary : Round312Boundary
canonicalRound312Boundary =
  round312-boundary true refl false refl true refl false refl false refl false refl

round312H1PublishedLocalizationLevel : ProofLevel
round312H1PublishedLocalizationLevel = R309.publishedDifferentiatedLocalizationLevel

round312H1SelectedJApplicabilityLevel : ProofLevel
round312H1SelectedJApplicabilityLevel = R309.selectedJApplicabilityPhysicalLevel

round312H2aPhysicalTimeSupportSemanticsLevel : ProofLevel
round312H2aPhysicalTimeSupportSemanticsLevel =
  R310.round310PhysicalTimeSupportSemanticsLevel

round312H2bBoundedTestAdmissibilityLevel : ProofLevel
round312H2bBoundedTestAdmissibilityLevel =
  R310.round310BoundedTestAdmissibilityLevel

round312H2cScalarOrderClosureLevel : ProofLevel
round312H2cScalarOrderClosureLevel = R310.round310ScalarOrderClosureLevel

round312H3aTransferEnergyDecayCoordinateLevel : ProofLevel
round312H3aTransferEnergyDecayCoordinateLevel =
  R311.round311TransferEnergyDecayCoordinateLevel

round312H3bHalfRatePhysicalDecayMeaningLevel : ProofLevel
round312H3bHalfRatePhysicalDecayMeaningLevel =
  R311.round311HalfRatePhysicalDecayMeaningLevel

round312StandardClusteringToSpectrumLevel : ProofLevel
round312StandardClusteringToSpectrumLevel =
  R305.round305StandardClusteringToSpectrumTransferLevel

round312CompilerLevels :
  ProofLevel × ProofLevel × ProofLevel × ProofLevel
round312CompilerLevels =
  R309.selectedJApplicabilityCompilerLevel ,
  R310.round310PairwisePresentationCompilerLevel ,
  R311.round311PairwiseMassRateAdapterLevel ,
  R305.round305NormalizedMassGapAssemblyLevel
