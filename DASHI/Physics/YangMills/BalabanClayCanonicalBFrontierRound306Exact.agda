{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound306Exact where

------------------------------------------------------------------------
-- ROUND306 / SHORTEST CURRENT B CUT
--
-- The standard OS/spectral route means the detailed subgap spectral-measure
-- construction R287-R303 is not mandatory mathematical debt.  It remains a
-- valuable optional internal reconstruction/cross-check.
--
-- R296 + R278 + R304 reduce arbitrary-pair continuum exponential clustering to
-- one source/application payment plus time/support semantics.  R305 then
-- isolates the established clustering->spectrum theorem as standard-library
-- authority.
--
-- Current YM-specific payments on this route:
--
--   G1. literal selected-J applicability of the published CMP116/CMP119
--       differentiated localization theorem on the exact T5 state;
--   G2. physical Euclidean-time presentation, selected-test boundedness, and
--       an order-closed scalar convergence authority;
--   G3. same reconstructed Hamiltonian: the concrete q=1/2 decay bound means
--       exponential decay at one strictly positive physical mass m*.
--
-- R309 makes G1 proof-bearing at the correct boundary.  R310 splits G2 so the
-- physical time/support meaning, bounded-test applicability and topology/order
-- closure cannot be confused with the already-checked covariance-limit algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanAbsoluteTwoJSourceMinCutRound299Exact as R299
import DASHI.Physics.YangMills.BalabanArbitraryPairContinuumClusteringRound304Exact as R304
import DASHI.Physics.YangMills.BalabanPairwiseClusteringStandardMassGapRound305Exact as R305
import DASHI.Physics.YangMills.BalabanCMP116SelectedJApplicabilityRound309Exact as R309
import DASHI.Physics.YangMills.BalabanPairwiseEuclideanSemanticsRound310Exact as R310

record Round306Boundary : Set where
  constructor round306-boundary
  field
    ymSpecificPhysicalCutHasThreeCoordinates : Bool
    ymSpecificPhysicalCutHasThreeCoordinatesIsTrue :
      ymSpecificPhysicalCutHasThreeCoordinates ≡ true

    g1DifferentiatedDecayMechanismAlreadySourceOwned : Bool
    g1DifferentiatedDecayMechanismAlreadySourceOwnedIsTrue :
      g1DifferentiatedDecayMechanismAlreadySourceOwned ≡ true

    g1RemainingPaymentIsSelectedJSameObjectSpecialization : Bool
    g1RemainingPaymentIsSelectedJSameObjectSpecializationIsTrue :
      g1RemainingPaymentIsSelectedJSameObjectSpecialization ≡ true

    g1NeighbourShellTypeEqualityMayPayApplicability : Bool
    g1NeighbourShellTypeEqualityMayPayApplicabilityIsFalse :
      g1NeighbourShellTypeEqualityMayPayApplicability ≡ false

    g2ManufacturesNewAnalyticDecayInformation : Bool
    g2ManufacturesNewAnalyticDecayInformationIsFalse :
      g2ManufacturesNewAnalyticDecayInformation ≡ false

    g2CovarianceLimitAlgebraIsSeparateCompiler : Bool
    g2CovarianceLimitAlgebraIsSeparateCompilerIsTrue :
      g2CovarianceLimitAlgebraIsSeparateCompiler ≡ true

    g3ManufacturesNewAnalyticDecayInformation : Bool
    g3ManufacturesNewAnalyticDecayInformationIsFalse :
      g3ManufacturesNewAnalyticDecayInformation ≡ false

    g2IsMandatorySameObjectPhysicalSemantics : Bool
    g2IsMandatorySameObjectPhysicalSemanticsIsTrue :
      g2IsMandatorySameObjectPhysicalSemantics ≡ true

    g3IsMandatorySameHamiltonianRateSemantics : Bool
    g3IsMandatorySameHamiltonianRateSemanticsIsTrue :
      g3IsMandatorySameHamiltonianRateSemantics ≡ true

    detailedSubgapSpectralRouteMandatory : Bool
    detailedSubgapSpectralRouteMandatoryIsFalse :
      detailedSubgapSpectralRouteMandatory ≡ false

    arbitraryPairContinuumClusteringAfterG1G2CompilerOwned : Bool
    arbitraryPairContinuumClusteringAfterG1G2CompilerOwnedIsTrue :
      arbitraryPairContinuumClusteringAfterG1G2CompilerOwned ≡ true

    massGapAfterClusteringRateAndStandardTransferCompilerOwned : Bool
    massGapAfterClusteringRateAndStandardTransferCompilerOwnedIsTrue :
      massGapAfterClusteringRateAndStandardTransferCompilerOwned ≡ true

    standardSpectralTransferIsYangMillsSpecificNewAnalysis : Bool
    standardSpectralTransferIsYangMillsSpecificNewAnalysisIsFalse :
      standardSpectralTransferIsYangMillsSpecificNewAnalysis ≡ false

canonicalRound306Boundary : Round306Boundary
canonicalRound306Boundary =
  round306-boundary
    true refl
    true refl
    true refl
    false refl
    false refl
    true refl
    false refl
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl

-- G1 source theorem and exact selected-T5 applicability are separate.
round306G1PublishedDifferentiatedLocalizationLevel : ProofLevel
round306G1PublishedDifferentiatedLocalizationLevel =
  R309.publishedDifferentiatedLocalizationLevel

round306G1SelectedJApplicabilityCompilerLevel : ProofLevel
round306G1SelectedJApplicabilityCompilerLevel =
  R309.selectedJApplicabilityCompilerLevel

round306G1SelectedJApplicabilityPhysicalLevel : ProofLevel
round306G1SelectedJApplicabilityPhysicalLevel =
  R309.selectedJApplicabilityPhysicalLevel

round306G1LiteralSelectedJSameObjectLocalizationLevel : ProofLevel
round306G1LiteralSelectedJSameObjectLocalizationLevel =
  R299.round299LiteralSelectedJSameObjectLocalizationLevel

round306G1LiteralAbsoluteTwoJLocalizationLevel : ProofLevel
round306G1LiteralAbsoluteTwoJLocalizationLevel =
  R296.round296LiteralAbsoluteTwoJLocalizationLevel

-- G2 split: no new decay theorem is hidden here.
round306G2PairwisePresentationCompilerLevel : ProofLevel
round306G2PairwisePresentationCompilerLevel =
  R310.round310PairwisePresentationCompilerLevel

round306G2PhysicalTimeSupportSemanticsLevel : ProofLevel
round306G2PhysicalTimeSupportSemanticsLevel =
  R310.round310PhysicalTimeSupportSemanticsLevel

round306G2BoundedTestAdmissibilityLevel : ProofLevel
round306G2BoundedTestAdmissibilityLevel =
  R310.round310BoundedTestAdmissibilityLevel

round306G2ScalarOrderClosureLevel : ProofLevel
round306G2ScalarOrderClosureLevel =
  R310.round310ScalarOrderClosureLevel

round306G2ConnectedCovarianceLimitCompilerLevel : ProofLevel
round306G2ConnectedCovarianceLimitCompilerLevel =
  R310.round310ConnectedCovarianceLimitCompilerLevel

-- Compatibility name retained for downstream status surfaces.
round306G2PhysicalPairwiseTimeMeaningLevel : ProofLevel
round306G2PhysicalPairwiseTimeMeaningLevel =
  R304.round304PhysicalTimeTranslationDistanceMeaningLevel

round306G3PhysicalMassRateNormalizationLevel : ProofLevel
round306G3PhysicalMassRateNormalizationLevel =
  R305.round305PhysicalMassRateNormalizationLevel

round306StandardClusteringToSpectrumLevel : ProofLevel
round306StandardClusteringToSpectrumLevel =
  R305.round305StandardClusteringToSpectrumTransferLevel

round306PairwiseClusteringCompilerLevel : ProofLevel
round306PairwiseClusteringCompilerLevel =
  R304.round304PairwiseContinuumClusteringCompilerLevel

round306MassGapAssemblyLevel : ProofLevel
round306MassGapAssemblyLevel = R305.round305NormalizedMassGapAssemblyLevel
