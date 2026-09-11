{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound311Exact where

------------------------------------------------------------------------
-- ROUND311 / ARCHAEOLOGY-NORMALIZED CANONICAL B MIN-CUT
--
-- Work backwards from the literal B consumer, not from historical producer
-- tactics.  R295/R296/R304/R305/R309/R310 already show that the broad phrase
-- "prove continuum clustering" decomposes into a small number of exact
-- source/application coordinates.
--
-- Already-owned theorem/compiler structure:
--
--   * CMP116 differentiated localization on its declared analytic J carrier;
--   * mixed d_J d_J log Z = connected covariance on the exact T5 expectation
--     algebra;
--   * magnitude correction and direct rooted-shell compiler;
--   * one-sided finite -> continuum upper transport once the exact convergence
--     instance is supplied;
--   * lattice/physical exponent algebra;
--   * standard exponential-clustering -> spectral-gap transfer.
--
-- Current B-specific application cut:
--
--   G1  selected physical T5 J-pair applicability of the published shell;
--   G2a physical Euclidean-time/support semantics;
--   G2b boundedness/admissibility of the selected left/right/product tests;
--   G2c the exact upper-closed order instance for the selected scalar limit;
--   G3  same reconstructed rate/energy identification.
--
-- This owner is navigational/proof-search only.  It manufactures none of those
-- physical inhabitants and does not promote Yang--Mills or Clay completion.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound306Exact as R306
import DASHI.Physics.YangMills.BalabanCMP116SelectedJApplicabilityRound309Exact as R309
import DASHI.Physics.YangMills.BalabanPairwiseEuclideanSemanticsRound310Exact as R310
import DASHI.Physics.YangMills.BalabanClayOneSidedCorrelationLimitRound276Exact as R276
import DASHI.Physics.YangMills.BalabanMarkedLogPartitionConnectedCorrelationCompilerExact as Marked
import DASHI.Physics.YangMills.BalabanPhysicalClusteringScaleAlgebraExact as Scale
import DASHI.Physics.YangMills.BalabanClusteringDecayRatioToGapRound285Exact as R285
import DASHI.Physics.YangMills.BalabanPairwiseClusteringStandardMassGapRound305Exact as R305

------------------------------------------------------------------------
-- Search objects after archaeology/consumer normalization.
------------------------------------------------------------------------

data CanonicalBResidual311 : Set where
  selectedT5JApplicability : CanonicalBResidual311
  physicalTimeSupportSemantics : CanonicalBResidual311
  selectedBoundedTestAdmissibility : CanonicalBResidual311
  selectedUpperClosedLimitInstance : CanonicalBResidual311
  sameReconstructedRateEnergyIdentification : CanonicalBResidual311

searchRole311 : CanonicalBResidual311 → Introspective.ProofSearchTargetRole
searchRole311 selectedT5JApplicability = Introspective.canonicalConsumerResidual
searchRole311 physicalTimeSupportSemantics = Introspective.canonicalConsumerResidual
searchRole311 selectedBoundedTestAdmissibility = Introspective.canonicalConsumerResidual
searchRole311 selectedUpperClosedLimitInstance = Introspective.canonicalConsumerResidual
searchRole311 sameReconstructedRateEnergyIdentification =
  Introspective.canonicalConsumerResidual

------------------------------------------------------------------------
-- Boundary: what is no longer a primitive YM theorem debt on this route.
------------------------------------------------------------------------

record Round311Boundary : Set where
  constructor round311-boundary
  field
    broadContinuumClusteringPrimitiveLeaf : Bool
    broadContinuumClusteringPrimitiveLeafIsFalse :
      broadContinuumClusteringPrimitiveLeaf ≡ false

    stepVClusterExpansionMandatoryRoute : Bool
    stepVClusterExpansionMandatoryRouteIsFalse :
      stepVClusterExpansionMandatoryRoute ≡ false

    rowCHeatDoobMandatoryRoute : Bool
    rowCHeatDoobMandatoryRouteIsFalse :
      rowCHeatDoobMandatoryRoute ≡ false

    mixedLogDerivativeToConnectedCorrelationNewYMAnalysis : Bool
    mixedLogDerivativeToConnectedCorrelationNewYMAnalysisIsFalse :
      mixedLogDerivativeToConnectedCorrelationNewYMAnalysis ≡ false

    oneSidedLimitCompilerNewYMAnalysis : Bool
    oneSidedLimitCompilerNewYMAnalysisIsFalse :
      oneSidedLimitCompilerNewYMAnalysis ≡ false

    physicalScaleExponentAlgebraNewYMAnalysis : Bool
    physicalScaleExponentAlgebraNewYMAnalysisIsFalse :
      physicalScaleExponentAlgebraNewYMAnalysis ≡ false

    standardClusteringToSpectrumNewYMAnalysis : Bool
    standardClusteringToSpectrumNewYMAnalysisIsFalse :
      standardClusteringToSpectrumNewYMAnalysis ≡ false

    exactApplicationMinCutHasFiveCoordinates : Bool
    exactApplicationMinCutHasFiveCoordinatesIsTrue :
      exactApplicationMinCutHasFiveCoordinates ≡ true

canonicalRound311Boundary : Round311Boundary
canonicalRound311Boundary =
  round311-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl

------------------------------------------------------------------------
-- Authority/status projection from the existing canonical owners.
------------------------------------------------------------------------

-- G1: source theorem exists; exact selected-T5 applicability remains physical.
round311PublishedTwoJLocalizationLevel : ProofLevel
round311PublishedTwoJLocalizationLevel = R309.publishedDifferentiatedLocalizationLevel

round311SelectedT5JApplicabilityLevel : ProofLevel
round311SelectedT5JApplicabilityLevel = R309.selectedJApplicabilityPhysicalLevel

round311SelectedT5JApplicabilityCompilerLevel : ProofLevel
round311SelectedT5JApplicabilityCompilerLevel = R309.selectedJApplicabilityCompilerLevel

-- The mixed derivative -> connected-correlation presentation is compiler-owned.
round311MixedDerivativeCorrelationCompilerLevel : ProofLevel
round311MixedDerivativeCorrelationCompilerLevel = machineChecked

-- G2: physical semantics/test applicability/exact order instance.
round311PhysicalTimeSupportSemanticsLevel : ProofLevel
round311PhysicalTimeSupportSemanticsLevel = R310.round310PhysicalTimeSupportSemanticsLevel

round311SelectedBoundedTestAdmissibilityLevel : ProofLevel
round311SelectedBoundedTestAdmissibilityLevel = R310.round310BoundedTestAdmissibilityLevel

round311SelectedUpperClosedLimitInstanceLevel : ProofLevel
round311SelectedUpperClosedLimitInstanceLevel = R310.round310ScalarOrderClosureLevel

round311GenericOneSidedLimitCompilerLevel : ProofLevel
round311GenericOneSidedLimitCompilerLevel = R276.round276OneSidedLimitCompilerLevel

round311ConcreteUpperClosedLimitTheoremLevel : ProofLevel
round311ConcreteUpperClosedLimitTheoremLevel =
  R276.round276ConcreteUpperClosedLimitAuthorityLevel

-- G3: dimensional algebra is already checked; the live seam is the exact
-- reconstructed rate/energy semantics on the same Hamiltonian.
round311PhysicalScaleExponentAlgebraLevel : ProofLevel
round311PhysicalScaleExponentAlgebraLevel = Scale.physicalClusteringExponentConversionLevel

round311RateToSpectrumIdentificationLevel : ProofLevel
round311RateToSpectrumIdentificationLevel =
  R285.round285PhysicalRateToSpectrumIdentificationLevel

round311StandardClusteringToSpectrumLevel : ProofLevel
round311StandardClusteringToSpectrumLevel =
  R305.round305StandardClusteringToSpectrumTransferLevel

round311MassGapAssemblyLevel : ProofLevel
round311MassGapAssemblyLevel = R306.round306MassGapAssemblyLevel

------------------------------------------------------------------------
-- Explicit non-promotion regressions.
------------------------------------------------------------------------

broadContinuumClusteringPrimitiveLeafIsFalse :
  Round311Boundary.broadContinuumClusteringPrimitiveLeaf
    canonicalRound311Boundary ≡ false
broadContinuumClusteringPrimitiveLeafIsFalse = refl

exactApplicationMinCutHasFiveCoordinatesIsTrue :
  Round311Boundary.exactApplicationMinCutHasFiveCoordinates
    canonicalRound311Boundary ≡ true
exactApplicationMinCutHasFiveCoordinatesIsTrue = refl

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
