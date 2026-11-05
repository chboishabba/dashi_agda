{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.Zhang2025EMGravityPhysicalPromotionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.Zhang2025EMGravitySourceClaimExact as Zhang
import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.AntigravityClaimTheoryComparisonExact as Comparison
import DASHI.Physics.ExoticGravity.AntigravityExperimentalCutProvenanceExact as Provenance
import DASHI.Physics.ExoticGravity.AntigravityResearchPromotionCutExact as Promotion
import DASHI.Physics.ExoticGravity.AntigravityCalibratedFullyDerivedExperimentalCutExact as Calibrated
import DASHI.Physics.ExoticGravity.AntigravityStrongestConditionalTheoremExact as Strong

------------------------------------------------------------------------
-- NO GENERIC "ANTIGRAVITY" RECEIPT MAY BE CREATED BY A PATENT NUMBER.
-- Reuse the existing strongest provenance and experimental cut literally.
------------------------------------------------------------------------

data SourceOnlyStage : Set where
  patentAssertionOnly : SourceOnlyStage
  socialRetellingOnly : SourceOnlyStage

data ExperimentallyGroundedStage : Set where
  actualSameApparatusComparison : ExperimentallyGroundedStage

data SourceOnlyDoesNotPromote : SourceOnlyStage → ExperimentallyGroundedStage → Set where

record ChinesePatentPhysicalComparison
  (claim : Anti.AntigravityClaim) : Set where
  constructor chinese-patent-physical-comparison
  field
    documentary : Zhang.DocumentaryClaimReceipt
    claimedMotion : Zhang.PatentClaimEntitlement Zhang.controlledTargetMotion
    apparatusIdentification : String
    physicalComparison : Provenance.ProvenancedComparativeAnomalyReceipt claim
    physicalStage : ExperimentallyGroundedStage
    stageIsExperimental : physicalStage ≡ actualSameApparatusComparison
    physicalAnomaly : Promotion.ComparativeAnomalyReceipt claim
    physicalAnomalySameAsProvenanced :
      physicalAnomaly ≡ Provenance.anomaly physicalComparison

open ChinesePatentPhysicalComparison public

-- The compiler only projects a supplied physical provenance receipt.
-- Documentary fields alone never build an experimental comparison.
compileChinesePatentComparison :
  {claim : Anti.AntigravityClaim} →
  (source : Zhang.DocumentaryClaimReceipt) →
  (apparatus : String) →
  (receipt : Provenance.ProvenancedComparativeAnomalyReceipt claim) →
  ChinesePatentPhysicalComparison claim
compileChinesePatentComparison source apparatus receipt =
  chinese-patent-physical-comparison
    source Zhang.claimedTargetMotion apparatus receipt
    actualSameApparatusComparison refl
    (Provenance.anomaly receipt) refl

------------------------------------------------------------------------
-- Route a claimed stronger effect only after its exact consumer-specific
-- experimental receipt has been provided.
------------------------------------------------------------------------

record ExternalFieldEvaluation : Set where
  constructor external-field-evaluation
  field
    comparison : ChinesePatentPhysicalComparison Anti.remoteRepulsiveField
    discriminator : Zhang.GravitationalRoute Zhang.externalTestMass
    discriminatorIsCanonical :
      discriminator ≡ Zhang.canonicalExternalRoute

compileExternalFieldEvaluation :
  ChinesePatentPhysicalComparison Anti.remoteRepulsiveField →
  ExternalFieldEvaluation
compileExternalFieldEvaluation comparison =
  external-field-evaluation comparison Zhang.canonicalExternalRoute refl

record MetricEvaluation : Set where
  constructor metric-evaluation
  field
    comparison : ChinesePatentPhysicalComparison Anti.engineeredMetricResponse
    discriminator : Zhang.GravitationalRoute Zhang.metricClock
    discriminatorIsCanonical :
      discriminator ≡ Zhang.canonicalMetricRoute

compileMetricEvaluation :
  ChinesePatentPhysicalComparison Anti.engineeredMetricResponse →
  MetricEvaluation
compileMetricEvaluation comparison =
  metric-evaluation comparison Zhang.canonicalMetricRoute refl

------------------------------------------------------------------------
-- The strongest negative-G interpretation needs an ADDITIONAL constitutive
-- receipt not supplied by patent text or an unexplained force alone.
-- We deliberately do not define such an inhabitant for this patent.
------------------------------------------------------------------------

strongestEstablishedStatusNeedsExistingCalibratedReceipt :
  (receipt :
    Calibrated.CalibratedFullyDerivedComparativeAnomalyReceipt
      Anti.remoteRepulsiveField) →
  Strong.terminalComparativeStatus receipt ≡
    Promotion.comparativeAnomalyEstablished
strongestEstablishedStatusNeedsExistingCalibratedReceipt receipt =
  Strong.terminalComparativeStatusIsEstablished receipt

data CurrentZhangPhysicalAuthority : Set where

record SourceSpecificPhysicalLeaves : Set where
  constructor source-specific-physical-leaves
  field
    completeMeasuredEMFieldAndTargetModel : Bool
    sourceDriveAndSuspensionMomentumClosure : Bool
    calibratedONOFFPairWithRawData : Bool
    ordinaryEMMechanicalThermalRFSystematicsClosed : Bool
    heldOutExternalTestMassOrFreeFallReadout : Bool
    independentMetricClockOpticalReadout : Bool
    independentlyReplicated : Bool
    measuredFarFieldTTGW : Bool

-- Status refers to evidence available from the SOURCE RECORD, not an
-- assertion that all experiments are impossible or a numeric null result.
currentDocumentaryOnlyLeaves : SourceSpecificPhysicalLeaves
currentDocumentaryOnlyLeaves =
  source-specific-physical-leaves
    false false false false false false false false

record NonPromotionBoundary : Set where
  constructor non-promotion-boundary
  field
    originalPatentGrantsEmpiricalAnomaly : Bool
    nominal50kVGrantsCalibratedForce : Bool
    nearVacuumExcludesElectrostatics : Bool
    dielectricTargetCannotFeelEMForce : Bool
    forceResidualAloneEstablishesMetric : Bool
    alternativeModelBetterFitIdentifiesUniqueMechanism : Bool
    PaisWaveClaimEqualsTargetMotion : Bool
    sourceSpecificConsumerEvidenceRequired : Bool

canonicalNonPromotionBoundary : NonPromotionBoundary
canonicalNonPromotionBoundary =
  non-promotion-boundary false false false false false false false true
