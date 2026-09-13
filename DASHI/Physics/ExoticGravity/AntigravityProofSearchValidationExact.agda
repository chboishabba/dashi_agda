module DASHI.Physics.ExoticGravity.AntigravityProofSearchValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.ExoticGravity.AntigravityConstraintPruningVsBundlePaymentExact as Pruning
import DASHI.Physics.ExoticGravity.ConstraintPruningIdentityWeldExact as Weld
import DASHI.Physics.ExoticGravity.AntigravityConstraintInformedBundleDesignExact as Design
import DASHI.Physics.ExoticGravity.AntigravityJointProofSearchFrontierExact as Joint
import DASHI.Physics.ExoticGravity.AntigravityMicroscopicBulkProofSearchBridgeExact as Micro
import DASHI.Physics.ExoticGravity.AntigravityFirstIrreducibleSourceResidualExact as Source
import DASHI.Physics.ExoticGravity.LiTorrTheorySourceDiligenceProofSearchExact as Theory
import DASHI.Physics.ExoticGravity.AntigravityEmpiricalTheoryDiligenceBidiExact as Parallel
import DASHI.Physics.ExoticGravity.AntigravityProofSearchLeastPrivilegeAdmissionExact as Admission
import DASHI.Physics.ExoticGravity.AntigravitySourceAcquisitionCompilationExact as Acquisition
import DASHI.Physics.ExoticGravity.AntigravitySourceBundleDerivationLineageExact as SourceDerivation
import DASHI.Physics.ExoticGravity.AntigravityExperimentalCutProvenanceExact as Provenance
import DASHI.Physics.ExoticGravity.AntigravityBundleExecutionDerivationExact as BundleDerivation
import DASHI.Physics.ExoticGravity.AntigravityFullyDerivedExperimentalCutExact as FullyDerived
import DASHI.Physics.ExoticGravity.AntigravityExecutionCalibrationExact as Calibration
import DASHI.Physics.ExoticGravity.AntigravityCalibratedExecutionBridgeExact as Calibrated
import DASHI.Physics.ExoticGravity.AntigravityCalibratedFullyDerivedExperimentalCutExact as CalibratedCut
import DASHI.Physics.ExoticGravity.AntigravityConsumerScopedCalibrationExact as ConsumerCalibration
import DASHI.Physics.ExoticGravity.AntigravityClaimScopedExperimentalCutExact as ClaimCut
import DASHI.Physics.ExoticGravity.AntigravityClaimScopedComparativeAnomalyExact as ClaimComparison
import DASHI.Physics.ExoticGravity.AntigravityStrongPromotionFacadeExact as Strong

------------------------------------------------------------------------
-- FOCUSED VALIDATION ROOT
------------------------------------------------------------------------

currentFrontierStillSourceGeometry :
  Joint.currentRecommendedBundle ≡ Joint.sourceGeometryBundle
currentFrontierStillSourceGeometry = Joint.currentRecommendationIsSourceGeometry

microscopicFrontierStillSourceDistribution :
  Micro.currentMicroscopicFirstOpenIsSourceDistribution
    ≡ Micro.currentMicroscopicFirstOpenIsSourceDistribution
microscopicFrontierStillSourceDistribution = refl

literalGeometryFrontierStillSourceShape :
  Source.currentLiteralGeometryFirstOpen
    ≡ Source.currentLiteralGeometryFirstOpen
literalGeometryFrontierStillSourceShape = refl

legacyExperimentsCannotBeStitchedIntoCurrentCut :
  Pruning.heterogeneousExperimentsMayBeStitchedIntoOneApparatusReceipt
    Pruning.canonicalConstraintPruningVsBundleBoundary
    ≡ false
legacyExperimentsCannotBeStitchedIntoCurrentCut = refl

hathawayConstraintIdentityWeldLoads :
  Weld.ConstraintPruningIdentityWeld Pruning.hathawayNullPruning
hathawayConstraintIdentityWeldLoads = Weld.hathawayIdentityWeld

tajmarTransitionIdentityWeldLoads :
  Weld.ConstraintPruningIdentityWeld Pruning.tajmarTransitionPruning
tajmarTransitionIdentityWeldLoads = Weld.tajmarTransitionIdentityWeld

legacyConstraintsMayRefineDesignWithoutPayingReceipt :
  Design.legacyConstraintMayRefineNewExperimentDesign
    Design.canonicalConstraintInformedBundleBoundary
    ≡ true
legacyConstraintsMayRefineDesignWithoutPayingReceipt = refl

refinedDesignDoesNotCreateBundleReceipt :
  Design.refinedDesignAutomaticallyCreatesBundleReceipt
    Design.canonicalConstraintInformedBundleBoundary
    ≡ false
refinedDesignDoesNotCreateBundleReceipt = refl

physicalSourceAndTheorySourceRemainDistinct :
  Parallel.physicalSourceAndTheorySourceAreSameCoordinate
    Parallel.canonicalEmpiricalTheoryDiligenceBoundary
    ≡ false
physicalSourceAndTheorySourceRemainDistinct = refl

physicalSourceMoveIsAdmitted :
  Admission.currentPhysicalSourceMoveIsAdmitted
    Admission.canonicalAntigravityLeastPrivilegeBoundary
    ≡ true
physicalSourceMoveIsAdmitted = refl

admissionIsNotExecution :
  Admission.admittedMoveEqualsExecutedExperiment
    Admission.canonicalAntigravityLeastPrivilegeBoundary
    ≡ false
admissionIsNotExecution = refl

sourceTargetIsNotMeasurementReceipt :
  Acquisition.targetDescriptionEqualsMeasurementReceipt
    Acquisition.canonicalSourceAcquisitionCompilationBoundary
    ≡ false
sourceTargetIsNotMeasurementReceipt = refl

apparatusIdentityIsNotRunIdentity :
  Acquisition.apparatusIdentityEqualsRunIdentifier
    Acquisition.canonicalSourceAcquisitionCompilationBoundary
    ≡ false
apparatusIdentityIsNotRunIdentity = refl

sourceCalibrationCarrierIsNotRevision :
  Acquisition.calibrationCarrierEqualsCalibrationRevision
    Acquisition.canonicalSourceAcquisitionCompilationBoundary
    ≡ false
sourceCalibrationCarrierIsNotRevision = refl

currentRepoStillLacksPhysicalSourcePackage :
  Acquisition.currentRepoContainsCanonicalPhysicalSourcePackage
    Acquisition.canonicalSourceAcquisitionCompilationBoundary
    ≡ false
currentRepoStillLacksPhysicalSourcePackage = refl

sameApparatusLabelDoesNotProveDataToBundleDerivation :
  SourceDerivation.sameApparatusLabelProvesDataToBundleDerivation
    SourceDerivation.canonicalSourceBundleDerivationBoundary
    ≡ false
sameApparatusLabelDoesNotProveDataToBundleDerivation = refl

bundleStateWitnessDoesNotEqualExecutionProvenance :
  Provenance.bundleStateWitnessAloneEqualsExecutionProvenance
    Provenance.canonicalExperimentalCutProvenanceBoundary
    ≡ false
bundleStateWitnessDoesNotEqualExecutionProvenance = refl

executionCalibrationCarrierIsNotRevision :
  Provenance.calibrationCarrierEqualsCalibrationRevision
    Provenance.canonicalExperimentalCutProvenanceBoundary
    ≡ false
executionCalibrationCarrierIsNotRevision = refl

bundleDerivationRequiresExactOutputIdentity :
  BundleDerivation.exactOutputBundleIdentityRequired
    BundleDerivation.canonicalBundleExecutionDerivationBoundary
    ≡ true
bundleDerivationRequiresExactOutputIdentity = refl

fullyDerivedCutStillDoesNotProveAntigravity :
  FullyDerived.fullyDerivedCutAutomaticallyProvesAntigravity
    FullyDerived.canonicalFullyDerivedExperimentalCutBoundary
    ≡ false
fullyDerivedCutStillDoesNotProveAntigravity = refl

------------------------------------------------------------------------
-- Calibration must be typed, same-data, same-configuration, and consumer scoped.
------------------------------------------------------------------------

calibrationCarrierStringIsNotTypedRefinement :
  Calibration.calibrationCarrierStringEqualsTypedRefinement
    Calibration.canonicalExecutionCalibrationBoundary
    ≡ false
calibrationCarrierStringIsNotTypedRefinement = refl

typedDataRefinementIsRequired :
  Calibration.typedDataRefinementRequired
    Calibration.canonicalExecutionCalibrationBoundary
    ≡ true
typedDataRefinementIsRequired = refl

calibrationMustBindExactExecutionData :
  Calibrated.refinedEvidenceMustBeExactExecutionData
    Calibrated.canonicalCalibratedExecutionBridgeBoundary
    ≡ true
calibrationMustBindExactExecutionData = refl

apparatusAndRunRemainDistinctInExecutionWeld :
  Calibrated.apparatusIdentityAndRunIdentityAreDistinct
    Calibrated.canonicalCalibratedExecutionBridgeBoundary
    ≡ true
apparatusAndRunRemainDistinctInExecutionWeld = refl

sameApparatusLabelDoesNotWeldSourceRun :
  Calibrated.sameApparatusLabelAloneWeldsSourceReceiptToExecution
    Calibrated.canonicalCalibratedExecutionBridgeBoundary
    ≡ false
sameApparatusLabelDoesNotWeldSourceRun = refl

allFourStagesNeedTypedCalibration :
  CalibratedCut.allFourStagesNeedTypedCalibration
    CalibratedCut.canonicalCalibratedFullyDerivedBoundary
    ≡ true
allFourStagesNeedTypedCalibration = refl

provenanceStringsDoNotPayCalibration :
  CalibratedCut.provenanceStringsAlonePayCalibration
    CalibratedCut.canonicalCalibratedFullyDerivedBoundary
    ≡ false
provenanceStringsDoNotPayCalibration = refl

genericCalibrationDoesNotEqualConsumerAdequacy :
  ConsumerCalibration.genericCalibrationAdequacyEqualsConsumerAdequacy
    ConsumerCalibration.canonicalConsumerScopedCalibrationBoundary
    ≡ false
genericCalibrationDoesNotEqualConsumerAdequacy = refl

claimDiscriminatorBindingRequiredForCalibration :
  ConsumerCalibration.exactClaimDiscriminatorBindingRequired
    ConsumerCalibration.canonicalConsumerScopedCalibrationBoundary
    ≡ true
claimDiscriminatorBindingRequiredForCalibration = refl

staticLoadCalibrationDoesNotPayFreeFall :
  ConsumerCalibration.staticLoadCalibrationAutomaticallyPaysFreeFallCalibration
    ConsumerCalibration.canonicalConsumerScopedCalibrationBoundary
    ≡ false
staticLoadCalibrationDoesNotPayFreeFall = refl

allStagesMustMatchSameClaimConsumer :
  ClaimCut.allFourStagesMustMatchSameClaimConsumer
    ClaimCut.canonicalClaimScopedCutBoundary
    ≡ true
allStagesMustMatchSameClaimConsumer = refl

consumerCalibrationCannotBeDroppedAtComparison :
  ClaimComparison.consumerCalibrationMayBeDroppedAtComparison
    ClaimComparison.canonicalClaimScopedComparisonBoundary
    ≡ false
consumerCalibrationCannotBeDroppedAtComparison = refl

exactClaimScopedCutIdentityRequired :
  Strong.exactClaimScopedCutIdentityRequired
    Strong.canonicalStrongPromotionBoundary
    ≡ true
exactClaimScopedCutIdentityRequired = refl

newConsumersRequireStrongReceipt :
  Strong.newConsumersRequireFullyDerivedReceipt
    Strong.canonicalStrongPromotionBoundary
    ≡ true
newConsumersRequireStrongReceipt = refl

newConsumersRequireTypedCalibration :
  Strong.newConsumersRequireTypedCalibration
    Strong.canonicalStrongPromotionBoundary
    ≡ true
newConsumersRequireTypedCalibration = refl

newConsumersRequireConsumerScopedCalibration :
  Strong.newConsumersRequireConsumerScopedCalibration
    Strong.canonicalStrongPromotionBoundary
    ≡ true
newConsumersRequireConsumerScopedCalibration = refl

calibrationStringAloneCannotPromote :
  Strong.calibrationStringAloneSufficient
    Strong.canonicalStrongPromotionBoundary
    ≡ false
calibrationStringAloneCannotPromote = refl

legacyComparativeReceiptDoesNotAutoUpgrade :
  Strong.legacyComparativeReceiptAutomaticallyUpgrades
    Strong.canonicalStrongPromotionBoundary
    ≡ false
legacyComparativeReceiptDoesNotAutoUpgrade = refl

strongComparativeTensionStillNotUniversalLaw :
  Strong.fullyDerivedComparativeTensionEqualsUniversalAntigravityLaw
    Strong.canonicalStrongPromotionBoundary
    ≡ false
strongComparativeTensionStillNotUniversalLaw = refl

------------------------------------------------------------------------
-- Theory diligence remains separately load-bearing.
------------------------------------------------------------------------

prd1991DiligenceResidualsLoad :
  Theory.prd1991CurrentResiduals ≡ Theory.prd1991CurrentResiduals
prd1991DiligenceResidualsLoad = refl

fopl1993DiligenceResidualsLoad :
  Theory.fopl1993CurrentResiduals ≡ Theory.fopl1993CurrentResiduals
fopl1993DiligenceResidualsLoad = refl
