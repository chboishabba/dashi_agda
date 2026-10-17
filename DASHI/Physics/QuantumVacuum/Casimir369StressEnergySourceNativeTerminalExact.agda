module DASHI.Physics.QuantumVacuum.Casimir369StressEnergySourceNativeTerminalExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)

import DASHI.Physics.QuantumVacuum.Casimir369StressEnergyTerminalMaxCutExact as Legacy
import DASHI.Physics.QuantumVacuum.CasimirSelectedQFTSourceNativeHostMaxCutExact as SourceHost
import DASHI.Physics.QuantumVacuum.CasimirRound131PinnedRecoveryCompilerExact as PinnedRecovery
import DASHI.Physics.QuantumVacuum.CasimirPinnedR457SourceNativeCompilerExact as PinnedR457
import DASHI.Physics.QuantumVacuum.CasimirQuaternionSU2GroupLawBridgeExact as GroupLaw
import DASHI.Physics.QuantumVacuum.CasimirU1RestrictedSelectedQFTStressExact as U1Stress
import DASHI.Physics.QuantumVacuum.CasimirFreeMaxwellActionNormalizationExact as FreeNormalization
import DASHI.Physics.QuantumVacuum.CasimirSide4CartanCurvatureClosureExact as Side4Cartan
import DASHI.Physics.QuantumVacuum.CasimirU1ActionVariationMaxCutExact as Action
import DASHI.Physics.QuantumVacuum.CasimirU1SelectedStressReadoutAttachmentExact as StressReadout
import DASHI.Physics.QuantumVacuum.CasimirU1ModeRenormalizedStressAttachmentExact as ModeStress
import DASHI.Physics.QuantumVacuum.CasimirSelectedStressMetricBasisSymmetryExact as MetricSymmetry
import DASHI.Physics.Foundations.Round131AllSectorAssemblyFrontierExact as Round131
import DASHI.Physics.Foundations.BalabanQ1FiniteTangentCurveReductionExact as Q1
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanContinuumMetricStressPairingRound130Exact as R130
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionRecoveryRound136Exact as R136

------------------------------------------------------------------------
-- SOURCE-NATIVE TERMINAL, PRIMITIVE-LEAF RECUT
--
-- The earlier terminal started too late: it treated R457/Round131 attachment as
-- the first input and hid the still-conditional source objects below it.  The
-- canonical pinned route now contracts the wrapper chain
--
--   R114 + R119 -> R120
--   R120 + R122 -> R123
--   R123 + R124 -> R125
--   pinned continuum + R125 -> R126
--   R126 + R127 -> R128 -> R457
--
-- and QFTRecoveryReceipt compiles selected-target identity -> Round131 recovery.
-- Thus the terminal begins at the first theorem-bearing source leaves.
------------------------------------------------------------------------

legacyTerminalBoundary : Legacy.Casimir369StressEnergyTerminalBoundary
legacyTerminalBoundary = Legacy.canonicalTerminalBoundary

sourceNativeHostBoundary : SourceHost.CasimirSelectedQFTSourceNativeHostBoundary
sourceNativeHostBoundary = SourceHost.canonicalSourceNativeHostBoundary

pinnedRecoveryBoundary : PinnedRecovery.CasimirRound131PinnedRecoveryBoundary
pinnedRecoveryBoundary = PinnedRecovery.canonicalRound131PinnedRecoveryBoundary

pinnedR457SourceNativeBoundary : PinnedR457.CasimirPinnedR457SourceNativeBoundary
pinnedR457SourceNativeBoundary = PinnedR457.canonicalPinnedR457SourceNativeBoundary

quaternionGroupLawBoundary : GroupLaw.CasimirQuaternionSU2GroupLawBoundary
quaternionGroupLawBoundary = GroupLaw.canonicalQuaternionSU2GroupLawBoundary

selectedQFTCartanFieldBoundary : U1Stress.CasimirU1RestrictedSelectedQFTStressBoundary
selectedQFTCartanFieldBoundary = U1Stress.canonicalCasimirU1RestrictedSelectedQFTStressBoundary

freeMaxwellNormalizationBoundary : FreeNormalization.CasimirFreeMaxwellNormalizationBoundary
freeMaxwellNormalizationBoundary = FreeNormalization.canonicalFreeMaxwellNormalizationBoundary

side4CartanCurvatureBoundary : Side4Cartan.CasimirSide4CartanCurvatureBoundary
side4CartanCurvatureBoundary = Side4Cartan.canonicalSide4CartanCurvatureBoundary

actionVariationBoundary : Action.CasimirU1ActionVariationBoundary
actionVariationBoundary = Action.canonicalCasimirU1ActionVariationBoundary

selectedStressReadoutBoundary : StressReadout.CasimirSelectedStressReadoutBoundary
selectedStressReadoutBoundary = StressReadout.canonicalSelectedStressReadoutBoundary

modeRenormalizedStressBoundary : ModeStress.CasimirU1ModeRenormalizedStressBoundary
modeRenormalizedStressBoundary = ModeStress.canonicalModeRenormalizedStressBoundary

metricBasisSymmetryBoundary : MetricSymmetry.CasimirSelectedStressMetricBasisBoundary
metricBasisSymmetryBoundary = MetricSymmetry.canonicalSelectedStressMetricBasisBoundary

round132SelectedGeneratedActionOwner : String
round132SelectedGeneratedActionOwner =
  "DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact"

q1FiniteTangentCurveOwner : String
q1FiniteTangentCurveOwner =
  "DASHI.Physics.Foundations.BalabanQ1FiniteTangentCurveReductionExact"

round130CanonicalMetricStressPairingOwner : String
round130CanonicalMetricStressPairingOwner =
  "DASHI.Physics.YangMills.BalabanContinuumMetricStressPairingRound130Exact"

round136GeneratedActionRecoveryOwner : String
round136GeneratedActionRecoveryOwner =
  "DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionRecoveryRound136Exact"

round132CompilerLevel : ProofLevel
round132CompilerLevel = R132.unifiedGeneratedActionDensityCompilerLevel

q1UsesExactPresentCutTangent : Bool
q1UsesExactPresentCutTangent = Q1.q1CurveUsesExactPresentCutFiniteTangent

round130CompilerLevel : ProofLevel
round130CompilerLevel = R130.continuumMetricStressPairingCompilerLevel

round136CompilerLevel : ProofLevel
round136CompilerLevel = R136.unifiedGeneratedActionRecoveryCompilerLevel

record CasimirSourceNativeTerminalBoundary : Set where
  constructor casimir-source-native-terminal-boundary
  field
    sourceNativeHostCompilerPaid : Bool
    pinnedR457SourceNativeCompilerPaid : Bool
    selectedTargetToRound131RecoveryCompilerPaid : Bool
    independentRound131RecoveredQFTAttachmentRequired : Bool
    independentR457PinnedConstructionIdentityRequired : Bool
    formalProjectionCompatibilityCompilerPaid : Bool
    independentProjectionCompatibilityPaymentRequired : Bool
    r457RecoveryEqualityCompilerPaid : Bool
    pinnedSourceNativeSelectionCompilerPaid : Bool
    independentPinnedSourceNativeSelectionRequired : Bool
    independentCompactSimplePaymentRequired : Bool
    quaternionSU2GroupLawBridgePaid : Bool
    selectedGroupStructureRealizationCompilerPaid : Bool
    independentAllGroupsStructureInterpretationRequired : Bool
    selectedQFTCartanFieldRealizationInterfacePaid : Bool
    freeMaxwellActionNormalizationInterfacePaid : Bool
    measuredAlphaEMRequiredForIdealCasimirActionWeld : Bool
    side4CartanCurlClosureCompilerPaid : Bool
    independentFiniteCartanCurlClosurePaymentRequired : Bool
    cartanFieldBracketCompilerPaid : Bool
    invariantPairingCompilerPaid : Bool
    abelianCurvatureCompilerPaid : Bool
    quadraticActionDensityCompilerPaid : Bool
    independentRestrictedYMMaxwellActionEqualityRequired : Bool
    metricVariationTransportCompilerPaid : Bool
    independentMetricVariationEqualityRequired : Bool
    selectedStressToMaxwellReadoutCompilerPaid : Bool
    independentRestrictedQuantumStressMaxwellEqualityRequired : Bool
    existingModeBoundaryRenormalizationWeldReused : Bool
    secondConductingPlateBoundaryRequired : Bool
    secondRenormalizationPrescriptionRequired : Bool
    round132SelectedGeneratedActionOwnerReused : Bool
    q1FiniteTangentCurveOwnerReused : Bool
    round130CanonicalMetricStressPairingOwnerReused : Bool
    metricBasisStressSymmetryCompilerPaid : Bool
    independentRestrictedStressSymmetryPaymentRequired : Bool

    pinnedYangMillsConstructionInhabited : Bool
    literalStressCoordinatePaid : Bool
    canonicalMetricSelectedStressSemanticsPaid : Bool
    literalDensityAnchoringPaid : Bool
    literalDensityFiniteMeasureWeldPaid : Bool
    sourceOSLiteralSchwingerWeldPaid : Bool
    pinnedLiteralSelectedQFTTargetIdentityPaid : Bool
    selectedGroupQuaternionSU2RealizationPaid : Bool
    selectedQFTCartanFieldRealizationPaid : Bool
    freeMaxwellActionNormalizationPaid : Bool
    sameObjectNondegenerateCurvatureFormulaPaid : Bool
    selectedNonlinearExteriorCartanTransportPaid : Bool
    casimirRound132GeneratedActionAttachmentPaid : Bool
    casimirQ1FiniteTangentCurveAttachmentPaid : Bool
    casimirRound130StressReadoutAttachmentPaid : Bool
    selectedQFTStressMetricVariationReadoutAttachmentPaid : Bool
    maxwellReadoutSameRenormalizedModeStressAttachmentPaid : Bool
    selectedStressMetricBasisAttachmentPaid : Bool
    brownMaclayTenComponentValuesPaid : Bool
    allSectorAssemblyPaid : Bool
    einsteinCommonMetricVariationPaid : Bool
    commonMetricProducerLanguagePaid : Bool
    commonCasimirActionVariationIdentificationPaid : Bool

open CasimirSourceNativeTerminalBoundary public

canonicalSourceNativeTerminalBoundary : CasimirSourceNativeTerminalBoundary
canonicalSourceNativeTerminalBoundary =
  casimir-source-native-terminal-boundary
    true true true false false true false true true false false true true false true true false true false
    true true true true false true false true false true false false true true true true false
    false false false false false false false false false false false false false false false false false false false false false false false

data RemainingSourceNativeCasimirBlocker : Set where
  missingPinnedYangMillsConstructionInhabitant : RemainingSourceNativeCasimirBlocker
  missingR114LiteralStressCoordinate : RemainingSourceNativeCasimirBlocker
  missingR119CanonicalMetricSelectedStressSemantics : RemainingSourceNativeCasimirBlocker
  missingR122LiteralDensityAnchoring : RemainingSourceNativeCasimirBlocker
  missingR124LiteralDensityFiniteMeasureWeld : RemainingSourceNativeCasimirBlocker
  missingR127SourceOSLiteralSchwingerWeld : RemainingSourceNativeCasimirBlocker
  missingPinnedLiteralSelectedQFTTargetIdentity : RemainingSourceNativeCasimirBlocker
  missingSelectedGroupQuaternionSU2Realization : RemainingSourceNativeCasimirBlocker
  missingSelectedQFTCartanFieldRealization : RemainingSourceNativeCasimirBlocker
  missingFreeMaxwellActionNormalization : RemainingSourceNativeCasimirBlocker
  missingSameObjectNondegenerateCurvatureFormulaAttachment : RemainingSourceNativeCasimirBlocker
  missingSelectedNonlinearExteriorCartanTransport : RemainingSourceNativeCasimirBlocker
  missingCasimirRound132GeneratedActionAttachment : RemainingSourceNativeCasimirBlocker
  missingCasimirQ1FiniteTangentCurveAttachment : RemainingSourceNativeCasimirBlocker
  missingCasimirRound130StressReadoutAttachment : RemainingSourceNativeCasimirBlocker
  missingSelectedQFTStressMetricVariationReadoutAttachment : RemainingSourceNativeCasimirBlocker
  missingMaxwellReadoutSameRenormalizedModeStressAttachment : RemainingSourceNativeCasimirBlocker
  missingSelectedStressMetricBasisAttachment : RemainingSourceNativeCasimirBlocker
  missingBrownMaclayTenIndependentComponentValues : RemainingSourceNativeCasimirBlocker
  missingRound131AllSectorAssembly : RemainingSourceNativeCasimirBlocker
  missingEinsteinCommonMetricVariation : RemainingSourceNativeCasimirBlocker
  missingCommonMetricProducerLanguage : RemainingSourceNativeCasimirBlocker
  missingCasimirCommonActionVariationIdentification : RemainingSourceNativeCasimirBlocker
  missingSemiclassicalGravitySameObjectWeld : RemainingSourceNativeCasimirBlocker
  missingDirectStressOrGravityMeasurement : RemainingSourceNativeCasimirBlocker
  missingExactHeadKernelReceipt : RemainingSourceNativeCasimirBlocker

firstUnificationBlocker : RemainingSourceNativeCasimirBlocker
firstUnificationBlocker = missingPinnedYangMillsConstructionInhabitant
secondUnificationBlocker : RemainingSourceNativeCasimirBlocker
secondUnificationBlocker = missingR114LiteralStressCoordinate
thirdUnificationBlocker : RemainingSourceNativeCasimirBlocker
thirdUnificationBlocker = missingR119CanonicalMetricSelectedStressSemantics
fourthUnificationBlocker : RemainingSourceNativeCasimirBlocker
fourthUnificationBlocker = missingR122LiteralDensityAnchoring
fifthUnificationBlocker : RemainingSourceNativeCasimirBlocker
fifthUnificationBlocker = missingR124LiteralDensityFiniteMeasureWeld
sixthUnificationBlocker : RemainingSourceNativeCasimirBlocker
sixthUnificationBlocker = missingR127SourceOSLiteralSchwingerWeld
seventhUnificationBlocker : RemainingSourceNativeCasimirBlocker
seventhUnificationBlocker = missingPinnedLiteralSelectedQFTTargetIdentity
eighthUnificationBlocker : RemainingSourceNativeCasimirBlocker
eighthUnificationBlocker = missingSelectedGroupQuaternionSU2Realization
ninthUnificationBlocker : RemainingSourceNativeCasimirBlocker
ninthUnificationBlocker = missingSelectedQFTCartanFieldRealization
tenthUnificationBlocker : RemainingSourceNativeCasimirBlocker
tenthUnificationBlocker = missingFreeMaxwellActionNormalization
eleventhUnificationBlocker : RemainingSourceNativeCasimirBlocker
eleventhUnificationBlocker = missingSameObjectNondegenerateCurvatureFormulaAttachment
twelfthUnificationBlocker : RemainingSourceNativeCasimirBlocker
twelfthUnificationBlocker = missingSelectedNonlinearExteriorCartanTransport
thirteenthUnificationBlocker : RemainingSourceNativeCasimirBlocker
thirteenthUnificationBlocker = missingCasimirRound132GeneratedActionAttachment
fourteenthUnificationBlocker : RemainingSourceNativeCasimirBlocker
fourteenthUnificationBlocker = missingCasimirQ1FiniteTangentCurveAttachment
fifteenthUnificationBlocker : RemainingSourceNativeCasimirBlocker
fifteenthUnificationBlocker = missingCasimirRound130StressReadoutAttachment
sixteenthUnificationBlocker : RemainingSourceNativeCasimirBlocker
sixteenthUnificationBlocker = missingSelectedQFTStressMetricVariationReadoutAttachment
seventeenthUnificationBlocker : RemainingSourceNativeCasimirBlocker
seventeenthUnificationBlocker = missingMaxwellReadoutSameRenormalizedModeStressAttachment
eighteenthUnificationBlocker : RemainingSourceNativeCasimirBlocker
eighteenthUnificationBlocker = missingSelectedStressMetricBasisAttachment
nineteenthUnificationBlocker : RemainingSourceNativeCasimirBlocker
nineteenthUnificationBlocker = missingBrownMaclayTenIndependentComponentValues
twentiethUnificationBlocker : RemainingSourceNativeCasimirBlocker
twentiethUnificationBlocker = missingRound131AllSectorAssembly
twentyFirstUnificationBlocker : RemainingSourceNativeCasimirBlocker
twentyFirstUnificationBlocker = missingEinsteinCommonMetricVariation
twentySecondUnificationBlocker : RemainingSourceNativeCasimirBlocker
twentySecondUnificationBlocker = missingCommonMetricProducerLanguage
twentyThirdUnificationBlocker : RemainingSourceNativeCasimirBlocker
twentyThirdUnificationBlocker = missingCasimirCommonActionVariationIdentification

firstAllSectorAssemblyLeaf : Round131.Round131AllSectorAssemblyLeaf
firstAllSectorAssemblyLeaf = Round131.commonSectorMetricAndScalarConvention

firstGravityBlocker : RemainingSourceNativeCasimirBlocker
firstGravityBlocker = missingSemiclassicalGravitySameObjectWeld

firstExperimentalBlocker : RemainingSourceNativeCasimirBlocker
firstExperimentalBlocker = missingDirectStressOrGravityMeasurement

data RetiredRound131AttachmentBlockerAutomaticallyReturns : Set where
data RetiredR457PinnedIdentityBlockerAutomaticallyReturns : Set where
data RetiredR120WrapperBlockerAutomaticallyReturns : Set where
data RetiredR123WrapperBlockerAutomaticallyReturns : Set where
data RetiredR125WrapperBlockerAutomaticallyReturns : Set where
data RetiredR126WrapperBlockerAutomaticallyReturns : Set where
data RetiredGenericActionFunctionalBlockerAutomaticallyReturns : Set where
data RetiredGenericMetricPathBlockerAutomaticallyReturns : Set where
data RetiredGenericStressReadoutBlockerAutomaticallyReturns : Set where
data RetiredIndependentStressSymmetryBlockerAutomaticallyReturns : Set where

retiredRound131AttachmentBlockerDoesNotReturn : RetiredRound131AttachmentBlockerAutomaticallyReturns → ⊥
retiredRound131AttachmentBlockerDoesNotReturn ()
retiredR457PinnedIdentityBlockerDoesNotReturn : RetiredR457PinnedIdentityBlockerAutomaticallyReturns → ⊥
retiredR457PinnedIdentityBlockerDoesNotReturn ()
retiredR120WrapperBlockerDoesNotReturn : RetiredR120WrapperBlockerAutomaticallyReturns → ⊥
retiredR120WrapperBlockerDoesNotReturn ()
retiredR123WrapperBlockerDoesNotReturn : RetiredR123WrapperBlockerAutomaticallyReturns → ⊥
retiredR123WrapperBlockerDoesNotReturn ()
retiredR125WrapperBlockerDoesNotReturn : RetiredR125WrapperBlockerAutomaticallyReturns → ⊥
retiredR125WrapperBlockerDoesNotReturn ()
retiredR126WrapperBlockerDoesNotReturn : RetiredR126WrapperBlockerAutomaticallyReturns → ⊥
retiredR126WrapperBlockerDoesNotReturn ()
retiredGenericActionFunctionalBlockerDoesNotReturn : RetiredGenericActionFunctionalBlockerAutomaticallyReturns → ⊥
retiredGenericActionFunctionalBlockerDoesNotReturn ()
retiredGenericMetricPathBlockerDoesNotReturn : RetiredGenericMetricPathBlockerAutomaticallyReturns → ⊥
retiredGenericMetricPathBlockerDoesNotReturn ()
retiredGenericStressReadoutBlockerDoesNotReturn : RetiredGenericStressReadoutBlockerAutomaticallyReturns → ⊥
retiredGenericStressReadoutBlockerDoesNotReturn ()
retiredIndependentStressSymmetryBlockerDoesNotReturn : RetiredIndependentStressSymmetryBlockerAutomaticallyReturns → ⊥
retiredIndependentStressSymmetryBlockerDoesNotReturn ()

sourceNativeTerminalReading : String
sourceNativeTerminalReading =
  "The source-native Casimir/GRQFT terminal now begins at the first theorem-bearing source objects rather than downstream recovery wrappers. No concrete PinnedYangMillsConstruction inhabitant is currently supplied. Conditional on that upstream Yang-Mills object, the local pinned-R457 route requires R114 one-coordinate same-object stress semantics, R119 canonical metric selected-stress semantics, R122 literal beta-density anchoring, R124 beta-density/literal-finite-measure identity and R127 source-OS/literal-Schwinger identity. These compile R120/R123/R125/R126/R128/R457, so Y_R457=Y_pinned is definitional on the canonical route. A single pinned-literal=qftTarget identity plus the existing QFTRecoveryReceipt then compiles Round131 recovery. All later SU2/U1/Maxwell/Casimir stress seams remain ordered after those source inputs."
