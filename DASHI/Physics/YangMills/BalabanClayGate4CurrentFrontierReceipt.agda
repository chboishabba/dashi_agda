module DASHI.Physics.YangMills.BalabanClayGate4CurrentFrontierReceipt where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayBranchHeadReceiptSurface as Branch
import DASHI.Physics.YangMills.BalabanClayGate4CurrentFrontierCompletionLedger as Ledger

record CurrentGate4FrontierReceipt : Set where
  constructor currentGate4FrontierReceipt
  field
    repositoryHead : String
    legacyBranchReceiptChecked : Bool
    currentFrontierLedgerChecked : Bool

    literalRationalSU2GroupChecked : Bool
    periodicCoordinateClosureChecked : Bool
    literalCubeBianchiChecked : Bool
    rationalSU2CubeBianchiChecked : Bool
    flatRationalSU2ReferenceChecked : Bool
    periodicTraversalGeometryChecked : Bool

    flatReferencePositiveWitnessChecked : Bool
    positiveReferenceMassChecked : Bool
    rationalPositiveMassReciprocalChecked : Bool
    physicalReferenceNormalizationAssemblyChecked : Bool
    compensatedSixFactorTComparisonChecked : Bool
    haarDeterminantRelativeLossReuseChecked : Bool

    canonicalRTraceReuseChecked : Bool
    orderedExponentialSeriesChecked : Bool
    localizedFactorReductionChecked : Bool
    dyadicRunningCouplingConventionChecked : Bool
    blockAveragingSummabilityChecked : Bool
    summableTailBudgetClosureChecked : Bool
    existingRGPhysicalOneStepReuseChecked : Bool

    publishedTerminalCriteriaChecked : Bool
    conditionedObservableLocalizationChecked : Bool
    perScaleDecouplingClosureChecked : Bool
    denseRotationOS1ReductionChecked : Bool
    osReconstructionCyclicityChecked : Bool
    clusteringToTransferGapReductionChecked : Bool

    harrisAlternativeQuarantined : Bool
    massGapClaimEcosystemQuarantined : Bool
    attachmentMechanismAuditChecked : Bool
    currentSurfacePostulateFree : Bool

open CurrentGate4FrontierReceipt public

record AuthoritativeCurrentGate4Evidence
    (receipt : CurrentGate4FrontierReceipt) : Set where
  field
    legacyReceiptTypechecks : Set
    currentLedgerTypechecks : Set
    rationalSU2GroupTypechecks : Set
    periodicCoordinateClosureTypechecks : Set
    literalCubeBianchiTypechecks : Set
    rationalSU2CubeBianchiTypechecks : Set
    flatRationalSU2ReferenceTypechecks : Set
    periodicTraversalGeometryTypechecks : Set
    flatReferencePositiveWitnessTypechecks : Set
    positiveReferenceMassTypechecks : Set
    rationalPositiveMassReciprocalTypechecks : Set
    physicalReferenceNormalizationAssemblyTypechecks : Set
    compensatedSixFactorTComparisonTypechecks : Set
    haarDeterminantRelativeLossReuseTypechecks : Set
    canonicalRTraceReuseTypechecks : Set
    orderedExponentialSeriesTypechecks : Set
    localizedFactorReductionTypechecks : Set
    dyadicRunningCouplingConventionTypechecks : Set
    blockAveragingSummabilityTypechecks : Set
    summableTailBudgetClosureTypechecks : Set
    existingRGPhysicalOneStepReuseTypechecks : Set
    publishedTerminalCriteriaTypechecks : Set
    conditionedObservableLocalizationTypechecks : Set
    perScaleDecouplingClosureTypechecks : Set
    denseRotationOS1ReductionTypechecks : Set
    osReconstructionCyclicityTypechecks : Set
    clusteringToTransferGapReductionTypechecks : Set
    attachmentMechanismAuditTypechecks : Set
    quarantineAuditTypechecks : Set
    currentSurfaceHasNoPostulatesOrUnsolvedMetas : Set

open AuthoritativeCurrentGate4Evidence public

legacyBranchReceiptTypecheckLevel : ProofLevel
legacyBranchReceiptTypecheckLevel = Branch.cleanAgda29BranchHeadReceiptLevel

currentFrontierLedgerTypecheckLevel : ProofLevel
currentFrontierLedgerTypecheckLevel = conditional

literalRationalSU2GroupTypecheckLevel : ProofLevel
literalRationalSU2GroupTypecheckLevel = conditional

periodicCoordinateClosureTypecheckLevel : ProofLevel
periodicCoordinateClosureTypecheckLevel = conditional

literalCubeBianchiTypecheckLevel : ProofLevel
literalCubeBianchiTypecheckLevel = conditional

rationalSU2CubeBianchiTypecheckLevel : ProofLevel
rationalSU2CubeBianchiTypecheckLevel = conditional

flatRationalSU2ReferenceTypecheckLevel : ProofLevel
flatRationalSU2ReferenceTypecheckLevel = conditional

periodicTraversalGeometryTypecheckLevel : ProofLevel
periodicTraversalGeometryTypecheckLevel = conditional

flatReferencePositiveWitnessTypecheckLevel : ProofLevel
flatReferencePositiveWitnessTypecheckLevel = conditional

positiveReferenceMassTypecheckLevel : ProofLevel
positiveReferenceMassTypecheckLevel = conditional

rationalPositiveMassReciprocalTypecheckLevel : ProofLevel
rationalPositiveMassReciprocalTypecheckLevel = conditional

physicalReferenceNormalizationAssemblyTypecheckLevel : ProofLevel
physicalReferenceNormalizationAssemblyTypecheckLevel = conditional

compensatedSixFactorTComparisonTypecheckLevel : ProofLevel
compensatedSixFactorTComparisonTypecheckLevel = conditional

haarDeterminantRelativeLossReuseTypecheckLevel : ProofLevel
haarDeterminantRelativeLossReuseTypecheckLevel = conditional

canonicalRTraceReuseTypecheckLevel : ProofLevel
canonicalRTraceReuseTypecheckLevel = conditional

orderedExponentialSeriesTypecheckLevel : ProofLevel
orderedExponentialSeriesTypecheckLevel = conditional

localizedFactorReductionTypecheckLevel : ProofLevel
localizedFactorReductionTypecheckLevel = conditional

dyadicRunningCouplingConventionTypecheckLevel : ProofLevel
dyadicRunningCouplingConventionTypecheckLevel = conditional

blockAveragingSummabilityTypecheckLevel : ProofLevel
blockAveragingSummabilityTypecheckLevel = conditional

summableTailBudgetClosureTypecheckLevel : ProofLevel
summableTailBudgetClosureTypecheckLevel = conditional

existingRGPhysicalOneStepReuseTypecheckLevel : ProofLevel
existingRGPhysicalOneStepReuseTypecheckLevel = conditional

publishedTerminalCriteriaTypecheckLevel : ProofLevel
publishedTerminalCriteriaTypecheckLevel = conditional

conditionedObservableLocalizationTypecheckLevel : ProofLevel
conditionedObservableLocalizationTypecheckLevel = conditional

perScaleDecouplingClosureTypecheckLevel : ProofLevel
perScaleDecouplingClosureTypecheckLevel = conditional

denseRotationOS1ReductionTypecheckLevel : ProofLevel
denseRotationOS1ReductionTypecheckLevel = conditional

osReconstructionCyclicityTypecheckLevel : ProofLevel
osReconstructionCyclicityTypecheckLevel = conditional

clusteringToTransferGapReductionTypecheckLevel : ProofLevel
clusteringToTransferGapReductionTypecheckLevel = conditional

attachmentMechanismAuditTypecheckLevel : ProofLevel
attachmentMechanismAuditTypecheckLevel = conditional

quarantineAuditTypecheckLevel : ProofLevel
quarantineAuditTypecheckLevel = conditional

currentSurfacePostulateFreeLevel : ProofLevel
currentSurfacePostulateFreeLevel = conditional
