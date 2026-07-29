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
    periodicTraversalGeometryChecked : Bool

    positiveReferenceMassChecked : Bool
    physicalReferenceNormalizationAssemblyChecked : Bool
    sixFactorTPointwiseComparisonChecked : Bool

    canonicalRTraceReuseChecked : Bool
    localizedFactorReductionChecked : Bool
    existingRGPhysicalOneStepReuseChecked : Bool

    publishedTerminalCriteriaChecked : Bool
    denseRotationOS1ReductionChecked : Bool
    clusteringToTransferGapReductionChecked : Bool

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
    periodicTraversalGeometryTypechecks : Set
    positiveReferenceMassTypechecks : Set
    physicalReferenceNormalizationAssemblyTypechecks : Set
    sixFactorTPointwiseComparisonTypechecks : Set
    canonicalRTraceReuseTypechecks : Set
    localizedFactorReductionTypechecks : Set
    existingRGPhysicalOneStepReuseTypechecks : Set
    publishedTerminalCriteriaTypechecks : Set
    denseRotationOS1ReductionTypechecks : Set
    clusteringToTransferGapReductionTypechecks : Set
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

periodicTraversalGeometryTypecheckLevel : ProofLevel
periodicTraversalGeometryTypecheckLevel = conditional

positiveReferenceMassTypecheckLevel : ProofLevel
positiveReferenceMassTypecheckLevel = conditional

physicalReferenceNormalizationAssemblyTypecheckLevel : ProofLevel
physicalReferenceNormalizationAssemblyTypecheckLevel = conditional

sixFactorTPointwiseComparisonTypecheckLevel : ProofLevel
sixFactorTPointwiseComparisonTypecheckLevel = conditional

canonicalRTraceReuseTypecheckLevel : ProofLevel
canonicalRTraceReuseTypecheckLevel = conditional

localizedFactorReductionTypecheckLevel : ProofLevel
localizedFactorReductionTypecheckLevel = conditional

existingRGPhysicalOneStepReuseTypecheckLevel : ProofLevel
existingRGPhysicalOneStepReuseTypecheckLevel = conditional

publishedTerminalCriteriaTypecheckLevel : ProofLevel
publishedTerminalCriteriaTypecheckLevel = conditional

denseRotationOS1ReductionTypecheckLevel : ProofLevel
denseRotationOS1ReductionTypecheckLevel = conditional

clusteringToTransferGapReductionTypecheckLevel : ProofLevel
clusteringToTransferGapReductionTypecheckLevel = conditional

currentSurfacePostulateFreeLevel : ProofLevel
currentSurfacePostulateFreeLevel = conditional
