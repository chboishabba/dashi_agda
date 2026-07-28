module DASHI.Physics.YangMills.BalabanClayBranchHeadReceiptSurface where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Branch-head verification receipt surface.
--
-- The user deliberately owns execution of Agda.  This module therefore records
-- the exact evidence that a later clean run must provide without falsely
-- promoting any unchecked branch head.
------------------------------------------------------------------------

record BranchHeadAgdaReceipt : Set where
  constructor branchHeadReceipt
  field
    repositoryHead : String
    agdaRevision : String
    standardLibraryRevision : String
    bishopSubmoduleRevision : String
    cleanInterfaceDeletionPerformed : Bool
    literatureAuditPassed : Bool
    frontierClaimsAuditPassed : Bool
    frontierAggregateAuditPassed : Bool
    bishopSubmodulePinnedChecked : Bool
    bishopLibraryResolutionChecked : Bool
    bishopConstructiveRealBridgeChecked : Bool
    bishopElementarySeriesChecked : Bool
    bishopFrontierLedgerChecked : Bool

    setoidBackendSpineChecked : Bool
    bishopBackendChecked : Bool
    fastCauchyBackendChecked : Bool
    bishopFastCauchyEquivalenceSeamChecked : Bool
    legacyEquivalenceAuthorityChecked : Bool
    canonicalBackendSelectionChecked : Bool
    cubicalHoTTBoundaryChecked : Bool
    bishopSeriesAdapterChecked : Bool
    reciprocalCoefficientConstructionChecked : Bool

    mechanismAtomBoundsChecked : Bool
    finiteStencilStripImageClosureChecked : Bool
    quaternionTailCollarClosureChecked : Bool
    periodicTraversalDecoderChecked : Bool
    wardBoxCertificateClosureChecked : Bool
    physicalT5TailMomentMeasureClosureChecked : Bool

    changedModules : List String
    constructiveProducerAggregateChecked : Bool
    frontierLedgerAggregateChecked : Bool
    configuredFrontierLedgerChecked : Bool
    publicYangMillsAggregateChecked : Bool
    changedSurfacePostulateFree : Bool

open BranchHeadAgdaReceipt public

record AuthoritativeBranchHeadEvidence
    (receipt : BranchHeadAgdaReceipt) : Set where
  field
    allChangedModulesChecked : Set
    constructiveProducerChecked : Set
    frontierLedgerChecked : Set
    configuredFrontierLedgerChecked : Set
    bishopGitlinkMatchesReceipt : Set
    bishopLibraryResolvesInAgda29 : Set
    bishopConstructiveRealBridgeTypechecks : Set
    bishopElementarySeriesTypechecks : Set
    bishopFrontierLedgerTypechecks : Set

    realBackendSpineTypechecks : Set
    bishopAndFastCauchyBackendsTypecheck : Set
    concreteEquivalenceSeamTypechecks : Set
    legacyEquivalenceAuthorityTypechecks : Set
    canonicalBackendAndHoTTBoundaryTypecheck : Set
    bishopSeriesAndCoefficientAdaptersTypecheck : Set

    t2TraversalAndQuaternionClosureTypecheck : Set
    t3MechanismAndGreenClosureTypecheck : Set
    t4WardAndBoxClosureTypecheck : Set
    t5PhysicalClosureTypecheck : Set

    publicAggregateChecked : Set
    postulateFreeChangedSurface : Set

open AuthoritativeBranchHeadEvidence public

changedYangMillsModulesTypecheckLevel : ProofLevel
changedYangMillsModulesTypecheckLevel = conditional

constructiveProducerAggregateTypecheckLevel : ProofLevel
constructiveProducerAggregateTypecheckLevel = conditional

frontierLedgerAggregateTypecheckLevel : ProofLevel
frontierLedgerAggregateTypecheckLevel = conditional

configuredFrontierLedgerAggregateTypecheckLevel : ProofLevel
configuredFrontierLedgerAggregateTypecheckLevel = conditional

bishopSubmodulePinReceiptLevel : ProofLevel
bishopSubmodulePinReceiptLevel = conditional

bishopConstructiveRealBridgeTypecheckLevel : ProofLevel
bishopConstructiveRealBridgeTypecheckLevel = conditional

bishopElementarySeriesTypecheckLevel : ProofLevel
bishopElementarySeriesTypecheckLevel = conditional

bishopFrontierLedgerTypecheckLevel : ProofLevel
bishopFrontierLedgerTypecheckLevel = conditional

realBackendTrancheTypecheckLevel : ProofLevel
realBackendTrancheTypecheckLevel = conditional

t2ClosureTrancheTypecheckLevel : ProofLevel
t2ClosureTrancheTypecheckLevel = conditional

t3ClosureTrancheTypecheckLevel : ProofLevel
t3ClosureTrancheTypecheckLevel = conditional

t4ClosureTrancheTypecheckLevel : ProofLevel
t4ClosureTrancheTypecheckLevel = conditional

t5ClosureTrancheTypecheckLevel : ProofLevel
t5ClosureTrancheTypecheckLevel = conditional

publicYangMillsAggregateTypecheckLevel : ProofLevel
publicYangMillsAggregateTypecheckLevel = conditional

postulateFreeChangedSurfaceLevel : ProofLevel
postulateFreeChangedSurfaceLevel = conditional

cleanAgda29BranchHeadReceiptLevel : ProofLevel
cleanAgda29BranchHeadReceiptLevel = conditional
