module DASHI.Physics.YangMills.BalabanClayBranchHeadReceiptSurface where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Branch-head verification receipt surface. These fields describe evidence a
-- clean run must provide; they do not promote an unchecked branch head.
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
    categoricityLpReuseLedgerChecked : Bool

    setoidBackendSpineChecked : Bool
    constructiveRealCapabilityHierarchyChecked : Bool
    constructiveRealTransportCapabilitiesChecked : Bool
    constructiveCompleteRealPackageChecked : Bool
    bishopFastCauchyCapabilityPackagesChecked : Bool
    constructiveRealCategoricityChecked : Bool
    bishopBackendChecked : Bool
    fastCauchyBackendChecked : Bool
    bishopFastCauchyEquivalenceSeamChecked : Bool
    bishopFastCauchyCommonCompletionChecked : Bool
    bishopFastCauchyCategoricityInstanceChecked : Bool
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
    t5LpUniformIntegrabilityChecked : Bool
    t5LpPhysicalMeasureAdapterChecked : Bool
    legacyGaugeRGMeasureReuseChecked : Bool

    gate4ValidationAggregateChecked : Bool
    gate4LiteralPeriodicGeometryChecked : Bool
    gate4PeriodicAdjacencyHolonomyChecked : Bool
    gate4BondPathBianchiChecked : Bool
    gate4RationalSU2ExactGroupChecked : Bool
    gate4PeriodicCoordinateClosureChecked : Bool
    gate4PeriodicTraversalGeometryReuseChecked : Bool
    gate4TransportedBianchiCancellationChecked : Bool
    gate4WilsonBoltzmannSuppressionChecked : Bool
    gate4PhysicalTDensityChecked : Bool
    gate4ReferenceFibreNormalizationChecked : Bool
    gate4ReferenceFibrePositiveMassChecked : Bool
    gate4PhysicalReferenceMassAssemblyChecked : Bool
    gate4FiniteTOperationChecked : Bool
    gate4TStructuralSuppressionReductionChecked : Bool
    gate4FiniteROperationChecked : Bool
    gate4RBoundarySupportChecked : Bool
    gate4CountingLocalizationReuseChecked : Bool
    gate4RCanonicalTraceReuseChecked : Bool
    gate4RRepresentationExponentiationChecked : Bool
    gate4P0CompatibilityAuditChecked : Bool
    gate4AnalyticityCouplingControlChecked : Bool
    gate4SuppressionRecurrenceChecked : Bool
    gate4CombinedSmallLargeAssemblyChecked : Bool
    gate4PhysicalOneStepClosureChecked : Bool
    gate4AbsorptionAndUVAssemblyChecked : Bool
    t5PublishedTerminalCriteriaChecked : Bool
    t5OS1RotationRestorationChecked : Bool
    t5ClusteringToTransferGapChecked : Bool
    concreteUVToMassGapDependencyChecked : Bool
    physicalContinuumOSGapBridgeChecked : Bool
    clusteringLocatorAuditChecked : Bool
    dongLiDissipativeBernsteinChecked : Bool

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
    focusedCategoricityLpReuseLedgerChecked : Set
    bishopGitlinkMatchesReceipt : Set
    bishopLibraryResolvesInAgda29 : Set
    bishopConstructiveRealBridgeTypechecks : Set
    bishopElementarySeriesTypechecks : Set
    bishopFrontierLedgerTypechecks : Set

    realBackendSpineTypechecks : Set
    capabilityHierarchyTransportAndCategoricityTypecheck : Set
    stableCompleteRealPackagesTypecheck : Set
    bishopAndFastCauchyBackendsTypecheck : Set
    concreteEquivalenceSeamTypechecks : Set
    commonCompletionAndCategoricityInstanceTypechecks : Set
    legacyEquivalenceAuthorityTypechecks : Set
    canonicalBackendAndHoTTBoundaryTypecheck : Set
    bishopSeriesAndCoefficientAdaptersTypecheck : Set

    t2TraversalAndQuaternionClosureTypecheck : Set
    t3MechanismAndGreenClosureTypecheck : Set
    t4WardAndBoxClosureTypecheck : Set
    t5PhysicalClosureTypecheck : Set
    lpUniformIntegrabilityPhysicalMeasureAndReuseAdaptersTypecheck : Set

    gate4ValidationAggregateTypechecks : Set
    gate4LiteralPeriodicGeometryTypechecks : Set
    gate4PeriodicAdjacencyHolonomyTypechecks : Set
    gate4BondPathBianchiTypechecks : Set
    gate4RationalSU2ExactGroupTypechecks : Set
    gate4PeriodicCoordinateClosureTypechecks : Set
    gate4PeriodicTraversalGeometryReuseTypechecks : Set
    gate4TransportedBianchiCancellationTypechecks : Set
    gate4WilsonBoltzmannSuppressionTypechecks : Set
    gate4PhysicalTDensityTypechecks : Set
    gate4ReferenceFibreNormalizationTypechecks : Set
    gate4ReferenceFibrePositiveMassTypechecks : Set
    gate4PhysicalReferenceMassAssemblyTypechecks : Set
    gate4FiniteTOperationTypechecks : Set
    gate4TStructuralSuppressionReductionTypechecks : Set
    gate4FiniteROperationTypechecks : Set
    gate4RBoundarySupportTypechecks : Set
    gate4CountingLocalizationReuseTypechecks : Set
    gate4RCanonicalTraceReuseTypechecks : Set
    gate4RRepresentationExponentiationTypechecks : Set
    gate4P0CompatibilityAuditTypechecks : Set
    gate4AnalyticityCouplingControlTypechecks : Set
    gate4SuppressionRecurrenceTypechecks : Set
    gate4CombinedSmallLargeAssemblyTypechecks : Set
    gate4PhysicalOneStepClosureTypechecks : Set
    gate4AbsorptionAndUVAssemblyTypechecks : Set
    t5PublishedTerminalCriteriaTypechecks : Set
    t5OS1RotationRestorationTypechecks : Set
    t5ClusteringToTransferGapTypechecks : Set
    concreteUVToMassGapDependencyTypechecks : Set
    physicalContinuumOSGapBridgeTypechecks : Set
    clusteringLocatorAuditTypechecks : Set
    dongLiDissipativeBernsteinTypechecks : Set

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

focusedCategoricityLpReuseLedgerTypecheckLevel : ProofLevel
focusedCategoricityLpReuseLedgerTypecheckLevel = conditional

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

stableCompleteRealPackageTypecheckLevel : ProofLevel
stableCompleteRealPackageTypecheckLevel = conditional

categoricityTrancheTypecheckLevel : ProofLevel
categoricityTrancheTypecheckLevel = conditional

t2ClosureTrancheTypecheckLevel : ProofLevel
t2ClosureTrancheTypecheckLevel = conditional

t3ClosureTrancheTypecheckLevel : ProofLevel
t3ClosureTrancheTypecheckLevel = conditional

t4ClosureTrancheTypecheckLevel : ProofLevel
t4ClosureTrancheTypecheckLevel = conditional

t5ClosureTrancheTypecheckLevel : ProofLevel
t5ClosureTrancheTypecheckLevel = conditional

t5LpReuseTrancheTypecheckLevel : ProofLevel
t5LpReuseTrancheTypecheckLevel = conditional

gate4ValidationAggregateTypecheckLevel : ProofLevel
gate4ValidationAggregateTypecheckLevel = conditional

gate4LiteralPeriodicGeometryTypecheckLevel : ProofLevel
gate4LiteralPeriodicGeometryTypecheckLevel = conditional

gate4PeriodicAdjacencyHolonomyTypecheckLevel : ProofLevel
gate4PeriodicAdjacencyHolonomyTypecheckLevel = conditional

gate4BondPathBianchiTypecheckLevel : ProofLevel
gate4BondPathBianchiTypecheckLevel = conditional

gate4RationalSU2ExactGroupTypecheckLevel : ProofLevel
gate4RationalSU2ExactGroupTypecheckLevel = conditional

gate4PeriodicCoordinateClosureTypecheckLevel : ProofLevel
gate4PeriodicCoordinateClosureTypecheckLevel = conditional

gate4PeriodicTraversalGeometryReuseTypecheckLevel : ProofLevel
gate4PeriodicTraversalGeometryReuseTypecheckLevel = conditional

gate4TransportedBianchiCancellationTypecheckLevel : ProofLevel
gate4TransportedBianchiCancellationTypecheckLevel = conditional

gate4WilsonBoltzmannSuppressionTypecheckLevel : ProofLevel
gate4WilsonBoltzmannSuppressionTypecheckLevel = conditional

gate4PhysicalTDensityTypecheckLevel : ProofLevel
gate4PhysicalTDensityTypecheckLevel = conditional

gate4ReferenceFibreNormalizationTypecheckLevel : ProofLevel
gate4ReferenceFibreNormalizationTypecheckLevel = conditional

gate4ReferenceFibrePositiveMassTypecheckLevel : ProofLevel
gate4ReferenceFibrePositiveMassTypecheckLevel = conditional

gate4PhysicalReferenceMassAssemblyTypecheckLevel : ProofLevel
gate4PhysicalReferenceMassAssemblyTypecheckLevel = conditional

gate4FiniteTOperationTypecheckLevel : ProofLevel
gate4FiniteTOperationTypecheckLevel = conditional

gate4TStructuralSuppressionReductionTypecheckLevel : ProofLevel
gate4TStructuralSuppressionReductionTypecheckLevel = conditional

gate4FiniteROperationTypecheckLevel : ProofLevel
gate4FiniteROperationTypecheckLevel = conditional

gate4RBoundarySupportTypecheckLevel : ProofLevel
gate4RBoundarySupportTypecheckLevel = conditional

gate4CountingLocalizationReuseTypecheckLevel : ProofLevel
gate4CountingLocalizationReuseTypecheckLevel = conditional

gate4RCanonicalTraceReuseTypecheckLevel : ProofLevel
gate4RCanonicalTraceReuseTypecheckLevel = conditional

gate4RRepresentationExponentiationTypecheckLevel : ProofLevel
gate4RRepresentationExponentiationTypecheckLevel = conditional

gate4P0CompatibilityAuditTypecheckLevel : ProofLevel
gate4P0CompatibilityAuditTypecheckLevel = conditional

gate4AnalyticityCouplingControlTypecheckLevel : ProofLevel
gate4AnalyticityCouplingControlTypecheckLevel = conditional

gate4SuppressionRecurrenceTypecheckLevel : ProofLevel
gate4SuppressionRecurrenceTypecheckLevel = conditional

gate4CombinedSmallLargeAssemblyTypecheckLevel : ProofLevel
gate4CombinedSmallLargeAssemblyTypecheckLevel = conditional

gate4PhysicalOneStepClosureTypecheckLevel : ProofLevel
gate4PhysicalOneStepClosureTypecheckLevel = conditional

gate4AbsorptionAndUVAssemblyTypecheckLevel : ProofLevel
gate4AbsorptionAndUVAssemblyTypecheckLevel = conditional

t5PublishedTerminalCriteriaTypecheckLevel : ProofLevel
t5PublishedTerminalCriteriaTypecheckLevel = conditional

t5OS1RotationRestorationTypecheckLevel : ProofLevel
t5OS1RotationRestorationTypecheckLevel = conditional

t5ClusteringToTransferGapTypecheckLevel : ProofLevel
t5ClusteringToTransferGapTypecheckLevel = conditional

concreteUVToMassGapDependencyTypecheckLevel : ProofLevel
concreteUVToMassGapDependencyTypecheckLevel = conditional

physicalContinuumOSGapBridgeTypecheckLevel : ProofLevel
physicalContinuumOSGapBridgeTypecheckLevel = conditional

clusteringLocatorAuditTypecheckLevel : ProofLevel
clusteringLocatorAuditTypecheckLevel = conditional

dongLiDissipativeBernsteinTypecheckLevel : ProofLevel
dongLiDissipativeBernsteinTypecheckLevel = conditional

publicYangMillsAggregateTypecheckLevel : ProofLevel
publicYangMillsAggregateTypecheckLevel = conditional

postulateFreeChangedSurfaceLevel : ProofLevel
postulateFreeChangedSurfaceLevel = conditional

cleanAgda29BranchHeadReceiptLevel : ProofLevel
cleanAgda29BranchHeadReceiptLevel = conditional
