module DASHI.Physics.Closure.YMSprint117CommonCarrierFeedThroughPropagator where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint110CommonCarrierHilbertIdentification
  as Carrier110
import DASHI.Physics.Closure.YMSprint110WeakCompactnessEnergyCore
  as Weak110
import DASHI.Physics.Closure.YMSprint110ClosedFormLowerSemicontinuityCriterion
  as Closed110
import DASHI.Physics.Closure.YMSprint110RecoveryCoreDensityEnergyLimsup
  as Recovery110
import DASHI.Physics.Closure.YMSprint111CommonCarrierConstructionAssembly
  as Carrier111
import DASHI.Physics.Closure.YMSprint114CommonCarrierEstimateClosureAssembly
  as Estimate114
import DASHI.Physics.Closure.YMSprint115CommonCarrierFeedThroughCriterion
  as Feed115
import DASHI.Physics.Closure.YMSprint116CommonCarrierTransferClosureReducer
  as Reducer116

------------------------------------------------------------------------
-- Sprint117 common-carrier feed-through propagator.
--
-- This module records the route that will propagate Sprint116
-- common-carrier transfer reduction through the Sprint117 norm, residual, and
-- sector feed closures.  Those Sprint117 feed modules are intentionally named
-- only by String path/name fields because sibling workers own them in
-- parallel.  The receipt is substantial and inhabited, but fail-closed: no
-- Sprint117 feed closure, external common-carrier closure, transfer lower
-- bound, continuum mass gap, or Clay Yang-Mills promotion is proved here.

sprintNumber : Nat
sprintNumber = 117

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint117CommonCarrierFeedThroughPropagator.agda"

sprint110CarrierSourcePath : String
sprint110CarrierSourcePath =
  Reducer116.sprint110CarrierSourcePath

sprint110WeakSourcePath : String
sprint110WeakSourcePath =
  Reducer116.sprint110WeakSourcePath

sprint110ClosedFormSourcePath : String
sprint110ClosedFormSourcePath =
  Reducer116.sprint110ClosedFormSourcePath

sprint110RecoverySourcePath : String
sprint110RecoverySourcePath =
  Reducer116.sprint110RecoverySourcePath

sprint111CarrierSourcePath : String
sprint111CarrierSourcePath =
  Reducer116.sprint111CarrierSourcePath

sprint114EstimateSourcePath : String
sprint114EstimateSourcePath =
  Reducer116.sprint114EstimateSourcePath

sprint115FeedThroughSourcePath : String
sprint115FeedThroughSourcePath =
  Reducer116.sprint115FeedThroughSourcePath

sprint116ReducerSourcePath : String
sprint116ReducerSourcePath =
  Reducer116.modulePath

sprint117NormFeedModuleName : String
sprint117NormFeedModuleName =
  "DASHI.Physics.Closure.YMSprint117NormClosureFeed"

sprint117ResidualFeedModuleName : String
sprint117ResidualFeedModuleName =
  "DASHI.Physics.Closure.YMSprint117ResidualClosureFeed"

sprint117SectorFeedModuleName : String
sprint117SectorFeedModuleName =
  "DASHI.Physics.Closure.YMSprint117SectorClosureFeed"

sprint117ExternalCommonCarrierModuleName : String
sprint117ExternalCommonCarrierModuleName =
  "DASHI.Physics.Closure.YMSprint117ExternalCommonCarrierClosure"

sprint117TransferLowerBoundModuleName : String
sprint117TransferLowerBoundModuleName =
  "DASHI.Physics.Closure.YMSprint117TransferLowerBoundFeedThrough"

sprint117NormFeedSourcePath : String
sprint117NormFeedSourcePath =
  "DASHI/Physics/Closure/YMSprint117NormClosureFeed.agda"

sprint117ResidualFeedSourcePath : String
sprint117ResidualFeedSourcePath =
  "DASHI/Physics/Closure/YMSprint117ResidualClosureFeed.agda"

sprint117SectorFeedSourcePath : String
sprint117SectorFeedSourcePath =
  "DASHI/Physics/Closure/YMSprint117SectorClosureFeed.agda"

sprint117ExternalCommonCarrierSourcePath : String
sprint117ExternalCommonCarrierSourcePath =
  "DASHI/Physics/Closure/YMSprint117ExternalCommonCarrierClosure.agda"

sprint117TransferLowerBoundSourcePath : String
sprint117TransferLowerBoundSourcePath =
  "DASHI/Physics/Closure/YMSprint117TransferLowerBoundFeedThrough.agda"

propagatorRecorded : Bool
propagatorRecorded = true

stableCommonCarrierInputsRecorded : Bool
stableCommonCarrierInputsRecorded = true

normFeedDependencyRecorded : Bool
normFeedDependencyRecorded = true

residualFeedDependencyRecorded : Bool
residualFeedDependencyRecorded = true

sectorFeedDependencyRecorded : Bool
sectorFeedDependencyRecorded = true

feedThroughPropagationRouteRecorded : Bool
feedThroughPropagationRouteRecorded = true

sourcePathReferenceOnlyRecorded : Bool
sourcePathReferenceOnlyRecorded = true

commonCarrierFeedThroughClosedHere : Bool
commonCarrierFeedThroughClosedHere = false

externalCommonCarrierClosedHere : Bool
externalCommonCarrierClosedHere = false

transferLowerBoundReadyHere : Bool
transferLowerBoundReadyHere = false

transferLowerBoundTheoremProvedHere : Bool
transferLowerBoundTheoremProvedHere = false

continuumMassGapProvedHere : Bool
continuumMassGapProvedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

normFeedClosedHere : Bool
normFeedClosedHere = false

residualFeedClosedHere : Bool
residualFeedClosedHere = false

sectorFeedClosedHere : Bool
sectorFeedClosedHere = false

stableCarrier110Imported : Bool
stableCarrier110Imported =
  Carrier110.commonCarrierReceiptRecorded

stableWeak110Imported : Bool
stableWeak110Imported =
  Weak110.weakCompactnessEnergyCoreRecorded

stableClosed110Imported : Bool
stableClosed110Imported =
  Closed110.criterionReceiptRecorded

stableRecovery110Imported : Bool
stableRecovery110Imported =
  Recovery110.receiptRecorded

stableCarrier111Imported : Bool
stableCarrier111Imported =
  Carrier111.sprint111AssemblyRecorded

stableEstimate114Imported : Bool
stableEstimate114Imported =
  Estimate114.assemblyRecorded

stableFeed115Imported : Bool
stableFeed115Imported =
  Feed115.feedThroughCriterionRecorded

stableReducer116Imported : Bool
stableReducer116Imported =
  Reducer116.reducerRecorded

reducer116CommonCarrierFeedThroughClosedInput : Bool
reducer116CommonCarrierFeedThroughClosedInput =
  Reducer116.commonCarrierFeedThroughClosedHere

reducer116ExternalCommonCarrierClosedInput : Bool
reducer116ExternalCommonCarrierClosedInput =
  Reducer116.externalCommonCarrierClosedHere

reducer116TransferLowerBoundReadyInput : Bool
reducer116TransferLowerBoundReadyInput =
  Reducer116.transferLowerBoundReadyHere

normFeedDependencyText : String
normFeedDependencyText =
  "Sprint117 norm feed dependency: the propagator may consume a norm closure only from the sibling path named here, and only when it proves the same Sprint112/Sprint114 upper-lower norm window required by the Sprint116 common-carrier reducer."

residualFeedDependencyText : String
residualFeedDependencyText =
  "Sprint117 residual feed dependency: the propagator may consume residual closure only from the sibling path named here, and only when quadrature, inverse/projection, E_a/P_a, and renormalized form residuals close in the Sprint114 convention."

sectorFeedDependencyText : String
sectorFeedDependencyText =
  "Sprint117 sector feed dependency: the propagator may consume sector closure only from the sibling path named here, and only when gauge quotient independence, physical projection compatibility, and vacuum/non-vacuum sector stability close together."

stableCommonCarrierInputText : String
stableCommonCarrierInputText =
  "Stable common-carrier inputs are exactly Sprint110 carrier/weak/closed-form/recovery receipts, Sprint111 common-carrier assembly, Sprint114 estimate closure assembly, Sprint115 feed-through criterion, and Sprint116 transfer closure reducer."

propagationRouteText : String
propagationRouteText =
  "Common-carrier feed-through propagation route: Sprint116 supplies the fail-closed reducer; Sprint117 norm, residual, and sector sibling feeds are path-referenced dependencies; transfer readiness remains false until all three feeds and the external common carrier close outside this module."

sourcePathBoundaryText : String
sourcePathBoundaryText =
  "Sprint117 sibling feeds are source-path references only; this module imports no Sprint117 sibling modules and therefore cannot close their claims here."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint117 propagates a route record only; commonCarrierFeedThroughClosedHere, externalCommonCarrierClosedHere, transferLowerBoundReadyHere, transferLowerBoundTheoremProvedHere, continuumMassGapProvedHere, and clayYangMillsPromoted remain false."

finalReceiptText : String
finalReceiptText =
  "Final Sprint117 receipt: the common-carrier feed-through propagation route is recorded with exact stable inputs and exact norm/residual/sector sibling path dependencies, while all theorem and promotion flags stay fail-closed."

data PropagationLane : Set where
  stable-common-carrier-input-lane :
    PropagationLane
  sprint116-reducer-input-lane :
    PropagationLane
  norm-feed-dependency-lane :
    PropagationLane
  residual-feed-dependency-lane :
    PropagationLane
  sector-feed-dependency-lane :
    PropagationLane
  external-common-carrier-dependency-lane :
    PropagationLane
  transfer-lower-bound-readiness-lane :
    PropagationLane
  theorem-boundary-lane :
    PropagationLane
  receipt-lane :
    PropagationLane

data PropagationStatus : Set where
  imported-stable-input :
    PropagationStatus
  imported-sprint116-reducer :
    PropagationStatus
  sibling-source-path-recorded :
    PropagationStatus
  feed-dependency-recorded :
    PropagationStatus
  route-recorded-fail-closed :
    PropagationStatus
  theorem-open :
    PropagationStatus
  final-receipt-recorded :
    PropagationStatus
  fail-closed-nonpromotion :
    PropagationStatus

data FeedDependencyKind : Set where
  norm-feed :
    FeedDependencyKind
  residual-feed :
    FeedDependencyKind
  sector-feed :
    FeedDependencyKind
  external-common-carrier-feed :
    FeedDependencyKind
  transfer-lower-bound-feed :
    FeedDependencyKind

canonicalPropagationLanes : List PropagationLane
canonicalPropagationLanes =
  stable-common-carrier-input-lane
  ∷ sprint116-reducer-input-lane
  ∷ norm-feed-dependency-lane
  ∷ residual-feed-dependency-lane
  ∷ sector-feed-dependency-lane
  ∷ external-common-carrier-dependency-lane
  ∷ transfer-lower-bound-readiness-lane
  ∷ theorem-boundary-lane
  ∷ receipt-lane
  ∷ []

record SourcePathRef : Set where
  constructor mkSourcePathRef
  field
    lane :
      PropagationLane
    moduleName :
      String
    sourcePath :
      String
    referenceOnly :
      Bool
    importedHere :
      Bool
    importedHereIsFalse :
      importedHere ≡ false
    status :
      PropagationStatus

record StableCommonCarrierInputs : Setω where
  constructor mkStableCommonCarrierInputs
  field
    statement :
      String
    carrier110Receipt :
      Carrier110.YMSprint110CommonCarrierHilbertIdentificationReceipt
    weak110Receipt :
      Weak110.YMSprint110WeakCompactnessEnergyCoreReceipt
    closed110Receipt :
      Closed110.YMSprint110ClosedFormLowerSemicontinuityCriterionReceipt
    recovery110Receipt :
      Recovery110.YMSprint110RecoveryCoreDensityEnergyLimsupReceipt
    carrier111Receipt :
      Carrier111.AssemblyReceipt
    estimate114Receipt :
      Estimate114.YMSprint114CommonCarrierEstimateClosureAssemblyReceipt
    feed115Receipt :
      Feed115.YMSprint115CommonCarrierFeedThroughCriterionReceipt
    reducer116Receipt :
      Reducer116.YMSprint116CommonCarrierTransferClosureReducerReceipt
    stableInputsRecorded :
      Bool
    carrier110Recorded :
      Bool
    weak110Recorded :
      Bool
    closed110Recorded :
      Bool
    recovery110Recorded :
      Bool
    carrier111Recorded :
      Bool
    estimate114Recorded :
      Bool
    feed115Recorded :
      Bool
    reducer116Recorded :
      Bool
    reducer116CommonCarrierFeedThroughClosed :
      Bool
    reducer116ExternalCommonCarrierClosed :
      Bool
    reducer116TransferLowerBoundReady :
      Bool
    reducer116CommonCarrierFeedThroughClosedIsFalse :
      reducer116CommonCarrierFeedThroughClosed ≡ false
    reducer116ExternalCommonCarrierClosedIsFalse :
      reducer116ExternalCommonCarrierClosed ≡ false
    reducer116TransferLowerBoundReadyIsFalse :
      reducer116TransferLowerBoundReady ≡ false
    status :
      PropagationStatus

record Sprint117SiblingFeedPathReferences : Set where
  constructor mkSprint117SiblingFeedPathReferences
  field
    normFeed :
      SourcePathRef
    residualFeed :
      SourcePathRef
    sectorFeed :
      SourcePathRef
    externalCommonCarrier :
      SourcePathRef
    transferLowerBound :
      SourcePathRef
    boundaryStatement :
      String
    usesStringReferencesOnly :
      Bool
    avoidsSprint117SiblingImports :
      Bool
    status :
      PropagationStatus

record FeedClosureDependency : Set where
  constructor mkFeedClosureDependency
  field
    kind :
      FeedDependencyKind
    lane :
      PropagationLane
    pathRef :
      SourcePathRef
    statement :
      String
    requiredBeforeFeedThrough :
      Bool
    requiredBeforeTransferReadiness :
      Bool
    dependencyRecorded :
      Bool
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false
    status :
      PropagationStatus

record FeedClosureDependencyLedger : Set where
  constructor mkFeedClosureDependencyLedger
  field
    normDependency :
      FeedClosureDependency
    residualDependency :
      FeedClosureDependency
    sectorDependency :
      FeedClosureDependency
    exactDependencies :
      List FeedClosureDependency
    dependenciesRecorded :
      Bool
    normFeedClosed :
      Bool
    residualFeedClosed :
      Bool
    sectorFeedClosed :
      Bool
    normFeedClosedIsFalse :
      normFeedClosed ≡ false
    residualFeedClosedIsFalse :
      residualFeedClosed ≡ false
    sectorFeedClosedIsFalse :
      sectorFeedClosed ≡ false
    status :
      PropagationStatus

record CommonCarrierFeedThroughPropagationRoute : Setω where
  constructor mkCommonCarrierFeedThroughPropagationRoute
  field
    routeStatement :
      String
    stableInputs :
      StableCommonCarrierInputs
    siblingPathReferences :
      Sprint117SiblingFeedPathReferences
    feedDependencies :
      FeedClosureDependencyLedger
    reducer116Route :
      Reducer116.FailClosedTransferRouteReducer
    routeRecorded :
      Bool
    sourcePathOnly :
      Bool
    normFeedClosed :
      Bool
    residualFeedClosed :
      Bool
    sectorFeedClosed :
      Bool
    commonCarrierFeedThroughClosed :
      Bool
    externalCommonCarrierClosed :
      Bool
    transferLowerBoundReady :
      Bool
    normFeedClosedIsFalse :
      normFeedClosed ≡ false
    residualFeedClosedIsFalse :
      residualFeedClosed ≡ false
    sectorFeedClosedIsFalse :
      sectorFeedClosed ≡ false
    commonCarrierFeedThroughClosedIsFalse :
      commonCarrierFeedThroughClosed ≡ false
    externalCommonCarrierClosedIsFalse :
      externalCommonCarrierClosed ≡ false
    transferLowerBoundReadyIsFalse :
      transferLowerBoundReady ≡ false
    status :
      PropagationStatus

record TheoremBoundary : Set where
  constructor mkTheoremBoundary
  field
    boundaryStatement :
      String
    commonCarrierFeedThroughClosedHereFlag :
      Bool
    commonCarrierFeedThroughClosedHereIsFalse :
      commonCarrierFeedThroughClosedHereFlag ≡ false
    externalCommonCarrierClosedHereFlag :
      Bool
    externalCommonCarrierClosedHereIsFalse :
      externalCommonCarrierClosedHereFlag ≡ false
    transferLowerBoundReadyHereFlag :
      Bool
    transferLowerBoundReadyHereIsFalse :
      transferLowerBoundReadyHereFlag ≡ false
    transferLowerBoundTheoremProvedHereFlag :
      Bool
    transferLowerBoundTheoremProvedHereIsFalse :
      transferLowerBoundTheoremProvedHereFlag ≡ false
    continuumMassGapProvedHereFlag :
      Bool
    continuumMassGapProvedHereIsFalse :
      continuumMassGapProvedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      PropagationStatus

record FinalReceipt : Set where
  constructor mkFinalReceipt
  field
    statement :
      String
    receiptRecorded :
      Bool
    routeRecorded :
      Bool
    dependenciesExact :
      Bool
    sourcePathsOnly :
      Bool
    commonCarrierFeedThroughClosed :
      Bool
    externalCommonCarrierClosed :
      Bool
    transferLowerBoundReady :
      Bool
    transferLowerBoundTheoremProved :
      Bool
    continuumMassGapProved :
      Bool
    clayYangMillsPromotedHere :
      Bool
    commonCarrierFeedThroughClosedIsFalse :
      commonCarrierFeedThroughClosed ≡ false
    externalCommonCarrierClosedIsFalse :
      externalCommonCarrierClosed ≡ false
    transferLowerBoundReadyIsFalse :
      transferLowerBoundReady ≡ false
    transferLowerBoundTheoremProvedIsFalse :
      transferLowerBoundTheoremProved ≡ false
    continuumMassGapProvedIsFalse :
      continuumMassGapProved ≡ false
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      PropagationStatus

record YMSprint117CommonCarrierFeedThroughPropagatorReceipt : Setω where
  constructor mkYMSprint117CommonCarrierFeedThroughPropagatorReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    stableInputs :
      StableCommonCarrierInputs
    siblingPathReferences :
      Sprint117SiblingFeedPathReferences
    feedDependencies :
      FeedClosureDependencyLedger
    propagationRoute :
      CommonCarrierFeedThroughPropagationRoute
    theoremBoundary :
      TheoremBoundary
    finalReceipt :
      FinalReceipt
    lanes :
      List PropagationLane
    evidenceLedger :
      List String
    receiptRecorded :
      Bool
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open YMSprint117CommonCarrierFeedThroughPropagatorReceipt public

canonicalNormFeedPathRef : SourcePathRef
canonicalNormFeedPathRef =
  mkSourcePathRef
    norm-feed-dependency-lane
    sprint117NormFeedModuleName
    sprint117NormFeedSourcePath
    true
    false
    refl
    sibling-source-path-recorded

canonicalResidualFeedPathRef : SourcePathRef
canonicalResidualFeedPathRef =
  mkSourcePathRef
    residual-feed-dependency-lane
    sprint117ResidualFeedModuleName
    sprint117ResidualFeedSourcePath
    true
    false
    refl
    sibling-source-path-recorded

canonicalSectorFeedPathRef : SourcePathRef
canonicalSectorFeedPathRef =
  mkSourcePathRef
    sector-feed-dependency-lane
    sprint117SectorFeedModuleName
    sprint117SectorFeedSourcePath
    true
    false
    refl
    sibling-source-path-recorded

canonicalExternalCommonCarrierPathRef : SourcePathRef
canonicalExternalCommonCarrierPathRef =
  mkSourcePathRef
    external-common-carrier-dependency-lane
    sprint117ExternalCommonCarrierModuleName
    sprint117ExternalCommonCarrierSourcePath
    true
    false
    refl
    sibling-source-path-recorded

canonicalTransferLowerBoundPathRef : SourcePathRef
canonicalTransferLowerBoundPathRef =
  mkSourcePathRef
    transfer-lower-bound-readiness-lane
    sprint117TransferLowerBoundModuleName
    sprint117TransferLowerBoundSourcePath
    true
    false
    refl
    sibling-source-path-recorded

canonicalStableCommonCarrierInputs : StableCommonCarrierInputs
canonicalStableCommonCarrierInputs =
  mkStableCommonCarrierInputs
    stableCommonCarrierInputText
    Carrier110.canonicalReceipt
    Weak110.canonicalReceipt
    Closed110.canonicalReceipt
    Recovery110.canonicalReceipt
    Carrier111.canonicalAssemblyReceipt
    Estimate114.canonicalReceipt
    Feed115.canonicalReceipt
    Reducer116.canonicalReceipt
    stableCommonCarrierInputsRecorded
    stableCarrier110Imported
    stableWeak110Imported
    stableClosed110Imported
    stableRecovery110Imported
    stableCarrier111Imported
    stableEstimate114Imported
    stableFeed115Imported
    stableReducer116Imported
    reducer116CommonCarrierFeedThroughClosedInput
    reducer116ExternalCommonCarrierClosedInput
    reducer116TransferLowerBoundReadyInput
    refl
    refl
    refl
    imported-stable-input

canonicalSprint117SiblingFeedPathReferences :
  Sprint117SiblingFeedPathReferences
canonicalSprint117SiblingFeedPathReferences =
  mkSprint117SiblingFeedPathReferences
    canonicalNormFeedPathRef
    canonicalResidualFeedPathRef
    canonicalSectorFeedPathRef
    canonicalExternalCommonCarrierPathRef
    canonicalTransferLowerBoundPathRef
    sourcePathBoundaryText
    true
    true
    sibling-source-path-recorded

canonicalNormFeedDependency : FeedClosureDependency
canonicalNormFeedDependency =
  mkFeedClosureDependency
    norm-feed
    norm-feed-dependency-lane
    canonicalNormFeedPathRef
    normFeedDependencyText
    true
    true
    normFeedDependencyRecorded
    normFeedClosedHere
    refl
    feed-dependency-recorded

canonicalResidualFeedDependency : FeedClosureDependency
canonicalResidualFeedDependency =
  mkFeedClosureDependency
    residual-feed
    residual-feed-dependency-lane
    canonicalResidualFeedPathRef
    residualFeedDependencyText
    true
    true
    residualFeedDependencyRecorded
    residualFeedClosedHere
    refl
    feed-dependency-recorded

canonicalSectorFeedDependency : FeedClosureDependency
canonicalSectorFeedDependency =
  mkFeedClosureDependency
    sector-feed
    sector-feed-dependency-lane
    canonicalSectorFeedPathRef
    sectorFeedDependencyText
    true
    true
    sectorFeedDependencyRecorded
    sectorFeedClosedHere
    refl
    feed-dependency-recorded

canonicalFeedClosureDependencyLedger : FeedClosureDependencyLedger
canonicalFeedClosureDependencyLedger =
  mkFeedClosureDependencyLedger
    canonicalNormFeedDependency
    canonicalResidualFeedDependency
    canonicalSectorFeedDependency
    (canonicalNormFeedDependency
     ∷ canonicalResidualFeedDependency
     ∷ canonicalSectorFeedDependency
     ∷ [])
    true
    normFeedClosedHere
    residualFeedClosedHere
    sectorFeedClosedHere
    refl
    refl
    refl
    feed-dependency-recorded

canonicalCommonCarrierFeedThroughPropagationRoute :
  CommonCarrierFeedThroughPropagationRoute
canonicalCommonCarrierFeedThroughPropagationRoute =
  mkCommonCarrierFeedThroughPropagationRoute
    propagationRouteText
    canonicalStableCommonCarrierInputs
    canonicalSprint117SiblingFeedPathReferences
    canonicalFeedClosureDependencyLedger
    Reducer116.canonicalFailClosedTransferRouteReducer
    feedThroughPropagationRouteRecorded
    sourcePathReferenceOnlyRecorded
    normFeedClosedHere
    residualFeedClosedHere
    sectorFeedClosedHere
    commonCarrierFeedThroughClosedHere
    externalCommonCarrierClosedHere
    transferLowerBoundReadyHere
    refl
    refl
    refl
    refl
    refl
    refl
    route-recorded-fail-closed

canonicalTheoremBoundary : TheoremBoundary
canonicalTheoremBoundary =
  mkTheoremBoundary
    nonPromotionBoundaryText
    commonCarrierFeedThroughClosedHere
    refl
    externalCommonCarrierClosedHere
    refl
    transferLowerBoundReadyHere
    refl
    transferLowerBoundTheoremProvedHere
    refl
    continuumMassGapProvedHere
    refl
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion

canonicalFinalReceipt : FinalReceipt
canonicalFinalReceipt =
  mkFinalReceipt
    finalReceiptText
    propagatorRecorded
    feedThroughPropagationRouteRecorded
    true
    sourcePathReferenceOnlyRecorded
    commonCarrierFeedThroughClosedHere
    externalCommonCarrierClosedHere
    transferLowerBoundReadyHere
    transferLowerBoundTheoremProvedHere
    continuumMassGapProvedHere
    clayYangMillsPromoted
    refl
    refl
    refl
    refl
    refl
    refl
    final-receipt-recorded

canonicalEvidenceLedger : List String
canonicalEvidenceLedger =
  modulePath
  ∷ sprint116ReducerSourcePath
  ∷ sprint115FeedThroughSourcePath
  ∷ sprint114EstimateSourcePath
  ∷ sprint111CarrierSourcePath
  ∷ sprint110CarrierSourcePath
  ∷ sprint110WeakSourcePath
  ∷ sprint110ClosedFormSourcePath
  ∷ sprint110RecoverySourcePath
  ∷ sprint117NormFeedSourcePath
  ∷ sprint117ResidualFeedSourcePath
  ∷ sprint117SectorFeedSourcePath
  ∷ sprint117ExternalCommonCarrierSourcePath
  ∷ sprint117TransferLowerBoundSourcePath
  ∷ stableCommonCarrierInputText
  ∷ normFeedDependencyText
  ∷ residualFeedDependencyText
  ∷ sectorFeedDependencyText
  ∷ propagationRouteText
  ∷ sourcePathBoundaryText
  ∷ nonPromotionBoundaryText
  ∷ finalReceiptText
  ∷ []

canonicalYMSprint117CommonCarrierFeedThroughPropagatorReceipt :
  YMSprint117CommonCarrierFeedThroughPropagatorReceipt
canonicalYMSprint117CommonCarrierFeedThroughPropagatorReceipt =
  mkYMSprint117CommonCarrierFeedThroughPropagatorReceipt
    sprintNumber
    modulePath
    canonicalStableCommonCarrierInputs
    canonicalSprint117SiblingFeedPathReferences
    canonicalFeedClosureDependencyLedger
    canonicalCommonCarrierFeedThroughPropagationRoute
    canonicalTheoremBoundary
    canonicalFinalReceipt
    canonicalPropagationLanes
    canonicalEvidenceLedger
    propagatorRecorded
    clayYangMillsPromoted
    refl

canonicalReceipt :
  YMSprint117CommonCarrierFeedThroughPropagatorReceipt
canonicalReceipt =
  canonicalYMSprint117CommonCarrierFeedThroughPropagatorReceipt

canonicalCommonCarrierFeedThroughClosedHereIsFalse :
  commonCarrierFeedThroughClosedHere ≡ false
canonicalCommonCarrierFeedThroughClosedHereIsFalse =
  refl

canonicalExternalCommonCarrierClosedHereIsFalse :
  externalCommonCarrierClosedHere ≡ false
canonicalExternalCommonCarrierClosedHereIsFalse =
  refl

canonicalTransferLowerBoundReadyHereIsFalse :
  transferLowerBoundReadyHere ≡ false
canonicalTransferLowerBoundReadyHereIsFalse =
  refl

canonicalTransferLowerBoundTheoremProvedHereIsFalse :
  transferLowerBoundTheoremProvedHere ≡ false
canonicalTransferLowerBoundTheoremProvedHereIsFalse =
  refl

canonicalContinuumMassGapProvedHereIsFalse :
  continuumMassGapProvedHere ≡ false
canonicalContinuumMassGapProvedHereIsFalse =
  refl

canonicalClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalClayYangMillsPromotedIsFalse =
  refl

canonicalNormFeedClosedHereIsFalse :
  normFeedClosedHere ≡ false
canonicalNormFeedClosedHereIsFalse =
  refl

canonicalResidualFeedClosedHereIsFalse :
  residualFeedClosedHere ≡ false
canonicalResidualFeedClosedHereIsFalse =
  refl

canonicalSectorFeedClosedHereIsFalse :
  sectorFeedClosedHere ≡ false
canonicalSectorFeedClosedHereIsFalse =
  refl

canonicalUsesStringReferencesOnly :
  Sprint117SiblingFeedPathReferences.usesStringReferencesOnly
    (siblingPathReferences canonicalReceipt) ≡ true
canonicalUsesStringReferencesOnly =
  refl

canonicalAvoidsSprint117SiblingImports :
  Sprint117SiblingFeedPathReferences.avoidsSprint117SiblingImports
    (siblingPathReferences canonicalReceipt) ≡ true
canonicalAvoidsSprint117SiblingImports =
  refl

canonicalConsumesReducer116FeedThroughClosedFalse :
  reducer116CommonCarrierFeedThroughClosedInput ≡ false
canonicalConsumesReducer116FeedThroughClosedFalse =
  refl

canonicalConsumesReducer116ExternalCommonCarrierClosedFalse :
  reducer116ExternalCommonCarrierClosedInput ≡ false
canonicalConsumesReducer116ExternalCommonCarrierClosedFalse =
  refl

canonicalConsumesReducer116TransferReadyFalse :
  reducer116TransferLowerBoundReadyInput ≡ false
canonicalConsumesReducer116TransferReadyFalse =
  refl
