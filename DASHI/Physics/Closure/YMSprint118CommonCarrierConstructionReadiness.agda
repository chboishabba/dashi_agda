module DASHI.Physics.Closure.YMSprint118CommonCarrierConstructionReadiness where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint111CommonCarrierConstructionAssembly
  as Carrier111
import DASHI.Physics.Closure.YMSprint114CommonCarrierEstimateClosureAssembly
  as Estimate114
import DASHI.Physics.Closure.YMSprint116CommonCarrierTransferClosureReducer
  as Reducer116
import DASHI.Physics.Closure.YMSprint117CommonCarrierFeedThroughPropagator
  as Propagator117

------------------------------------------------------------------------
-- Sprint118 common-carrier construction readiness.
--
-- This module reduces the external common-carrier construction closure to the
-- exact construction-readiness inputs that have to be supplied before the
-- downstream transfer lower-bound route can be reopened.  It imports the
-- stable Sprint111, Sprint114, Sprint116, and Sprint117 receipts and assembles
-- concrete obligation rows for E_a/P_a maps, quotient compatibility, norm
-- window, adjointness/approximate inverse, projection stability,
-- weak/recovery feed-through, and common-carrier estimate closure.
--
-- The package is inhabited and records readiness assembly here, but remains
-- fail-closed: it proves no external common-carrier construction closure, no
-- common-carrier construction theorem, no feed-through closure, no transfer
-- lower-bound readiness, and no Clay Yang-Mills promotion.

sprintNumber : Nat
sprintNumber = 118

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint118CommonCarrierConstructionReadiness.agda"

sprint111CarrierSourcePath : String
sprint111CarrierSourcePath =
  "DASHI/Physics/Closure/YMSprint111CommonCarrierConstructionAssembly.agda"

sprint114EstimateSourcePath : String
sprint114EstimateSourcePath =
  "DASHI/Physics/Closure/YMSprint114CommonCarrierEstimateClosureAssembly.agda"

sprint116ReducerSourcePath : String
sprint116ReducerSourcePath =
  "DASHI/Physics/Closure/YMSprint116CommonCarrierTransferClosureReducer.agda"

sprint117PropagatorSourcePath : String
sprint117PropagatorSourcePath =
  "DASHI/Physics/Closure/YMSprint117CommonCarrierFeedThroughPropagator.agda"

constructionReadinessPackageAssembledHere : Bool
constructionReadinessPackageAssembledHere = true

constructionReadinessInputsRecorded : Bool
constructionReadinessInputsRecorded = true

sourcePathLedgerRecorded : Bool
sourcePathLedgerRecorded = true

eAPaMapReadinessRecorded : Bool
eAPaMapReadinessRecorded = true

quotientCompatibilityReadinessRecorded : Bool
quotientCompatibilityReadinessRecorded = true

normWindowReadinessRecorded : Bool
normWindowReadinessRecorded = true

adjointnessApproxInverseReadinessRecorded : Bool
adjointnessApproxInverseReadinessRecorded = true

projectionStabilityReadinessRecorded : Bool
projectionStabilityReadinessRecorded = true

weakRecoveryFeedThroughReadinessRecorded : Bool
weakRecoveryFeedThroughReadinessRecorded = true

commonCarrierEstimateClosureReadinessRecorded : Bool
commonCarrierEstimateClosureReadinessRecorded = true

canonicalReceiptRecorded : Bool
canonicalReceiptRecorded = true

finalReceiptRecorded : Bool
finalReceiptRecorded = true

externalCommonCarrierConstructionClosedHere : Bool
externalCommonCarrierConstructionClosedHere = false

commonCarrierConstructionTheoremProvedHere : Bool
commonCarrierConstructionTheoremProvedHere = false

commonCarrierFeedThroughClosedHere : Bool
commonCarrierFeedThroughClosedHere = false

transferLowerBoundReadyHere : Bool
transferLowerBoundReadyHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

carrier111Imported : Bool
carrier111Imported =
  Carrier111.sprint111AssemblyRecorded

estimate114Imported : Bool
estimate114Imported =
  Estimate114.assemblyRecorded

reducer116Imported : Bool
reducer116Imported =
  Reducer116.reducerRecorded

propagator117Imported : Bool
propagator117Imported =
  Propagator117.propagatorRecorded

carrier111ClosedInput : Bool
carrier111ClosedInput =
  Carrier111.commonCarrierConstructionClosedHere

estimate114ClosedInput : Bool
estimate114ClosedInput =
  Estimate114.commonCarrierEstimateClosureClosedHere

reducer116ExternalCommonCarrierClosedInput : Bool
reducer116ExternalCommonCarrierClosedInput =
  Reducer116.externalCommonCarrierClosedHere

reducer116TransferReadyInput : Bool
reducer116TransferReadyInput =
  Reducer116.transferLowerBoundReadyHere

propagator117FeedThroughClosedInput : Bool
propagator117FeedThroughClosedInput =
  Propagator117.commonCarrierFeedThroughClosedHere

propagator117ExternalCommonCarrierClosedInput : Bool
propagator117ExternalCommonCarrierClosedInput =
  Propagator117.externalCommonCarrierClosedHere

readinessRouteText : String
readinessRouteText =
  "Sprint118 readiness route: external common-carrier construction can be closed only after exact E_a/P_a maps, quotient compatibility, norm window, adjointness or approximate inverse, projection stability, weak/recovery feed-through, and common-carrier estimate closure are supplied on the same carrier convention."

eAPaMapReadinessText : String
eAPaMapReadinessText =
  "E_a/P_a map readiness: provide concrete embedding E_a and projection P_a maps between finite physical quotient carriers and the continuum physical carrier, with the Sprint111 renormalized convention and named source evidence."

quotientCompatibilityReadinessText : String
quotientCompatibilityReadinessText =
  "Quotient compatibility readiness: prove finite representative independence, continuum physical projection descent, gauge covariance, and sector separation compatibility for the same E_a/P_a maps."

normWindowReadinessText : String
normWindowReadinessText =
  "Norm window readiness: provide cutoff-uniform upper and lower norm comparisons over the admissible a-window, consuming the Sprint114 constant ledger without changing carrier normalization."

adjointnessApproxInverseReadinessText : String
adjointnessApproxInverseReadinessText =
  "Adjointness/approximate inverse readiness: prove the E_a/P_a adjointness residual or left/right approximate inverse residuals vanish in the quotient Hilbert norms required by Sprint114 and Sprint116."

projectionStabilityReadinessText : String
projectionStabilityReadinessText =
  "Projection stability readiness: prove physical projection commutators, vacuum/non-vacuum sector stability, and quotient descent remain stable under the same E_a/P_a construction."

weakRecoveryFeedThroughReadinessText : String
weakRecoveryFeedThroughReadinessText =
  "Weak/recovery feed-through readiness: feed the constructed common carrier into Sprint110 weak compactness, closed-form lower semicontinuity, recovery strong convergence, and recovery energy limsup with no carrier relabelling."

estimateClosureReadinessText : String
estimateClosureReadinessText =
  "Common carrier estimate closure readiness: consume the Sprint114 gauge quotient, uniform constant, quadrature residual, inverse/projection, and weak/recovery criteria as one exact estimate-closure input."

nonClosureBoundaryText : String
nonClosureBoundaryText =
  "Sprint118 assembles readiness inputs only; externalCommonCarrierConstructionClosedHere, commonCarrierConstructionTheoremProvedHere, commonCarrierFeedThroughClosedHere, transferLowerBoundReadyHere, and clayYangMillsPromoted remain false."

canonicalReceiptText : String
canonicalReceiptText =
  "Canonical Sprint118 receipt: construction-readiness obligations are exact, source paths are recorded, upstream receipts are consumed, and all theorem/promotion flags remain fail-closed."

finalReceiptText : String
finalReceiptText =
  "Final Sprint118 receipt: the readiness package is assembled here for external common-carrier construction, but no external closure, construction theorem, feed-through closure, transfer readiness, or Clay promotion is claimed."

data ReadinessLane : Set where
  stable-input-lane :
    ReadinessLane
  source-path-lane :
    ReadinessLane
  e-a-p-a-map-lane :
    ReadinessLane
  quotient-compatibility-lane :
    ReadinessLane
  norm-window-lane :
    ReadinessLane
  adjointness-approx-inverse-lane :
    ReadinessLane
  projection-stability-lane :
    ReadinessLane
  weak-recovery-feed-through-lane :
    ReadinessLane
  estimate-closure-lane :
    ReadinessLane
  external-construction-boundary-lane :
    ReadinessLane
  receipt-lane :
    ReadinessLane

data ReadinessStatus : Set where
  imported-stable-input :
    ReadinessStatus
  source-path-recorded :
    ReadinessStatus
  obligation-recorded :
    ReadinessStatus
  exact-input-required :
    ReadinessStatus
  estimate-closure-input-required :
    ReadinessStatus
  feed-through-input-required :
    ReadinessStatus
  construction-boundary-fail-closed :
    ReadinessStatus
  canonical-receipt-recorded :
    ReadinessStatus
  final-receipt-recorded :
    ReadinessStatus
  fail-closed-nonpromotion :
    ReadinessStatus

data ReadinessKind : Set where
  e-a-p-a-maps :
    ReadinessKind
  quotient-compatibility :
    ReadinessKind
  norm-window :
    ReadinessKind
  adjointness-approx-inverse :
    ReadinessKind
  projection-stability :
    ReadinessKind
  weak-recovery-feed-through :
    ReadinessKind
  common-carrier-estimate-closure :
    ReadinessKind

canonicalReadinessLanes : List ReadinessLane
canonicalReadinessLanes =
  stable-input-lane
  ∷ source-path-lane
  ∷ e-a-p-a-map-lane
  ∷ quotient-compatibility-lane
  ∷ norm-window-lane
  ∷ adjointness-approx-inverse-lane
  ∷ projection-stability-lane
  ∷ weak-recovery-feed-through-lane
  ∷ estimate-closure-lane
  ∷ external-construction-boundary-lane
  ∷ receipt-lane
  ∷ []

record StableReadinessInputs : Setω where
  constructor mkStableReadinessInputs
  field
    carrier111Receipt :
      Carrier111.AssemblyReceipt
    estimate114Receipt :
      Estimate114.YMSprint114CommonCarrierEstimateClosureAssemblyReceipt
    reducer116Receipt :
      Reducer116.YMSprint116CommonCarrierTransferClosureReducerReceipt
    propagator117Receipt :
      Propagator117.YMSprint117CommonCarrierFeedThroughPropagatorReceipt
    carrier111Recorded :
      Bool
    estimate114Recorded :
      Bool
    reducer116Recorded :
      Bool
    propagator117Recorded :
      Bool
    carrier111Closed :
      Bool
    estimate114Closed :
      Bool
    reducer116ExternalCommonCarrierClosed :
      Bool
    reducer116TransferReady :
      Bool
    propagator117FeedThroughClosed :
      Bool
    propagator117ExternalCommonCarrierClosed :
      Bool
    carrier111ClosedIsFalse :
      carrier111Closed ≡ false
    estimate114ClosedIsFalse :
      estimate114Closed ≡ false
    reducer116ExternalCommonCarrierClosedIsFalse :
      reducer116ExternalCommonCarrierClosed ≡ false
    reducer116TransferReadyIsFalse :
      reducer116TransferReady ≡ false
    propagator117FeedThroughClosedIsFalse :
      propagator117FeedThroughClosed ≡ false
    propagator117ExternalCommonCarrierClosedIsFalse :
      propagator117ExternalCommonCarrierClosed ≡ false
    status :
      ReadinessStatus

record SourcePathLedger : Set where
  constructor mkSourcePathLedger
  field
    carrier111Path :
      String
    estimate114Path :
      String
    reducer116Path :
      String
    propagator117Path :
      String
    localPath :
      String
    pathsConcrete :
      Bool
    status :
      ReadinessStatus

record ConstructionObligationRow : Set where
  constructor mkConstructionObligationRow
  field
    kind :
      ReadinessKind
    lane :
      ReadinessLane
    sourcePath :
      String
    statement :
      String
    requiredForExternalConstruction :
      Bool
    requiredForFeedThrough :
      Bool
    requiredForTransferReadiness :
      Bool
    recordedHere :
      Bool
    suppliedHere :
      Bool
    suppliedHereIsFalse :
      suppliedHere ≡ false
    status :
      ReadinessStatus

record EAPaMapReadiness : Set where
  constructor mkEAPaMapReadiness
  field
    row :
      ConstructionObligationRow
    finiteToContinuumEmbeddingNamed :
      Bool
    continuumToFiniteProjectionNamed :
      Bool
    sharedPhysicalCarrierRequired :
      Bool
    renormalizedConventionRequired :
      Bool
    quotientDescentRequired :
      Bool
    mapConstructionClosedHere :
      Bool
    mapConstructionClosedHereIsFalse :
      mapConstructionClosedHere ≡ false

record QuotientCompatibilityReadiness : Set where
  constructor mkQuotientCompatibilityReadiness
  field
    row :
      ConstructionObligationRow
    finiteRepresentativeIndependenceRequired :
      Bool
    continuumProjectionCompatibilityRequired :
      Bool
    gaugeCovarianceRequired :
      Bool
    sectorSeparationRequired :
      Bool
    quotientCompatibilityClosedHere :
      Bool
    quotientCompatibilityClosedHereIsFalse :
      quotientCompatibilityClosedHere ≡ false

record NormWindowReadiness : Set where
  constructor mkNormWindowReadiness
  field
    row :
      ConstructionObligationRow
    cutoffUniformUpperBoundRequired :
      Bool
    cutoffUniformLowerBoundRequired :
      Bool
    admissibleAWindowRequired :
      Bool
    sprint114PackageConstant :
      Nat
    consumesSprint114ConstantLedger :
      Bool
    normWindowClosedHere :
      Bool
    normWindowClosedHereIsFalse :
      normWindowClosedHere ≡ false

record AdjointnessApproxInverseReadiness : Set where
  constructor mkAdjointnessApproxInverseReadiness
  field
    row :
      ConstructionObligationRow
    adjointnessResidualRequired :
      Bool
    leftApproxInverseRequired :
      Bool
    rightApproxInverseRequired :
      Bool
    quotientHilbertNormRequired :
      Bool
    residualVanishingRequired :
      Bool
    adjointnessApproxInverseClosedHere :
      Bool
    adjointnessApproxInverseClosedHereIsFalse :
      adjointnessApproxInverseClosedHere ≡ false

record ProjectionStabilityReadiness : Set where
  constructor mkProjectionStabilityReadiness
  field
    row :
      ConstructionObligationRow
    physicalProjectionCommutatorRequired :
      Bool
    quotientProjectionStabilityRequired :
      Bool
    vacuumSectorStabilityRequired :
      Bool
    nonVacuumSectorStabilityRequired :
      Bool
    stabilityClosedHere :
      Bool
    stabilityClosedHereIsFalse :
      stabilityClosedHere ≡ false

record WeakRecoveryFeedThroughReadiness : Setω where
  constructor mkWeakRecoveryFeedThroughReadiness
  field
    row :
      ConstructionObligationRow
    reducer116WeakFeed :
      Reducer116.WeakCompactnessFeed
    reducer116RecoveryFeed :
      Reducer116.RecoveryLimsupFeed
    propagator117Route :
      Propagator117.CommonCarrierFeedThroughPropagationRoute
    weakCompactnessRequired :
      Bool
    lowerSemicontinuityRequired :
      Bool
    recoveryStrongConvergenceRequired :
      Bool
    recoveryEnergyLimsupRequired :
      Bool
    sameCarrierRequired :
      Bool
    feedThroughClosedHere :
      Bool
    feedThroughClosedHereIsFalse :
      feedThroughClosedHere ≡ false

record EstimateClosureReadiness : Setω where
  constructor mkEstimateClosureReadiness
  field
    row :
      ConstructionObligationRow
    estimate114GaugeQuotient :
      Estimate114.GaugeQuotientClosureCriterion
    estimate114NormConstants :
      Estimate114.UniformNormConstantAssembly
    estimate114QuadratureResidual :
      Estimate114.QuadratureResidualClosure
    estimate114InverseProjection :
      Estimate114.InverseProjectionClosure
    estimate114WeakRecovery :
      Estimate114.WeakRecoveryFeedThroughRequirements
    estimateClosureRequired :
      Bool
    estimateClosureClosedHere :
      Bool
    estimateClosureClosedHereIsFalse :
      estimateClosureClosedHere ≡ false

record ConstructionReadinessObligations : Setω where
  constructor mkConstructionReadinessObligations
  field
    eAPaMaps :
      EAPaMapReadiness
    quotientCompatibility :
      QuotientCompatibilityReadiness
    normWindow :
      NormWindowReadiness
    adjointnessApproxInverse :
      AdjointnessApproxInverseReadiness
    projectionStability :
      ProjectionStabilityReadiness
    weakRecoveryFeedThrough :
      WeakRecoveryFeedThroughReadiness
    estimateClosure :
      EstimateClosureReadiness
    obligationRows :
      List ConstructionObligationRow
    allRowsRecorded :
      Bool
    externalConstructionClosed :
      Bool
    feedThroughClosed :
      Bool
    transferReady :
      Bool
    externalConstructionClosedIsFalse :
      externalConstructionClosed ≡ false
    feedThroughClosedIsFalse :
      feedThroughClosed ≡ false
    transferReadyIsFalse :
      transferReady ≡ false
    status :
      ReadinessStatus

record ConstructionBoundary : Set where
  constructor mkConstructionBoundary
  field
    boundaryStatement :
      String
    packageAssembledHere :
      Bool
    externalCommonCarrierConstructionClosed :
      Bool
    commonCarrierConstructionTheoremProved :
      Bool
    commonCarrierFeedThroughClosed :
      Bool
    transferLowerBoundReady :
      Bool
    clayPromoted :
      Bool
    externalCommonCarrierConstructionClosedIsFalse :
      externalCommonCarrierConstructionClosed ≡ false
    commonCarrierConstructionTheoremProvedIsFalse :
      commonCarrierConstructionTheoremProved ≡ false
    commonCarrierFeedThroughClosedIsFalse :
      commonCarrierFeedThroughClosed ≡ false
    transferLowerBoundReadyIsFalse :
      transferLowerBoundReady ≡ false
    clayPromotedIsFalse :
      clayPromoted ≡ false
    status :
      ReadinessStatus

record ReadinessReceipt : Setω where
  constructor mkReadinessReceipt
  field
    statement :
      String
    stableInputs :
      StableReadinessInputs
    sourcePaths :
      SourcePathLedger
    obligations :
      ConstructionReadinessObligations
    constructionBoundary :
      ConstructionBoundary
    lanes :
      List ReadinessLane
    evidenceLedger :
      List String
    receiptRecorded :
      Bool
    canonicalReceiptRecordedHere :
      Bool
    externalCommonCarrierConstructionClosed :
      Bool
    commonCarrierConstructionTheoremProved :
      Bool
    commonCarrierFeedThroughClosed :
      Bool
    transferLowerBoundReady :
      Bool
    clayPromoted :
      Bool
    externalCommonCarrierConstructionClosedIsFalse :
      externalCommonCarrierConstructionClosed ≡ false
    commonCarrierConstructionTheoremProvedIsFalse :
      commonCarrierConstructionTheoremProved ≡ false
    commonCarrierFeedThroughClosedIsFalse :
      commonCarrierFeedThroughClosed ≡ false
    transferLowerBoundReadyIsFalse :
      transferLowerBoundReady ≡ false
    clayPromotedIsFalse :
      clayPromoted ≡ false

record FinalReceipt : Setω where
  constructor mkFinalReceipt
  field
    statement :
      String
    canonicalReceipt :
      ReadinessReceipt
    finalReceiptRecordedHere :
      Bool
    readinessPackageAssembledHere :
      Bool
    exactInputsReduced :
      Bool
    sourcePathsRecorded :
      Bool
    externalCommonCarrierConstructionClosed :
      Bool
    commonCarrierConstructionTheoremProved :
      Bool
    commonCarrierFeedThroughClosed :
      Bool
    transferLowerBoundReady :
      Bool
    clayPromoted :
      Bool
    externalCommonCarrierConstructionClosedIsFalse :
      externalCommonCarrierConstructionClosed ≡ false
    commonCarrierConstructionTheoremProvedIsFalse :
      commonCarrierConstructionTheoremProved ≡ false
    commonCarrierFeedThroughClosedIsFalse :
      commonCarrierFeedThroughClosed ≡ false
    transferLowerBoundReadyIsFalse :
      transferLowerBoundReady ≡ false
    clayPromotedIsFalse :
      clayPromoted ≡ false
    status :
      ReadinessStatus

record YMSprint118CommonCarrierConstructionReadinessReceipt : Setω where
  constructor mkYMSprint118CommonCarrierConstructionReadinessReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    readinessReceipt :
      ReadinessReceipt
    finalReadinessReceipt :
      FinalReceipt
    receiptRecorded :
      Bool
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open YMSprint118CommonCarrierConstructionReadinessReceipt public

canonicalStableReadinessInputs : StableReadinessInputs
canonicalStableReadinessInputs =
  mkStableReadinessInputs
    Carrier111.canonicalAssemblyReceipt
    Estimate114.canonicalReceipt
    Reducer116.canonicalReceipt
    Propagator117.canonicalReceipt
    carrier111Imported
    estimate114Imported
    reducer116Imported
    propagator117Imported
    carrier111ClosedInput
    estimate114ClosedInput
    reducer116ExternalCommonCarrierClosedInput
    reducer116TransferReadyInput
    propagator117FeedThroughClosedInput
    propagator117ExternalCommonCarrierClosedInput
    refl
    refl
    refl
    refl
    refl
    refl
    imported-stable-input

canonicalSourcePathLedger : SourcePathLedger
canonicalSourcePathLedger =
  mkSourcePathLedger
    sprint111CarrierSourcePath
    sprint114EstimateSourcePath
    sprint116ReducerSourcePath
    sprint117PropagatorSourcePath
    modulePath
    sourcePathLedgerRecorded
    source-path-recorded

canonicalEAPaMapObligationRow : ConstructionObligationRow
canonicalEAPaMapObligationRow =
  mkConstructionObligationRow
    e-a-p-a-maps
    e-a-p-a-map-lane
    sprint111CarrierSourcePath
    eAPaMapReadinessText
    true
    true
    true
    eAPaMapReadinessRecorded
    externalCommonCarrierConstructionClosedHere
    refl
    exact-input-required

canonicalQuotientCompatibilityObligationRow :
  ConstructionObligationRow
canonicalQuotientCompatibilityObligationRow =
  mkConstructionObligationRow
    quotient-compatibility
    quotient-compatibility-lane
    sprint114EstimateSourcePath
    quotientCompatibilityReadinessText
    true
    true
    true
    quotientCompatibilityReadinessRecorded
    externalCommonCarrierConstructionClosedHere
    refl
    exact-input-required

canonicalNormWindowObligationRow : ConstructionObligationRow
canonicalNormWindowObligationRow =
  mkConstructionObligationRow
    norm-window
    norm-window-lane
    sprint114EstimateSourcePath
    normWindowReadinessText
    true
    true
    true
    normWindowReadinessRecorded
    transferLowerBoundReadyHere
    refl
    exact-input-required

canonicalAdjointnessApproxInverseObligationRow :
  ConstructionObligationRow
canonicalAdjointnessApproxInverseObligationRow =
  mkConstructionObligationRow
    adjointness-approx-inverse
    adjointness-approx-inverse-lane
    sprint114EstimateSourcePath
    adjointnessApproxInverseReadinessText
    true
    true
    true
    adjointnessApproxInverseReadinessRecorded
    externalCommonCarrierConstructionClosedHere
    refl
    exact-input-required

canonicalProjectionStabilityObligationRow : ConstructionObligationRow
canonicalProjectionStabilityObligationRow =
  mkConstructionObligationRow
    projection-stability
    projection-stability-lane
    sprint116ReducerSourcePath
    projectionStabilityReadinessText
    true
    true
    true
    projectionStabilityReadinessRecorded
    externalCommonCarrierConstructionClosedHere
    refl
    exact-input-required

canonicalWeakRecoveryFeedThroughObligationRow :
  ConstructionObligationRow
canonicalWeakRecoveryFeedThroughObligationRow =
  mkConstructionObligationRow
    weak-recovery-feed-through
    weak-recovery-feed-through-lane
    sprint117PropagatorSourcePath
    weakRecoveryFeedThroughReadinessText
    true
    true
    true
    weakRecoveryFeedThroughReadinessRecorded
    commonCarrierFeedThroughClosedHere
    refl
    feed-through-input-required

canonicalEstimateClosureObligationRow : ConstructionObligationRow
canonicalEstimateClosureObligationRow =
  mkConstructionObligationRow
    common-carrier-estimate-closure
    estimate-closure-lane
    sprint114EstimateSourcePath
    estimateClosureReadinessText
    true
    true
    true
    commonCarrierEstimateClosureReadinessRecorded
    estimate114ClosedInput
    refl
    estimate-closure-input-required

canonicalEAPaMapReadiness : EAPaMapReadiness
canonicalEAPaMapReadiness =
  mkEAPaMapReadiness
    canonicalEAPaMapObligationRow
    true
    true
    true
    true
    true
    externalCommonCarrierConstructionClosedHere
    refl

canonicalQuotientCompatibilityReadiness :
  QuotientCompatibilityReadiness
canonicalQuotientCompatibilityReadiness =
  mkQuotientCompatibilityReadiness
    canonicalQuotientCompatibilityObligationRow
    true
    true
    true
    true
    externalCommonCarrierConstructionClosedHere
    refl

canonicalNormWindowReadiness : NormWindowReadiness
canonicalNormWindowReadiness =
  mkNormWindowReadiness
    canonicalNormWindowObligationRow
    true
    true
    true
    645120
    true
    transferLowerBoundReadyHere
    refl

canonicalAdjointnessApproxInverseReadiness :
  AdjointnessApproxInverseReadiness
canonicalAdjointnessApproxInverseReadiness =
  mkAdjointnessApproxInverseReadiness
    canonicalAdjointnessApproxInverseObligationRow
    true
    true
    true
    true
    true
    externalCommonCarrierConstructionClosedHere
    refl

canonicalProjectionStabilityReadiness : ProjectionStabilityReadiness
canonicalProjectionStabilityReadiness =
  mkProjectionStabilityReadiness
    canonicalProjectionStabilityObligationRow
    true
    true
    true
    true
    externalCommonCarrierConstructionClosedHere
    refl

canonicalWeakRecoveryFeedThroughReadiness :
  WeakRecoveryFeedThroughReadiness
canonicalWeakRecoveryFeedThroughReadiness =
  mkWeakRecoveryFeedThroughReadiness
    canonicalWeakRecoveryFeedThroughObligationRow
    Reducer116.canonicalWeakCompactnessFeed
    Reducer116.canonicalRecoveryLimsupFeed
    Propagator117.canonicalCommonCarrierFeedThroughPropagationRoute
    true
    true
    true
    true
    true
    commonCarrierFeedThroughClosedHere
    refl

canonicalEstimateClosureReadiness : EstimateClosureReadiness
canonicalEstimateClosureReadiness =
  mkEstimateClosureReadiness
    canonicalEstimateClosureObligationRow
    Estimate114.canonicalGaugeQuotientClosureCriterion
    Estimate114.canonicalUniformNormConstantAssembly
    Estimate114.canonicalQuadratureResidualClosure
    Estimate114.canonicalInverseProjectionClosure
    Estimate114.canonicalWeakRecoveryFeedThroughRequirements
    true
    estimate114ClosedInput
    refl

canonicalObligationRows : List ConstructionObligationRow
canonicalObligationRows =
  canonicalEAPaMapObligationRow
  ∷ canonicalQuotientCompatibilityObligationRow
  ∷ canonicalNormWindowObligationRow
  ∷ canonicalAdjointnessApproxInverseObligationRow
  ∷ canonicalProjectionStabilityObligationRow
  ∷ canonicalWeakRecoveryFeedThroughObligationRow
  ∷ canonicalEstimateClosureObligationRow
  ∷ []

canonicalConstructionReadinessObligations :
  ConstructionReadinessObligations
canonicalConstructionReadinessObligations =
  mkConstructionReadinessObligations
    canonicalEAPaMapReadiness
    canonicalQuotientCompatibilityReadiness
    canonicalNormWindowReadiness
    canonicalAdjointnessApproxInverseReadiness
    canonicalProjectionStabilityReadiness
    canonicalWeakRecoveryFeedThroughReadiness
    canonicalEstimateClosureReadiness
    canonicalObligationRows
    constructionReadinessInputsRecorded
    externalCommonCarrierConstructionClosedHere
    commonCarrierFeedThroughClosedHere
    transferLowerBoundReadyHere
    refl
    refl
    refl
    obligation-recorded

canonicalConstructionBoundary : ConstructionBoundary
canonicalConstructionBoundary =
  mkConstructionBoundary
    nonClosureBoundaryText
    constructionReadinessPackageAssembledHere
    externalCommonCarrierConstructionClosedHere
    commonCarrierConstructionTheoremProvedHere
    commonCarrierFeedThroughClosedHere
    transferLowerBoundReadyHere
    clayYangMillsPromoted
    refl
    refl
    refl
    refl
    refl
    construction-boundary-fail-closed

canonicalEvidenceLedger : List String
canonicalEvidenceLedger =
  modulePath
  ∷ sprint111CarrierSourcePath
  ∷ sprint114EstimateSourcePath
  ∷ sprint116ReducerSourcePath
  ∷ sprint117PropagatorSourcePath
  ∷ readinessRouteText
  ∷ eAPaMapReadinessText
  ∷ quotientCompatibilityReadinessText
  ∷ normWindowReadinessText
  ∷ adjointnessApproxInverseReadinessText
  ∷ projectionStabilityReadinessText
  ∷ weakRecoveryFeedThroughReadinessText
  ∷ estimateClosureReadinessText
  ∷ nonClosureBoundaryText
  ∷ canonicalReceiptText
  ∷ finalReceiptText
  ∷ []

canonicalReadinessReceipt : ReadinessReceipt
canonicalReadinessReceipt =
  mkReadinessReceipt
    canonicalReceiptText
    canonicalStableReadinessInputs
    canonicalSourcePathLedger
    canonicalConstructionReadinessObligations
    canonicalConstructionBoundary
    canonicalReadinessLanes
    canonicalEvidenceLedger
    canonicalReceiptRecorded
    true
    externalCommonCarrierConstructionClosedHere
    commonCarrierConstructionTheoremProvedHere
    commonCarrierFeedThroughClosedHere
    transferLowerBoundReadyHere
    clayYangMillsPromoted
    refl
    refl
    refl
    refl
    refl

canonicalFinalReceipt : FinalReceipt
canonicalFinalReceipt =
  mkFinalReceipt
    finalReceiptText
    canonicalReadinessReceipt
    finalReceiptRecorded
    constructionReadinessPackageAssembledHere
    true
    sourcePathLedgerRecorded
    externalCommonCarrierConstructionClosedHere
    commonCarrierConstructionTheoremProvedHere
    commonCarrierFeedThroughClosedHere
    transferLowerBoundReadyHere
    clayYangMillsPromoted
    refl
    refl
    refl
    refl
    refl
    final-receipt-recorded

canonicalYMSprint118CommonCarrierConstructionReadinessReceipt :
  YMSprint118CommonCarrierConstructionReadinessReceipt
canonicalYMSprint118CommonCarrierConstructionReadinessReceipt =
  mkYMSprint118CommonCarrierConstructionReadinessReceipt
    sprintNumber
    modulePath
    canonicalReadinessReceipt
    canonicalFinalReceipt
    finalReceiptRecorded
    clayYangMillsPromoted
    refl

canonicalReceipt :
  YMSprint118CommonCarrierConstructionReadinessReceipt
canonicalReceipt =
  canonicalYMSprint118CommonCarrierConstructionReadinessReceipt

finalReceipt : FinalReceipt
finalReceipt =
  canonicalFinalReceipt

canonicalExternalCommonCarrierConstructionClosedHereIsFalse :
  externalCommonCarrierConstructionClosedHere ≡ false
canonicalExternalCommonCarrierConstructionClosedHereIsFalse =
  refl

canonicalCommonCarrierConstructionTheoremProvedHereIsFalse :
  commonCarrierConstructionTheoremProvedHere ≡ false
canonicalCommonCarrierConstructionTheoremProvedHereIsFalse =
  refl

canonicalCommonCarrierFeedThroughClosedHereIsFalse :
  commonCarrierFeedThroughClosedHere ≡ false
canonicalCommonCarrierFeedThroughClosedHereIsFalse =
  refl

canonicalTransferLowerBoundReadyHereIsFalse :
  transferLowerBoundReadyHere ≡ false
canonicalTransferLowerBoundReadyHereIsFalse =
  refl

canonicalClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalClayYangMillsPromotedIsFalse =
  refl

canonicalCarrier111ClosedInputIsFalse :
  carrier111ClosedInput ≡ false
canonicalCarrier111ClosedInputIsFalse =
  refl

canonicalEstimate114ClosedInputIsFalse :
  estimate114ClosedInput ≡ false
canonicalEstimate114ClosedInputIsFalse =
  refl

canonicalReducer116ExternalCommonCarrierClosedInputIsFalse :
  reducer116ExternalCommonCarrierClosedInput ≡ false
canonicalReducer116ExternalCommonCarrierClosedInputIsFalse =
  refl

canonicalReducer116TransferReadyInputIsFalse :
  reducer116TransferReadyInput ≡ false
canonicalReducer116TransferReadyInputIsFalse =
  refl

canonicalPropagator117FeedThroughClosedInputIsFalse :
  propagator117FeedThroughClosedInput ≡ false
canonicalPropagator117FeedThroughClosedInputIsFalse =
  refl

canonicalPropagator117ExternalCommonCarrierClosedInputIsFalse :
  propagator117ExternalCommonCarrierClosedInput ≡ false
canonicalPropagator117ExternalCommonCarrierClosedInputIsFalse =
  refl

canonicalReadinessPackageAssembledHereIsTrue :
  constructionReadinessPackageAssembledHere ≡ true
canonicalReadinessPackageAssembledHereIsTrue =
  refl
