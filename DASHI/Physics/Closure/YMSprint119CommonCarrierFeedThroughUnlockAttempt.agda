module DASHI.Physics.Closure.YMSprint119CommonCarrierFeedThroughUnlockAttempt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint118CriterionFeedAggregator
  as Feed118
import DASHI.Physics.Closure.YMSprint118CommonCarrierConstructionReadiness
  as Readiness118
import DASHI.Physics.Closure.YMSprint117CommonCarrierFeedThroughPropagator
  as Propagator117

------------------------------------------------------------------------
-- Sprint119 common-carrier feed-through unlock attempt.
--
-- Sprint118 already aggregated the norm, residual, and sector criterion feeds
-- as true, and assembled the common-carrier construction-readiness package as
-- true.  This module consumes those exact receipts and records the remaining
-- gates for common-carrier feed-through: an external common-carrier
-- construction theorem, weak compactness/Mosco aggregate, transfer calculus
-- aggregate, and readiness propagation.  The receipt is inhabited, but every
-- theorem, transfer, mass-gap, and Clay promotion flag remains fail-closed.

sprintNumber : Nat
sprintNumber = 119

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint119CommonCarrierFeedThroughUnlockAttempt.agda"

sprint118CriterionFeedAggregatorPath : String
sprint118CriterionFeedAggregatorPath =
  Feed118.modulePath

sprint118CommonCarrierConstructionReadinessPath : String
sprint118CommonCarrierConstructionReadinessPath =
  Readiness118.modulePath

sprint117CommonCarrierFeedThroughPropagatorPath : String
sprint117CommonCarrierFeedThroughPropagatorPath =
  Propagator117.modulePath

criterionFeedsAggregatedHere : Bool
criterionFeedsAggregatedHere = true

constructionReadinessAssembledHere : Bool
constructionReadinessAssembledHere = true

feedThroughUnlockAttemptRecorded : Bool
feedThroughUnlockAttemptRecorded = true

blockerRowsRecorded : Bool
blockerRowsRecorded = true

commonCarrierFeedThroughClosedHere : Bool
commonCarrierFeedThroughClosedHere = false

externalCommonCarrierClosedHere : Bool
externalCommonCarrierClosedHere = false

externalCommonCarrierConstructionClosedHere : Bool
externalCommonCarrierConstructionClosedHere = false

externalCommonCarrierConstructionTheoremProvedHere : Bool
externalCommonCarrierConstructionTheoremProvedHere = false

transferLowerBoundReadyHere : Bool
transferLowerBoundReadyHere = false

transferLowerBoundTheoremProvedHere : Bool
transferLowerBoundTheoremProvedHere = false

continuumMassGapProvedHere : Bool
continuumMassGapProvedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

sourcePathLedgerText : String
sourcePathLedgerText =
  "Sprint119 consumes Sprint118 criterion-feed aggregation, Sprint118 construction-readiness assembly, and Sprint117 common-carrier feed-through propagation as typed receipts."

criterionFeedConsumptionText : String
criterionFeedConsumptionText =
  "Criterion-feed consumption: Sprint119 reuses the Sprint118 aggregated norm, residual, and sector true flags without changing the common-carrier boundary."

constructionReadinessConsumptionText : String
constructionReadinessConsumptionText =
  "Construction-readiness consumption: Sprint119 reuses the Sprint118 readiness assembly as a true package, while external common-carrier construction closure remains false."

unlockReductionText : String
unlockReductionText =
  "Unlock reduction: common-carrier feed-through is reduced to four remaining gates: external common-carrier construction theorem, weak compactness/Mosco aggregate, transfer calculus aggregate, and readiness propagation."

nonClosureBoundaryText : String
nonClosureBoundaryText =
  "Sprint119 records an unlock attempt only; common-carrier feed-through, external common carrier, external construction closure, transfer lower-bound readiness, transfer theorem, continuum mass gap, and Clay promotion remain false."

canonicalReceiptText : String
canonicalReceiptText =
  "Canonical Sprint119 receipt: true criterion feeds and true construction-readiness assembly are consumed, four blocker rows are recorded, and all downstream theorem and promotion flags stay false."

finalReceiptText : String
finalReceiptText =
  "Final Sprint119 receipt: the common-carrier feed-through unlock attempt is recorded as an inhabited status receipt with no feed-through closure, no transfer lower-bound theorem, no continuum mass gap, and no Clay promotion."

data UnlockLane : Set where
  source-path-lane :
    UnlockLane
  criterion-feed-lane :
    UnlockLane
  construction-readiness-lane :
    UnlockLane
  external-construction-theorem-lane :
    UnlockLane
  weak-mosco-aggregate-lane :
    UnlockLane
  transfer-calculus-aggregate-lane :
    UnlockLane
  readiness-propagation-lane :
    UnlockLane
  theorem-boundary-lane :
    UnlockLane
  receipt-lane :
    UnlockLane

data UnlockStatus : Set where
  source-paths-recorded :
    UnlockStatus
  criterion-feeds-consumed :
    UnlockStatus
  construction-readiness-consumed :
    UnlockStatus
  blocker-row-recorded :
    UnlockStatus
  unlock-attempt-recorded :
    UnlockStatus
  boundary-fail-closed :
    UnlockStatus
  final-receipt-recorded :
    UnlockStatus

data RemainingGate : Set where
  external-common-carrier-construction-theorem :
    RemainingGate
  weak-compactness-mosco-aggregate :
    RemainingGate
  transfer-calculus-aggregate :
    RemainingGate
  readiness-propagation :
    RemainingGate

canonicalUnlockLanes : List UnlockLane
canonicalUnlockLanes =
  source-path-lane
  ∷ criterion-feed-lane
  ∷ construction-readiness-lane
  ∷ external-construction-theorem-lane
  ∷ weak-mosco-aggregate-lane
  ∷ transfer-calculus-aggregate-lane
  ∷ readiness-propagation-lane
  ∷ theorem-boundary-lane
  ∷ receipt-lane
  ∷ []

record SourcePathLedger : Set where
  constructor mkSourcePathLedger
  field
    currentModulePath :
      String
    criterionFeedAggregatorPath :
      String
    constructionReadinessPath :
      String
    feedThroughPropagatorPath :
      String
    statement :
      String
    ledgerRecorded :
      Bool
    ledgerRecordedIsTrue :
      ledgerRecorded ≡ true
    status :
      UnlockStatus

record ConsumedCriterionFeeds : Setω where
  constructor mkConsumedCriterionFeeds
  field
    aggregatorReceipt :
      Feed118.YMSprint118CriterionFeedAggregatorReceipt
    statement :
      String
    normFeedClosed :
      Bool
    normFeedClosedIsTrue :
      normFeedClosed ≡ true
    normFeedEqualsSprint118 :
      normFeedClosed ≡ Feed118.normFeedClosedHere
    residualFeedClosed :
      Bool
    residualFeedClosedIsTrue :
      residualFeedClosed ≡ true
    residualFeedEqualsSprint118 :
      residualFeedClosed ≡ Feed118.residualFeedClosedHere
    sectorFeedClosed :
      Bool
    sectorFeedClosedIsTrue :
      sectorFeedClosed ≡ true
    sectorFeedEqualsSprint118 :
      sectorFeedClosed ≡ Feed118.sectorFeedClosedHere
    feedsAggregatedHere :
      Bool
    feedsAggregatedHereIsTrue :
      feedsAggregatedHere ≡ true
    status :
      UnlockStatus

record ConsumedConstructionReadiness : Setω where
  constructor mkConsumedConstructionReadiness
  field
    readinessReceipt :
      Readiness118.YMSprint118CommonCarrierConstructionReadinessReceipt
    propagatorReceipt :
      Propagator117.YMSprint117CommonCarrierFeedThroughPropagatorReceipt
    statement :
      String
    readinessAssembledHere :
      Bool
    readinessAssembledHereIsTrue :
      readinessAssembledHere ≡ true
    readinessEqualsSprint118 :
      readinessAssembledHere ≡
      Readiness118.constructionReadinessPackageAssembledHere
    sprint118ExternalConstructionClosed :
      Bool
    sprint118ExternalConstructionClosedIsFalse :
      sprint118ExternalConstructionClosed ≡ false
    sprint117FeedThroughClosed :
      Bool
    sprint117FeedThroughClosedIsFalse :
      sprint117FeedThroughClosed ≡ false
    status :
      UnlockStatus

record RemainingGateRow : Set where
  constructor mkRemainingGateRow
  field
    gate :
      RemainingGate
    lane :
      UnlockLane
    sourcePath :
      String
    statement :
      String
    requiredForFeedThrough :
      Bool
    rowRecorded :
      Bool
    rowRecordedIsTrue :
      rowRecorded ≡ true
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false
    status :
      UnlockStatus

record UnlockReduction : Set where
  constructor mkUnlockReduction
  field
    statement :
      String
    externalConstructionTheoremRow :
      RemainingGateRow
    weakMoscoAggregateRow :
      RemainingGateRow
    transferCalculusAggregateRow :
      RemainingGateRow
    readinessPropagationRow :
      RemainingGateRow
    rows :
      List RemainingGateRow
    rowsRecorded :
      Bool
    rowsRecordedIsTrue :
      rowsRecorded ≡ true
    feedThroughClosed :
      Bool
    feedThroughClosedIsFalse :
      feedThroughClosed ≡ false
    transferReady :
      Bool
    transferReadyIsFalse :
      transferReady ≡ false
    status :
      UnlockStatus

record TheoremBoundary : Set where
  constructor mkTheoremBoundary
  field
    statement :
      String
    commonCarrierFeedThroughClosed :
      Bool
    commonCarrierFeedThroughClosedIsFalse :
      commonCarrierFeedThroughClosed ≡ false
    externalCommonCarrierClosed :
      Bool
    externalCommonCarrierClosedIsFalse :
      externalCommonCarrierClosed ≡ false
    externalCommonCarrierConstructionClosed :
      Bool
    externalCommonCarrierConstructionClosedIsFalse :
      externalCommonCarrierConstructionClosed ≡ false
    externalCommonCarrierConstructionTheoremProved :
      Bool
    externalCommonCarrierConstructionTheoremProvedIsFalse :
      externalCommonCarrierConstructionTheoremProved ≡ false
    transferLowerBoundReady :
      Bool
    transferLowerBoundReadyIsFalse :
      transferLowerBoundReady ≡ false
    transferLowerBoundTheoremProved :
      Bool
    transferLowerBoundTheoremProvedIsFalse :
      transferLowerBoundTheoremProved ≡ false
    continuumMassGapProved :
      Bool
    continuumMassGapProvedIsFalse :
      continuumMassGapProved ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      UnlockStatus

record FinalReceipt : Setω where
  constructor mkFinalReceipt
  field
    statement :
      String
    consumedCriterionFeeds :
      ConsumedCriterionFeeds
    consumedConstructionReadiness :
      ConsumedConstructionReadiness
    unlockReduction :
      UnlockReduction
    theoremBoundary :
      TheoremBoundary
    receiptRecorded :
      Bool
    receiptRecordedIsTrue :
      receiptRecorded ≡ true
    criterionFeedsAggregated :
      Bool
    criterionFeedsAggregatedIsTrue :
      criterionFeedsAggregated ≡ true
    constructionReadinessAssembled :
      Bool
    constructionReadinessAssembledIsTrue :
      constructionReadinessAssembled ≡ true
    commonCarrierFeedThroughClosed :
      Bool
    commonCarrierFeedThroughClosedIsFalse :
      commonCarrierFeedThroughClosed ≡ false
    externalCommonCarrierClosed :
      Bool
    externalCommonCarrierClosedIsFalse :
      externalCommonCarrierClosed ≡ false
    externalCommonCarrierConstructionClosed :
      Bool
    externalCommonCarrierConstructionClosedIsFalse :
      externalCommonCarrierConstructionClosed ≡ false
    transferLowerBoundReady :
      Bool
    transferLowerBoundReadyIsFalse :
      transferLowerBoundReady ≡ false
    transferLowerBoundTheoremProved :
      Bool
    transferLowerBoundTheoremProvedIsFalse :
      transferLowerBoundTheoremProved ≡ false
    continuumMassGapProved :
      Bool
    continuumMassGapProvedIsFalse :
      continuumMassGapProved ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      UnlockStatus

record YMSprint119CommonCarrierFeedThroughUnlockAttemptReceipt : Setω where
  constructor mkYMSprint119CommonCarrierFeedThroughUnlockAttemptReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    sourcePaths :
      SourcePathLedger
    criterionFeeds :
      ConsumedCriterionFeeds
    constructionReadiness :
      ConsumedConstructionReadiness
    unlockReduction :
      UnlockReduction
    theoremBoundary :
      TheoremBoundary
    finalReceiptField :
      FinalReceipt
    lanes :
      List UnlockLane
    sourcePathList :
      List String
    evidenceLedger :
      List String
    receiptRecorded :
      Bool
    receiptRecordedIsTrue :
      receiptRecorded ≡ true
    criterionFeedsAggregatedHereFlag :
      Bool
    criterionFeedsAggregatedHereFlagIsTrue :
      criterionFeedsAggregatedHereFlag ≡ true
    constructionReadinessAssembledHereFlag :
      Bool
    constructionReadinessAssembledHereFlagIsTrue :
      constructionReadinessAssembledHereFlag ≡ true
    blockerRowsRecordedHereFlag :
      Bool
    blockerRowsRecordedHereFlagIsTrue :
      blockerRowsRecordedHereFlag ≡ true
    commonCarrierFeedThroughClosedHereFlag :
      Bool
    commonCarrierFeedThroughClosedHereFlagIsFalse :
      commonCarrierFeedThroughClosedHereFlag ≡ false
    externalCommonCarrierClosedHereFlag :
      Bool
    externalCommonCarrierClosedHereFlagIsFalse :
      externalCommonCarrierClosedHereFlag ≡ false
    externalCommonCarrierConstructionClosedHereFlag :
      Bool
    externalCommonCarrierConstructionClosedHereFlagIsFalse :
      externalCommonCarrierConstructionClosedHereFlag ≡ false
    transferLowerBoundReadyHereFlag :
      Bool
    transferLowerBoundReadyHereFlagIsFalse :
      transferLowerBoundReadyHereFlag ≡ false
    transferLowerBoundTheoremProvedHereFlag :
      Bool
    transferLowerBoundTheoremProvedHereFlagIsFalse :
      transferLowerBoundTheoremProvedHereFlag ≡ false
    continuumMassGapProvedHereFlag :
      Bool
    continuumMassGapProvedHereFlagIsFalse :
      continuumMassGapProvedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open SourcePathLedger public
open ConsumedCriterionFeeds public
open ConsumedConstructionReadiness public
open RemainingGateRow public
open UnlockReduction public
open TheoremBoundary public
open FinalReceipt public
open YMSprint119CommonCarrierFeedThroughUnlockAttemptReceipt public

canonicalSourcePathLedger : SourcePathLedger
canonicalSourcePathLedger =
  mkSourcePathLedger
    modulePath
    sprint118CriterionFeedAggregatorPath
    sprint118CommonCarrierConstructionReadinessPath
    sprint117CommonCarrierFeedThroughPropagatorPath
    sourcePathLedgerText
    feedThroughUnlockAttemptRecorded
    refl
    source-paths-recorded

canonicalConsumedCriterionFeeds : ConsumedCriterionFeeds
canonicalConsumedCriterionFeeds =
  mkConsumedCriterionFeeds
    Feed118.canonicalReceipt
    criterionFeedConsumptionText
    Feed118.normFeedClosedHere
    refl
    refl
    Feed118.residualFeedClosedHere
    refl
    refl
    Feed118.sectorFeedClosedHere
    refl
    refl
    criterionFeedsAggregatedHere
    refl
    criterion-feeds-consumed

canonicalConsumedConstructionReadiness : ConsumedConstructionReadiness
canonicalConsumedConstructionReadiness =
  mkConsumedConstructionReadiness
    Readiness118.canonicalReceipt
    Propagator117.canonicalReceipt
    constructionReadinessConsumptionText
    constructionReadinessAssembledHere
    refl
    refl
    Readiness118.externalCommonCarrierConstructionClosedHere
    refl
    Propagator117.commonCarrierFeedThroughClosedHere
    refl
    construction-readiness-consumed

externalConstructionTheoremText : String
externalConstructionTheoremText =
  "Remaining gate: prove the external common-carrier construction theorem on the same carrier convention consumed by Sprint118 readiness."

weakMoscoAggregateText : String
weakMoscoAggregateText =
  "Remaining gate: aggregate weak compactness, Mosco liminf, no bottom-spectrum pollution, and recovery limsup into one common-carrier compactness package."

transferCalculusAggregateText : String
transferCalculusAggregateText =
  "Remaining gate: aggregate uniform form lower bound, log-generator calculus, and spectral transport into the transfer lower-bound calculus package."

readinessPropagationText : String
readinessPropagationText =
  "Remaining gate: propagate the true criterion feeds and construction-readiness package through the common-carrier feed-through route."

canonicalExternalConstructionTheoremRow : RemainingGateRow
canonicalExternalConstructionTheoremRow =
  mkRemainingGateRow
    external-common-carrier-construction-theorem
    external-construction-theorem-lane
    sprint118CommonCarrierConstructionReadinessPath
    externalConstructionTheoremText
    true
    blockerRowsRecorded
    refl
    externalCommonCarrierConstructionTheoremProvedHere
    refl
    blocker-row-recorded

canonicalWeakMoscoAggregateRow : RemainingGateRow
canonicalWeakMoscoAggregateRow =
  mkRemainingGateRow
    weak-compactness-mosco-aggregate
    weak-mosco-aggregate-lane
    sprint117CommonCarrierFeedThroughPropagatorPath
    weakMoscoAggregateText
    true
    blockerRowsRecorded
    refl
    commonCarrierFeedThroughClosedHere
    refl
    blocker-row-recorded

canonicalTransferCalculusAggregateRow : RemainingGateRow
canonicalTransferCalculusAggregateRow =
  mkRemainingGateRow
    transfer-calculus-aggregate
    transfer-calculus-aggregate-lane
    sprint117CommonCarrierFeedThroughPropagatorPath
    transferCalculusAggregateText
    true
    blockerRowsRecorded
    refl
    transferLowerBoundReadyHere
    refl
    blocker-row-recorded

canonicalReadinessPropagationRow : RemainingGateRow
canonicalReadinessPropagationRow =
  mkRemainingGateRow
    readiness-propagation
    readiness-propagation-lane
    sprint117CommonCarrierFeedThroughPropagatorPath
    readinessPropagationText
    true
    blockerRowsRecorded
    refl
    commonCarrierFeedThroughClosedHere
    refl
    blocker-row-recorded

canonicalRemainingGateRows : List RemainingGateRow
canonicalRemainingGateRows =
  canonicalExternalConstructionTheoremRow
  ∷ canonicalWeakMoscoAggregateRow
  ∷ canonicalTransferCalculusAggregateRow
  ∷ canonicalReadinessPropagationRow
  ∷ []

canonicalUnlockReduction : UnlockReduction
canonicalUnlockReduction =
  mkUnlockReduction
    unlockReductionText
    canonicalExternalConstructionTheoremRow
    canonicalWeakMoscoAggregateRow
    canonicalTransferCalculusAggregateRow
    canonicalReadinessPropagationRow
    canonicalRemainingGateRows
    blockerRowsRecorded
    refl
    commonCarrierFeedThroughClosedHere
    refl
    transferLowerBoundReadyHere
    refl
    unlock-attempt-recorded

canonicalTheoremBoundary : TheoremBoundary
canonicalTheoremBoundary =
  mkTheoremBoundary
    nonClosureBoundaryText
    commonCarrierFeedThroughClosedHere
    refl
    externalCommonCarrierClosedHere
    refl
    externalCommonCarrierConstructionClosedHere
    refl
    externalCommonCarrierConstructionTheoremProvedHere
    refl
    transferLowerBoundReadyHere
    refl
    transferLowerBoundTheoremProvedHere
    refl
    continuumMassGapProvedHere
    refl
    clayYangMillsPromoted
    refl
    boundary-fail-closed

canonicalFinalReceipt : FinalReceipt
canonicalFinalReceipt =
  mkFinalReceipt
    finalReceiptText
    canonicalConsumedCriterionFeeds
    canonicalConsumedConstructionReadiness
    canonicalUnlockReduction
    canonicalTheoremBoundary
    feedThroughUnlockAttemptRecorded
    refl
    criterionFeedsAggregatedHere
    refl
    constructionReadinessAssembledHere
    refl
    commonCarrierFeedThroughClosedHere
    refl
    externalCommonCarrierClosedHere
    refl
    externalCommonCarrierConstructionClosedHere
    refl
    transferLowerBoundReadyHere
    refl
    transferLowerBoundTheoremProvedHere
    refl
    continuumMassGapProvedHere
    refl
    clayYangMillsPromoted
    refl
    final-receipt-recorded

canonicalSourcePathList : List String
canonicalSourcePathList =
  modulePath
  ∷ sprint118CriterionFeedAggregatorPath
  ∷ sprint118CommonCarrierConstructionReadinessPath
  ∷ sprint117CommonCarrierFeedThroughPropagatorPath
  ∷ []

canonicalEvidenceLedger : List String
canonicalEvidenceLedger =
  sourcePathLedgerText
  ∷ criterionFeedConsumptionText
  ∷ constructionReadinessConsumptionText
  ∷ unlockReductionText
  ∷ externalConstructionTheoremText
  ∷ weakMoscoAggregateText
  ∷ transferCalculusAggregateText
  ∷ readinessPropagationText
  ∷ nonClosureBoundaryText
  ∷ canonicalReceiptText
  ∷ finalReceiptText
  ∷ Feed118.finalReceiptText
  ∷ Readiness118.finalReceiptText
  ∷ Propagator117.finalReceiptText
  ∷ []

canonicalYMSprint119CommonCarrierFeedThroughUnlockAttemptReceipt :
  YMSprint119CommonCarrierFeedThroughUnlockAttemptReceipt
canonicalYMSprint119CommonCarrierFeedThroughUnlockAttemptReceipt =
  mkYMSprint119CommonCarrierFeedThroughUnlockAttemptReceipt
    sprintNumber
    modulePath
    canonicalSourcePathLedger
    canonicalConsumedCriterionFeeds
    canonicalConsumedConstructionReadiness
    canonicalUnlockReduction
    canonicalTheoremBoundary
    canonicalFinalReceipt
    canonicalUnlockLanes
    canonicalSourcePathList
    canonicalEvidenceLedger
    feedThroughUnlockAttemptRecorded
    refl
    criterionFeedsAggregatedHere
    refl
    constructionReadinessAssembledHere
    refl
    blockerRowsRecorded
    refl
    commonCarrierFeedThroughClosedHere
    refl
    externalCommonCarrierClosedHere
    refl
    externalCommonCarrierConstructionClosedHere
    refl
    transferLowerBoundReadyHere
    refl
    transferLowerBoundTheoremProvedHere
    refl
    continuumMassGapProvedHere
    refl
    clayYangMillsPromoted
    refl

canonicalReceipt :
  YMSprint119CommonCarrierFeedThroughUnlockAttemptReceipt
canonicalReceipt =
  canonicalYMSprint119CommonCarrierFeedThroughUnlockAttemptReceipt

finalReceipt : FinalReceipt
finalReceipt =
  canonicalFinalReceipt

canonicalCriterionFeedsAggregatedHereIsTrue :
  criterionFeedsAggregatedHereFlag canonicalReceipt ≡ true
canonicalCriterionFeedsAggregatedHereIsTrue =
  refl

canonicalConstructionReadinessAssembledHereIsTrue :
  constructionReadinessAssembledHereFlag canonicalReceipt ≡ true
canonicalConstructionReadinessAssembledHereIsTrue =
  refl

canonicalBlockerRowsRecordedHereIsTrue :
  blockerRowsRecordedHereFlag canonicalReceipt ≡ true
canonicalBlockerRowsRecordedHereIsTrue =
  refl

canonicalNormFeedConsumedIsTrue :
  ConsumedCriterionFeeds.normFeedClosed canonicalConsumedCriterionFeeds ≡ true
canonicalNormFeedConsumedIsTrue =
  refl

canonicalResidualFeedConsumedIsTrue :
  ConsumedCriterionFeeds.residualFeedClosed canonicalConsumedCriterionFeeds ≡ true
canonicalResidualFeedConsumedIsTrue =
  refl

canonicalSectorFeedConsumedIsTrue :
  ConsumedCriterionFeeds.sectorFeedClosed canonicalConsumedCriterionFeeds ≡ true
canonicalSectorFeedConsumedIsTrue =
  refl

canonicalCommonCarrierFeedThroughClosedHereIsFalse :
  commonCarrierFeedThroughClosedHereFlag canonicalReceipt ≡ false
canonicalCommonCarrierFeedThroughClosedHereIsFalse =
  refl

canonicalExternalCommonCarrierClosedHereIsFalse :
  externalCommonCarrierClosedHereFlag canonicalReceipt ≡ false
canonicalExternalCommonCarrierClosedHereIsFalse =
  refl

canonicalExternalCommonCarrierConstructionClosedHereIsFalse :
  externalCommonCarrierConstructionClosedHereFlag canonicalReceipt ≡ false
canonicalExternalCommonCarrierConstructionClosedHereIsFalse =
  refl

canonicalTransferLowerBoundReadyHereIsFalse :
  transferLowerBoundReadyHereFlag canonicalReceipt ≡ false
canonicalTransferLowerBoundReadyHereIsFalse =
  refl

canonicalTransferLowerBoundTheoremProvedHereIsFalse :
  transferLowerBoundTheoremProvedHereFlag canonicalReceipt ≡ false
canonicalTransferLowerBoundTheoremProvedHereIsFalse =
  refl

canonicalContinuumMassGapProvedHereIsFalse :
  continuumMassGapProvedHereFlag canonicalReceipt ≡ false
canonicalContinuumMassGapProvedHereIsFalse =
  refl

canonicalClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalClayYangMillsPromotedIsFalse =
  refl

canonicalFinalReceiptClayYangMillsPromotedIsFalse :
  FinalReceipt.clayYangMillsPromotedHere finalReceipt ≡ false
canonicalFinalReceiptClayYangMillsPromotedIsFalse =
  refl
