module DASHI.Physics.Closure.YMSprint120CommonCarrierFeedThroughClosureReducer where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint119CommonCarrierFeedThroughUnlockAttempt
  as Unlock119
import DASHI.Physics.Closure.YMSprint119TransferReadinessUnlockReducer
  as Transfer119
import DASHI.Physics.Closure.YMSprint118CriterionFeedAggregator
  as Feed118
import DASHI.Physics.Closure.YMSprint118CommonCarrierConstructionReadiness
  as Readiness118

------------------------------------------------------------------------
-- Sprint120 common-carrier feed-through closure reducer.
--
-- This module records the complete reducer surface for common-carrier
-- feed-through.  It consumes the Sprint118 true criterion feeds and the
-- Sprint118 construction-readiness package, then records the remaining exact
-- rows: external common-carrier construction theorem, weak compactness
-- certificate, Mosco aggregate closure, transfer-calculus aggregate closure,
-- and readiness propagation.  The reducer and row ledger are inhabited here,
-- but every closure, transfer theorem, mass-gap, and Clay promotion flag
-- remains fail-closed.

sprintNumber : Nat
sprintNumber = 120

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint120CommonCarrierFeedThroughClosureReducer.agda"

sprint119UnlockAttemptPath : String
sprint119UnlockAttemptPath =
  Unlock119.modulePath

sprint119TransferReadinessUnlockReducerPath : String
sprint119TransferReadinessUnlockReducerPath =
  Transfer119.modulePath

sprint118CriterionFeedAggregatorPath : String
sprint118CriterionFeedAggregatorPath =
  Feed118.modulePath

sprint118CommonCarrierConstructionReadinessPath : String
sprint118CommonCarrierConstructionReadinessPath =
  Readiness118.modulePath

sprint119WeakCompactnessReducerPath : String
sprint119WeakCompactnessReducerPath =
  "DASHI/Physics/Closure/YMSprint119WeakCompactnessObligationReducer.agda"

sprint119MoscoAggregateReducerPath : String
sprint119MoscoAggregateReducerPath =
  "DASHI/Physics/Closure/YMSprint119MoscoAllObligationsReducer.agda"

sprint119TransferCalculusAggregateReducerPath : String
sprint119TransferCalculusAggregateReducerPath =
  "DASHI/Physics/Closure/YMSprint119TransferCalculusAllObligationsReducer.agda"

feedThroughClosureReducerRecorded : Bool
feedThroughClosureReducerRecorded = true

feedThroughClosureRowsComplete : Bool
feedThroughClosureRowsComplete = true

canonicalReceiptRecorded : Bool
canonicalReceiptRecorded = true

finalReceiptRecorded : Bool
finalReceiptRecorded = true

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

externalCommonCarrierConstructionTheoremProvedHere : Bool
externalCommonCarrierConstructionTheoremProvedHere = false

weakCompactnessCertificateClosedHere : Bool
weakCompactnessCertificateClosedHere = false

moscoAggregateClosureClosedHere : Bool
moscoAggregateClosureClosedHere = false

transferCalculusAggregateClosureClosedHere : Bool
transferCalculusAggregateClosureClosedHere = false

readinessPropagationClosedHere : Bool
readinessPropagationClosedHere = false

sourcePathLedgerText : String
sourcePathLedgerText =
  "Sprint120 consumes Sprint119 common-carrier feed-through unlock attempt, Sprint119 transfer-readiness unlock reducer, Sprint118 criterion-feed aggregator, and Sprint118 common-carrier construction-readiness receipts."

reducerStatementText : String
reducerStatementText =
  "Common-carrier feed-through closure requires true norm, residual, and sector criterion feeds, plus an external common-carrier construction theorem, weak compactness certificate, Mosco aggregate closure, transfer-calculus aggregate closure, and readiness propagation on the same carrier convention."

falseBoundaryText : String
falseBoundaryText =
  "Sprint120 records the feed-through closure reducer only; common-carrier feed-through, external common carrier, transfer lower-bound readiness, transfer theorem, continuum mass gap, and Clay Yang-Mills promotion remain false."

canonicalReceiptText : String
canonicalReceiptText =
  "Canonical Sprint120 receipt: reducer recorded, exact rows complete, source paths and upstream false flags captured, true criterion feeds consumed, and all downstream theorem flags fail-closed."

finalReceiptText : String
finalReceiptText =
  "Final Sprint120 receipt: feedThroughClosureReducerRecorded=true and feedThroughClosureRowsComplete=true, while commonCarrierFeedThroughClosedHere=false and no transfer, mass-gap, or Clay promotion is claimed."

data ClosureRequirement : Set where
  norm-criterion-feed :
    ClosureRequirement
  residual-criterion-feed :
    ClosureRequirement
  sector-criterion-feed :
    ClosureRequirement
  external-common-carrier-construction-theorem :
    ClosureRequirement
  weak-compactness-certificate :
    ClosureRequirement
  mosco-aggregate-closure :
    ClosureRequirement
  transfer-calculus-aggregate-closure :
    ClosureRequirement
  readiness-propagation :
    ClosureRequirement
  final-governance-boundary :
    ClosureRequirement

data ClosureRowStatus : Set where
  true-feed-consumed :
    ClosureRowStatus
  external-theorem-required :
    ClosureRowStatus
  compactness-certificate-required :
    ClosureRowStatus
  aggregate-closure-required :
    ClosureRowStatus
  propagation-required :
    ClosureRowStatus
  fail-closed-boundary :
    ClosureRowStatus
  canonical-receipt-recorded :
    ClosureRowStatus
  final-receipt-recorded :
    ClosureRowStatus

record SourcePathLedger : Set where
  constructor mkSourcePathLedger
  field
    currentModulePath :
      String
    unlockAttemptPath :
      String
    transferReadinessUnlockReducerPath :
      String
    criterionFeedAggregatorPath :
      String
    constructionReadinessPath :
      String
    weakCompactnessReducerPath :
      String
    moscoAggregateReducerPath :
      String
    transferCalculusAggregateReducerPath :
      String
    statement :
      String
    ledgerRecorded :
      Bool
    ledgerRecordedIsTrue :
      ledgerRecorded ≡ true

record UpstreamReceipts : Setω where
  constructor mkUpstreamReceipts
  field
    unlockAttemptReceipt :
      Unlock119.YMSprint119CommonCarrierFeedThroughUnlockAttemptReceipt
    transferReadinessUnlockReceipt :
      Transfer119.YMSprint119TransferReadinessUnlockReducerReceipt
    criterionFeedAggregatorReceipt :
      Feed118.YMSprint118CriterionFeedAggregatorReceipt
    constructionReadinessReceipt :
      Readiness118.YMSprint118CommonCarrierConstructionReadinessReceipt
    receiptsRecorded :
      Bool
    receiptsRecordedIsTrue :
      receiptsRecorded ≡ true

record ClosureRequirementRow : Set where
  constructor mkClosureRequirementRow
  field
    requirement :
      ClosureRequirement
    sourcePath :
      String
    upstreamClosedFlag :
      Bool
    upstreamFlagIsExpected :
      Bool
    upstreamFlagEquality :
      upstreamClosedFlag ≡ upstreamFlagIsExpected
    requiredForFeedThroughClosure :
      Bool
    requiredForFeedThroughClosureIsTrue :
      requiredForFeedThroughClosure ≡ true
    rowRecorded :
      Bool
    rowRecordedIsTrue :
      rowRecorded ≡ true
    statement :
      String
    status :
      ClosureRowStatus

record UpstreamFlagLedger : Set where
  constructor mkUpstreamFlagLedger
  field
    normFeedClosed :
      Bool
    normFeedClosedIsTrue :
      normFeedClosed ≡ true
    residualFeedClosed :
      Bool
    residualFeedClosedIsTrue :
      residualFeedClosed ≡ true
    sectorFeedClosed :
      Bool
    sectorFeedClosedIsTrue :
      sectorFeedClosed ≡ true
    sprint119FeedThroughClosed :
      Bool
    sprint119FeedThroughClosedIsFalse :
      sprint119FeedThroughClosed ≡ false
    sprint119TransferReady :
      Bool
    sprint119TransferReadyIsFalse :
      sprint119TransferReady ≡ false
    sprint119TransferTheoremProved :
      Bool
    sprint119TransferTheoremProvedIsFalse :
      sprint119TransferTheoremProved ≡ false
    sprint119ContinuumMassGapProved :
      Bool
    sprint119ContinuumMassGapProvedIsFalse :
      sprint119ContinuumMassGapProved ≡ false
    sprint119ClayPromoted :
      Bool
    sprint119ClayPromotedIsFalse :
      sprint119ClayPromoted ≡ false

record ClosureReducerPackage : Setω where
  constructor mkClosureReducerPackage
  field
    sourcePaths :
      SourcePathLedger
    upstreamReceipts :
      UpstreamReceipts
    upstreamFlags :
      UpstreamFlagLedger
    rows :
      List ClosureRequirementRow
    reducerStatement :
      String
    reducerRecorded :
      Bool
    reducerRecordedIsTrue :
      reducerRecorded ≡ true
    rowsComplete :
      Bool
    rowsCompleteIsTrue :
      rowsComplete ≡ true
    commonCarrierFeedThroughClosed :
      Bool
    commonCarrierFeedThroughClosedIsFalse :
      commonCarrierFeedThroughClosed ≡ false

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

record FinalReceipt : Setω where
  constructor mkFinalReceipt
  field
    statement :
      String
    package :
      ClosureReducerPackage
    theoremBoundary :
      TheoremBoundary
    canonicalReceiptRecordedHere :
      Bool
    canonicalReceiptRecordedHereIsTrue :
      canonicalReceiptRecordedHere ≡ true
    finalReceiptRecordedHere :
      Bool
    finalReceiptRecordedHereIsTrue :
      finalReceiptRecordedHere ≡ true
    feedThroughClosureReducerRecordedHere :
      Bool
    feedThroughClosureReducerRecordedHereIsTrue :
      feedThroughClosureReducerRecordedHere ≡ true
    feedThroughClosureRowsCompleteHere :
      Bool
    feedThroughClosureRowsCompleteHereIsTrue :
      feedThroughClosureRowsCompleteHere ≡ true
    commonCarrierFeedThroughClosedHereFlag :
      Bool
    commonCarrierFeedThroughClosedHereFlagIsFalse :
      commonCarrierFeedThroughClosedHereFlag ≡ false

record YMSprint120CommonCarrierFeedThroughClosureReducerReceipt : Setω where
  constructor mkYMSprint120CommonCarrierFeedThroughClosureReducerReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    package :
      ClosureReducerPackage
    finalReceiptField :
      FinalReceipt
    sourcePathList :
      List String
    evidenceLedger :
      List String
    feedThroughClosureReducerRecordedHere :
      Bool
    feedThroughClosureReducerRecordedHereIsTrue :
      feedThroughClosureReducerRecordedHere ≡ true
    feedThroughClosureRowsCompleteHere :
      Bool
    feedThroughClosureRowsCompleteHereIsTrue :
      feedThroughClosureRowsCompleteHere ≡ true
    commonCarrierFeedThroughClosedHereFlag :
      Bool
    commonCarrierFeedThroughClosedHereFlagIsFalse :
      commonCarrierFeedThroughClosedHereFlag ≡ false
    externalCommonCarrierClosedHereFlag :
      Bool
    externalCommonCarrierClosedHereFlagIsFalse :
      externalCommonCarrierClosedHereFlag ≡ false
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
open UpstreamReceipts public
open ClosureRequirementRow public
open UpstreamFlagLedger public
open ClosureReducerPackage public
open TheoremBoundary public
open FinalReceipt public
open YMSprint120CommonCarrierFeedThroughClosureReducerReceipt public

canonicalSourcePathLedger : SourcePathLedger
canonicalSourcePathLedger =
  mkSourcePathLedger
    modulePath
    sprint119UnlockAttemptPath
    sprint119TransferReadinessUnlockReducerPath
    sprint118CriterionFeedAggregatorPath
    sprint118CommonCarrierConstructionReadinessPath
    sprint119WeakCompactnessReducerPath
    sprint119MoscoAggregateReducerPath
    sprint119TransferCalculusAggregateReducerPath
    sourcePathLedgerText
    feedThroughClosureReducerRecorded
    refl

canonicalUpstreamReceipts : UpstreamReceipts
canonicalUpstreamReceipts =
  mkUpstreamReceipts
    Unlock119.canonicalReceipt
    Transfer119.canonicalReceipt
    Feed118.canonicalReceipt
    Readiness118.canonicalReceipt
    true
    refl

normCriterionFeedRow : ClosureRequirementRow
normCriterionFeedRow =
  mkClosureRequirementRow
    norm-criterion-feed
    sprint118CriterionFeedAggregatorPath
    Feed118.normFeedClosedHere
    true
    refl
    true
    refl
    feedThroughClosureRowsComplete
    refl
    Feed118.normFeedEvidenceText
    true-feed-consumed

residualCriterionFeedRow : ClosureRequirementRow
residualCriterionFeedRow =
  mkClosureRequirementRow
    residual-criterion-feed
    sprint118CriterionFeedAggregatorPath
    Feed118.residualFeedClosedHere
    true
    refl
    true
    refl
    feedThroughClosureRowsComplete
    refl
    Feed118.residualFeedEvidenceText
    true-feed-consumed

sectorCriterionFeedRow : ClosureRequirementRow
sectorCriterionFeedRow =
  mkClosureRequirementRow
    sector-criterion-feed
    sprint118CriterionFeedAggregatorPath
    Feed118.sectorFeedClosedHere
    true
    refl
    true
    refl
    feedThroughClosureRowsComplete
    refl
    Feed118.sectorFeedEvidenceText
    true-feed-consumed

externalConstructionTheoremRow : ClosureRequirementRow
externalConstructionTheoremRow =
  mkClosureRequirementRow
    external-common-carrier-construction-theorem
    sprint118CommonCarrierConstructionReadinessPath
    Readiness118.commonCarrierConstructionTheoremProvedHere
    false
    refl
    true
    refl
    feedThroughClosureRowsComplete
    refl
    "External common-carrier construction theorem is required for feed-through closure and remains false in Sprint118 construction readiness."
    external-theorem-required

weakCompactnessCertificateRow : ClosureRequirementRow
weakCompactnessCertificateRow =
  mkClosureRequirementRow
    weak-compactness-certificate
    sprint119WeakCompactnessReducerPath
    weakCompactnessCertificateClosedHere
    false
    refl
    true
    refl
    feedThroughClosureRowsComplete
    refl
    "Weak compactness certificate is required before common-carrier feed-through closure can be promoted."
    compactness-certificate-required

moscoAggregateClosureRow : ClosureRequirementRow
moscoAggregateClosureRow =
  mkClosureRequirementRow
    mosco-aggregate-closure
    sprint119MoscoAggregateReducerPath
    moscoAggregateClosureClosedHere
    false
    refl
    true
    refl
    feedThroughClosureRowsComplete
    refl
    "Mosco aggregate closure is required before common-carrier feed-through closure can be promoted."
    aggregate-closure-required

transferCalculusAggregateClosureRow : ClosureRequirementRow
transferCalculusAggregateClosureRow =
  mkClosureRequirementRow
    transfer-calculus-aggregate-closure
    sprint119TransferCalculusAggregateReducerPath
    transferCalculusAggregateClosureClosedHere
    false
    refl
    true
    refl
    feedThroughClosureRowsComplete
    refl
    "Transfer-calculus aggregate closure is required before common-carrier feed-through closure can feed transfer lower-bound readiness."
    aggregate-closure-required

readinessPropagationRow : ClosureRequirementRow
readinessPropagationRow =
  mkClosureRequirementRow
    readiness-propagation
    sprint119UnlockAttemptPath
    readinessPropagationClosedHere
    false
    refl
    true
    refl
    feedThroughClosureRowsComplete
    refl
    "Readiness propagation from true criterion feeds and construction readiness is required and remains unclosed here."
    propagation-required

finalGovernanceBoundaryRow : ClosureRequirementRow
finalGovernanceBoundaryRow =
  mkClosureRequirementRow
    final-governance-boundary
    sprint119TransferReadinessUnlockReducerPath
    Transfer119.transferLowerBoundReadyHere
    false
    refl
    true
    refl
    feedThroughClosureRowsComplete
    refl
    falseBoundaryText
    fail-closed-boundary

canonicalClosureRequirementRows : List ClosureRequirementRow
canonicalClosureRequirementRows =
  normCriterionFeedRow
  ∷ residualCriterionFeedRow
  ∷ sectorCriterionFeedRow
  ∷ externalConstructionTheoremRow
  ∷ weakCompactnessCertificateRow
  ∷ moscoAggregateClosureRow
  ∷ transferCalculusAggregateClosureRow
  ∷ readinessPropagationRow
  ∷ finalGovernanceBoundaryRow
  ∷ []

canonicalUpstreamFlagLedger : UpstreamFlagLedger
canonicalUpstreamFlagLedger =
  mkUpstreamFlagLedger
    Feed118.normFeedClosedHere
    refl
    Feed118.residualFeedClosedHere
    refl
    Feed118.sectorFeedClosedHere
    refl
    Unlock119.commonCarrierFeedThroughClosedHere
    refl
    Transfer119.transferLowerBoundReadyHere
    refl
    Transfer119.transferLowerBoundTheoremProvedHere
    refl
    Transfer119.continuumMassGapProvedHere
    refl
    Transfer119.clayYangMillsPromoted
    refl

canonicalClosureReducerPackage : ClosureReducerPackage
canonicalClosureReducerPackage =
  mkClosureReducerPackage
    canonicalSourcePathLedger
    canonicalUpstreamReceipts
    canonicalUpstreamFlagLedger
    canonicalClosureRequirementRows
    reducerStatementText
    feedThroughClosureReducerRecorded
    refl
    feedThroughClosureRowsComplete
    refl
    commonCarrierFeedThroughClosedHere
    refl

canonicalTheoremBoundary : TheoremBoundary
canonicalTheoremBoundary =
  mkTheoremBoundary
    falseBoundaryText
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

canonicalFinalReceipt : FinalReceipt
canonicalFinalReceipt =
  mkFinalReceipt
    finalReceiptText
    canonicalClosureReducerPackage
    canonicalTheoremBoundary
    canonicalReceiptRecorded
    refl
    finalReceiptRecorded
    refl
    feedThroughClosureReducerRecorded
    refl
    feedThroughClosureRowsComplete
    refl
    commonCarrierFeedThroughClosedHere
    refl

canonicalSourcePathList : List String
canonicalSourcePathList =
  modulePath
  ∷ sprint119UnlockAttemptPath
  ∷ sprint119TransferReadinessUnlockReducerPath
  ∷ sprint118CriterionFeedAggregatorPath
  ∷ sprint118CommonCarrierConstructionReadinessPath
  ∷ sprint119WeakCompactnessReducerPath
  ∷ sprint119MoscoAggregateReducerPath
  ∷ sprint119TransferCalculusAggregateReducerPath
  ∷ []

canonicalEvidenceLedger : List String
canonicalEvidenceLedger =
  sourcePathLedgerText
  ∷ reducerStatementText
  ∷ falseBoundaryText
  ∷ canonicalReceiptText
  ∷ finalReceiptText
  ∷ Unlock119.finalReceiptText
  ∷ Transfer119.finalReceiptText
  ∷ Feed118.finalReceiptText
  ∷ Readiness118.finalReceiptText
  ∷ []

canonicalReceipt :
  YMSprint120CommonCarrierFeedThroughClosureReducerReceipt
canonicalReceipt =
  mkYMSprint120CommonCarrierFeedThroughClosureReducerReceipt
    sprintNumber
    modulePath
    canonicalClosureReducerPackage
    canonicalFinalReceipt
    canonicalSourcePathList
    canonicalEvidenceLedger
    feedThroughClosureReducerRecorded
    refl
    feedThroughClosureRowsComplete
    refl
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

finalReceipt : FinalReceipt
finalReceipt =
  canonicalFinalReceipt

canonicalFeedThroughClosureReducerRecordedIsTrue :
  feedThroughClosureReducerRecordedHere canonicalReceipt ≡ true
canonicalFeedThroughClosureReducerRecordedIsTrue =
  refl

canonicalFeedThroughClosureRowsCompleteIsTrue :
  feedThroughClosureRowsCompleteHere canonicalReceipt ≡ true
canonicalFeedThroughClosureRowsCompleteIsTrue =
  refl

canonicalCommonCarrierFeedThroughClosedHereIsFalse :
  commonCarrierFeedThroughClosedHereFlag canonicalReceipt ≡ false
canonicalCommonCarrierFeedThroughClosedHereIsFalse =
  refl

canonicalExternalCommonCarrierClosedHereIsFalse :
  externalCommonCarrierClosedHereFlag canonicalReceipt ≡ false
canonicalExternalCommonCarrierClosedHereIsFalse =
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
