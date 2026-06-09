module DASHI.Physics.Closure.YMSprint118CriterionFeedAggregator where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint117NormCriterionClosurePropagator
  as Norm117
import DASHI.Physics.Closure.YMSprint117ResidualCriterionClosurePropagator
  as Residual117
import DASHI.Physics.Closure.YMSprint117SectorCriterionClosurePropagator
  as Sector117
import DASHI.Physics.Closure.YMSprint117CommonCarrierFeedThroughPropagator
  as Common117

------------------------------------------------------------------------
-- Sprint118 criterion feed aggregator.
--
-- Sprint117 produced three true criterion-feed closure receipts: norm,
-- residual, and sector.  Sprint117 also produced a common-carrier
-- feed-through propagator receipt, but that receipt is intentionally
-- fail-closed for common-carrier feed-through, external common carrier,
-- transfer lower-bound readiness, transfer lower-bound theorem, continuum
-- mass gap, and Clay Yang-Mills promotion.  This Sprint118 module aggregates
-- the true Sprint117 criterion feeds into one typed feed package while
-- preserving every downstream theorem and promotion boundary as false.

sprintNumber : Nat
sprintNumber = 118

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint118CriterionFeedAggregator.agda"

sprint117NormSourcePath : String
sprint117NormSourcePath =
  Norm117.modulePath

sprint117ResidualSourcePath : String
sprint117ResidualSourcePath =
  Residual117.modulePath

sprint117SectorSourcePath : String
sprint117SectorSourcePath =
  Sector117.modulePath

sprint117CommonCarrierSourcePath : String
sprint117CommonCarrierSourcePath =
  Common117.modulePath

criterionFeedAggregatorRecorded : Bool
criterionFeedAggregatorRecorded = true

normFeedClosedHere : Bool
normFeedClosedHere =
  Norm117.normCriterionFeedClosedHere

residualFeedClosedHere : Bool
residualFeedClosedHere =
  Residual117.residualCriterionFeedClosedHere

sectorFeedClosedHere : Bool
sectorFeedClosedHere =
  Sector117.sectorCriterionFeedClosedHere

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

sourcePathLedgerText : String
sourcePathLedgerText =
  "Sprint118 source paths: canonical Sprint117 norm criterion closure propagator, residual criterion closure propagator, sector criterion closure propagator, and common-carrier feed-through propagator."

normFeedEvidenceText : String
normFeedEvidenceText =
  "Norm feed evidence: Sprint118 imports the canonical Sprint117 norm criterion receipt and reuses its normCriterionFeedClosedHere flag as the aggregated normFeedClosedHere flag."

residualFeedEvidenceText : String
residualFeedEvidenceText =
  "Residual feed evidence: Sprint118 imports the canonical Sprint117 residual criterion receipt and reuses its residualCriterionFeedClosedHere flag as the aggregated residualFeedClosedHere flag."

sectorFeedEvidenceText : String
sectorFeedEvidenceText =
  "Sector feed evidence: Sprint118 imports the canonical Sprint117 sector criterion receipt and reuses its sectorCriterionFeedClosedHere flag as the aggregated sectorFeedClosedHere flag."

commonCarrierBoundaryText : String
commonCarrierBoundaryText =
  "Common-carrier boundary: Sprint118 carries the typed Sprint117 common-carrier feed-through propagator receipt only as a fail-closed dependency; common-carrier feed-through and external common-carrier closure remain false."

transferBoundaryText : String
transferBoundaryText =
  "Transfer boundary: Sprint118 aggregation does not make transfer lower-bound readiness true, does not prove a transfer lower-bound theorem, and does not prove a continuum mass gap."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Non-promotion boundary: Sprint118 aggregates criterion feed receipts only; Clay Yang-Mills promotion remains false."

finalReceiptText : String
finalReceiptText =
  "Final Sprint118 receipt: normFeedClosedHere=true, residualFeedClosedHere=true, and sectorFeedClosedHere=true are aggregated from Sprint117 typed receipts, while common-carrier, transfer, continuum mass-gap, and Clay promotion gates remain false."

data AggregatorLane : Set where
  source-path-lane :
    AggregatorLane
  norm-feed-lane :
    AggregatorLane
  residual-feed-lane :
    AggregatorLane
  sector-feed-lane :
    AggregatorLane
  common-carrier-boundary-lane :
    AggregatorLane
  transfer-boundary-lane :
    AggregatorLane
  nonpromotion-boundary-lane :
    AggregatorLane
  receipt-lane :
    AggregatorLane

data AggregatorStatus : Set where
  source-paths-recorded :
    AggregatorStatus
  sprint117-norm-feed-imported :
    AggregatorStatus
  sprint117-residual-feed-imported :
    AggregatorStatus
  sprint117-sector-feed-imported :
    AggregatorStatus
  sprint117-common-carrier-boundary-imported :
    AggregatorStatus
  criterion-feed-package-aggregated :
    AggregatorStatus
  theorem-boundary-fail-closed :
    AggregatorStatus
  final-receipt-recorded :
    AggregatorStatus

canonicalAggregatorLanes : List AggregatorLane
canonicalAggregatorLanes =
  source-path-lane
  ∷ norm-feed-lane
  ∷ residual-feed-lane
  ∷ sector-feed-lane
  ∷ common-carrier-boundary-lane
  ∷ transfer-boundary-lane
  ∷ nonpromotion-boundary-lane
  ∷ receipt-lane
  ∷ []

record SourcePathLedger : Set where
  constructor mkSourcePathLedger
  field
    currentModulePath :
      String
    normSourcePath :
      String
    residualSourcePath :
      String
    sectorSourcePath :
      String
    commonCarrierSourcePath :
      String
    statement :
      String
    ledgerRecorded :
      Bool
    ledgerRecordedIsTrue :
      ledgerRecorded ≡ true
    status :
      AggregatorStatus

record Sprint117FeedReceipts : Setω where
  constructor mkSprint117FeedReceipts
  field
    normReceipt :
      Norm117.YMSprint117NormCriterionClosurePropagatorReceipt
    residualReceipt :
      Residual117.YMSprint117ResidualCriterionClosurePropagatorReceipt
    sectorReceipt :
      Sector117.YMSprint117SectorCriterionClosurePropagatorReceipt
    commonCarrierReceipt :
      Common117.YMSprint117CommonCarrierFeedThroughPropagatorReceipt
    normReceiptFeedClosed :
      Bool
    normReceiptFeedClosedIsTrue :
      normReceiptFeedClosed ≡ true
    residualReceiptFeedClosed :
      Bool
    residualReceiptFeedClosedIsTrue :
      residualReceiptFeedClosed ≡ true
    sectorReceiptFeedClosed :
      Bool
    sectorReceiptFeedClosedIsTrue :
      sectorReceiptFeedClosed ≡ true
    commonCarrierReceiptFeedThroughClosed :
      Bool
    commonCarrierReceiptFeedThroughClosedIsFalse :
      commonCarrierReceiptFeedThroughClosed ≡ false
    commonCarrierReceiptExternalClosed :
      Bool
    commonCarrierReceiptExternalClosedIsFalse :
      commonCarrierReceiptExternalClosed ≡ false
    commonCarrierReceiptTransferReady :
      Bool
    commonCarrierReceiptTransferReadyIsFalse :
      commonCarrierReceiptTransferReady ≡ false
    commonCarrierReceiptClayPromoted :
      Bool
    commonCarrierReceiptClayPromotedIsFalse :
      commonCarrierReceiptClayPromoted ≡ false

record CriterionFeedPackage : Setω where
  constructor mkCriterionFeedPackage
  field
    sourceReceipts :
      Sprint117FeedReceipts
    normStatement :
      String
    residualStatement :
      String
    sectorStatement :
      String
    normFeedClosed :
      Bool
    normFeedClosedIsTrue :
      normFeedClosed ≡ true
    normFeedEqualsSprint117Flag :
      normFeedClosed ≡ Norm117.normCriterionFeedClosedHere
    residualFeedClosed :
      Bool
    residualFeedClosedIsTrue :
      residualFeedClosed ≡ true
    residualFeedEqualsSprint117Flag :
      residualFeedClosed ≡ Residual117.residualCriterionFeedClosedHere
    sectorFeedClosed :
      Bool
    sectorFeedClosedIsTrue :
      sectorFeedClosed ≡ true
    sectorFeedEqualsSprint117Flag :
      sectorFeedClosed ≡ Sector117.sectorCriterionFeedClosedHere
    aggregationRecorded :
      Bool
    aggregationRecordedIsTrue :
      aggregationRecorded ≡ true
    status :
      AggregatorStatus

record TheoremBoundary : Setω where
  constructor mkTheoremBoundary
  field
    statement :
      String
    commonCarrierStatement :
      String
    transferStatement :
      String
    nonPromotionStatement :
      String
    commonCarrierReceipt :
      Common117.YMSprint117CommonCarrierFeedThroughPropagatorReceipt
    commonCarrierFeedThroughClosedFlag :
      Bool
    commonCarrierFeedThroughClosedIsFalse :
      commonCarrierFeedThroughClosedFlag ≡ false
    commonCarrierFeedThroughEqualsSprint117Flag :
      commonCarrierFeedThroughClosedFlag ≡
      Common117.commonCarrierFeedThroughClosedHere
    externalCommonCarrierClosedFlag :
      Bool
    externalCommonCarrierClosedIsFalse :
      externalCommonCarrierClosedFlag ≡ false
    externalCommonCarrierEqualsSprint117Flag :
      externalCommonCarrierClosedFlag ≡
      Common117.externalCommonCarrierClosedHere
    transferLowerBoundReadyFlag :
      Bool
    transferLowerBoundReadyIsFalse :
      transferLowerBoundReadyFlag ≡ false
    transferLowerBoundReadyEqualsSprint117Flag :
      transferLowerBoundReadyFlag ≡ Common117.transferLowerBoundReadyHere
    transferLowerBoundTheoremProvedFlag :
      Bool
    transferLowerBoundTheoremProvedIsFalse :
      transferLowerBoundTheoremProvedFlag ≡ false
    transferLowerBoundTheoremEqualsSprint117Flag :
      transferLowerBoundTheoremProvedFlag ≡
      Common117.transferLowerBoundTheoremProvedHere
    continuumMassGapProvedFlag :
      Bool
    continuumMassGapProvedIsFalse :
      continuumMassGapProvedFlag ≡ false
    continuumMassGapEqualsSprint117Flag :
      continuumMassGapProvedFlag ≡ Common117.continuumMassGapProvedHere
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    clayYangMillsEqualsSprint117Flag :
      clayYangMillsPromotedHere ≡ Common117.clayYangMillsPromoted
    status :
      AggregatorStatus

record FinalReceipt : Setω where
  constructor mkFinalReceipt
  field
    statement :
      String
    package :
      CriterionFeedPackage
    theoremBoundary :
      TheoremBoundary
    aggregatorRecorded :
      Bool
    aggregatorRecordedIsTrue :
      aggregatorRecorded ≡ true
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
    status :
      AggregatorStatus

record YMSprint118CriterionFeedAggregatorReceipt : Setω where
  constructor mkYMSprint118CriterionFeedAggregatorReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    sourcePaths :
      SourcePathLedger
    sourceReceipts :
      Sprint117FeedReceipts
    criterionFeedPackage :
      CriterionFeedPackage
    theoremBoundary :
      TheoremBoundary
    finalReceiptField :
      FinalReceipt
    lanes :
      List AggregatorLane
    sourcePathList :
      List String
    evidenceLedger :
      List String
    receiptRecorded :
      Bool
    receiptRecordedIsTrue :
      receiptRecorded ≡ true
    normFeedClosedHereFlag :
      Bool
    normFeedClosedHereFlagIsTrue :
      normFeedClosedHereFlag ≡ true
    residualFeedClosedHereFlag :
      Bool
    residualFeedClosedHereFlagIsTrue :
      residualFeedClosedHereFlag ≡ true
    sectorFeedClosedHereFlag :
      Bool
    sectorFeedClosedHereFlagIsTrue :
      sectorFeedClosedHereFlag ≡ true
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
open Sprint117FeedReceipts public
open CriterionFeedPackage public
open TheoremBoundary public
open FinalReceipt public
open YMSprint118CriterionFeedAggregatorReceipt public

canonicalSourcePathLedger : SourcePathLedger
canonicalSourcePathLedger =
  mkSourcePathLedger
    modulePath
    sprint117NormSourcePath
    sprint117ResidualSourcePath
    sprint117SectorSourcePath
    sprint117CommonCarrierSourcePath
    sourcePathLedgerText
    criterionFeedAggregatorRecorded
    refl
    source-paths-recorded

canonicalSprint117FeedReceipts : Sprint117FeedReceipts
canonicalSprint117FeedReceipts =
  mkSprint117FeedReceipts
    Norm117.canonicalReceipt
    Residual117.canonicalReceipt
    Sector117.canonicalReceipt
    Common117.canonicalReceipt
    (Norm117.normCriterionFeedClosedHereFlag Norm117.canonicalReceipt)
    Norm117.canonicalNormCriterionFeedClosedHere
    (Residual117.residualCriterionFeedClosedHereFlag
      Residual117.canonicalReceipt)
    Residual117.canonicalResidualCriterionFeedClosedHereIsTrue
    (Sector117.sectorCriterionFeedClosed Sector117.canonicalReceipt)
    Sector117.canonicalSectorCriterionFeedClosedIsTrue
    Common117.commonCarrierFeedThroughClosedHere
    Common117.canonicalCommonCarrierFeedThroughClosedHereIsFalse
    Common117.externalCommonCarrierClosedHere
    Common117.canonicalExternalCommonCarrierClosedHereIsFalse
    Common117.transferLowerBoundReadyHere
    Common117.canonicalTransferLowerBoundReadyHereIsFalse
    (Common117.clayYangMillsPromotedHere Common117.canonicalReceipt)
    Common117.canonicalClayYangMillsPromotedIsFalse

canonicalCriterionFeedPackage : CriterionFeedPackage
canonicalCriterionFeedPackage =
  mkCriterionFeedPackage
    canonicalSprint117FeedReceipts
    normFeedEvidenceText
    residualFeedEvidenceText
    sectorFeedEvidenceText
    normFeedClosedHere
    refl
    refl
    residualFeedClosedHere
    refl
    refl
    sectorFeedClosedHere
    refl
    refl
    criterionFeedAggregatorRecorded
    refl
    criterion-feed-package-aggregated

canonicalTheoremBoundary : TheoremBoundary
canonicalTheoremBoundary =
  mkTheoremBoundary
    nonPromotionBoundaryText
    commonCarrierBoundaryText
    transferBoundaryText
    nonPromotionBoundaryText
    Common117.canonicalReceipt
    commonCarrierFeedThroughClosedHere
    refl
    refl
    externalCommonCarrierClosedHere
    refl
    refl
    transferLowerBoundReadyHere
    refl
    refl
    transferLowerBoundTheoremProvedHere
    refl
    refl
    continuumMassGapProvedHere
    refl
    refl
    clayYangMillsPromoted
    refl
    refl
    theorem-boundary-fail-closed

canonicalFinalReceipt : FinalReceipt
canonicalFinalReceipt =
  mkFinalReceipt
    finalReceiptText
    canonicalCriterionFeedPackage
    canonicalTheoremBoundary
    criterionFeedAggregatorRecorded
    refl
    normFeedClosedHere
    refl
    residualFeedClosedHere
    refl
    sectorFeedClosedHere
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
    final-receipt-recorded

canonicalSourcePathList : List String
canonicalSourcePathList =
  modulePath
  ∷ sprint117NormSourcePath
  ∷ sprint117ResidualSourcePath
  ∷ sprint117SectorSourcePath
  ∷ sprint117CommonCarrierSourcePath
  ∷ []

canonicalEvidenceLedger : List String
canonicalEvidenceLedger =
  sourcePathLedgerText
  ∷ normFeedEvidenceText
  ∷ residualFeedEvidenceText
  ∷ sectorFeedEvidenceText
  ∷ commonCarrierBoundaryText
  ∷ transferBoundaryText
  ∷ nonPromotionBoundaryText
  ∷ finalReceiptText
  ∷ Norm117.propagatorStatementText
  ∷ Residual117.propagationStatementText
  ∷ Sector117.propagatorStatementText
  ∷ Common117.finalReceiptText
  ∷ []

canonicalYMSprint118CriterionFeedAggregatorReceipt :
  YMSprint118CriterionFeedAggregatorReceipt
canonicalYMSprint118CriterionFeedAggregatorReceipt =
  mkYMSprint118CriterionFeedAggregatorReceipt
    sprintNumber
    modulePath
    canonicalSourcePathLedger
    canonicalSprint117FeedReceipts
    canonicalCriterionFeedPackage
    canonicalTheoremBoundary
    canonicalFinalReceipt
    canonicalAggregatorLanes
    canonicalSourcePathList
    canonicalEvidenceLedger
    criterionFeedAggregatorRecorded
    refl
    normFeedClosedHere
    refl
    residualFeedClosedHere
    refl
    sectorFeedClosedHere
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

canonicalReceipt : YMSprint118CriterionFeedAggregatorReceipt
canonicalReceipt =
  canonicalYMSprint118CriterionFeedAggregatorReceipt

finalReceipt : FinalReceipt
finalReceipt =
  canonicalFinalReceipt

canonicalNormFeedClosedHereIsTrue :
  normFeedClosedHereFlag canonicalReceipt ≡ true
canonicalNormFeedClosedHereIsTrue =
  refl

canonicalNormFeedEqualsSprint117NormCriterionFeed :
  normFeedClosedHereFlag canonicalReceipt ≡
  Norm117.normCriterionFeedClosedHere
canonicalNormFeedEqualsSprint117NormCriterionFeed =
  refl

canonicalResidualFeedClosedHereIsTrue :
  residualFeedClosedHereFlag canonicalReceipt ≡ true
canonicalResidualFeedClosedHereIsTrue =
  refl

canonicalResidualFeedEqualsSprint117ResidualCriterionFeed :
  residualFeedClosedHereFlag canonicalReceipt ≡
  Residual117.residualCriterionFeedClosedHere
canonicalResidualFeedEqualsSprint117ResidualCriterionFeed =
  refl

canonicalSectorFeedClosedHereIsTrue :
  sectorFeedClosedHereFlag canonicalReceipt ≡ true
canonicalSectorFeedClosedHereIsTrue =
  refl

canonicalSectorFeedEqualsSprint117SectorCriterionFeed :
  sectorFeedClosedHereFlag canonicalReceipt ≡
  Sector117.sectorCriterionFeedClosedHere
canonicalSectorFeedEqualsSprint117SectorCriterionFeed =
  refl

canonicalCommonCarrierFeedThroughClosedHereIsFalse :
  commonCarrierFeedThroughClosedHereFlag canonicalReceipt ≡ false
canonicalCommonCarrierFeedThroughClosedHereIsFalse =
  refl

canonicalCommonCarrierFeedThroughEqualsSprint117Boundary :
  commonCarrierFeedThroughClosedHereFlag canonicalReceipt ≡
  Common117.commonCarrierFeedThroughClosedHere
canonicalCommonCarrierFeedThroughEqualsSprint117Boundary =
  refl

canonicalExternalCommonCarrierClosedHereIsFalse :
  externalCommonCarrierClosedHereFlag canonicalReceipt ≡ false
canonicalExternalCommonCarrierClosedHereIsFalse =
  refl

canonicalExternalCommonCarrierEqualsSprint117Boundary :
  externalCommonCarrierClosedHereFlag canonicalReceipt ≡
  Common117.externalCommonCarrierClosedHere
canonicalExternalCommonCarrierEqualsSprint117Boundary =
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

canonicalFinalReceiptNormFeedClosed :
  FinalReceipt.normFeedClosed finalReceipt ≡ true
canonicalFinalReceiptNormFeedClosed =
  refl

canonicalFinalReceiptResidualFeedClosed :
  FinalReceipt.residualFeedClosed finalReceipt ≡ true
canonicalFinalReceiptResidualFeedClosed =
  refl

canonicalFinalReceiptSectorFeedClosed :
  FinalReceipt.sectorFeedClosed finalReceipt ≡ true
canonicalFinalReceiptSectorFeedClosed =
  refl

canonicalFinalReceiptClayYangMillsPromotedIsFalse :
  FinalReceipt.clayYangMillsPromotedHere finalReceipt ≡ false
canonicalFinalReceiptClayYangMillsPromotedIsFalse =
  refl
