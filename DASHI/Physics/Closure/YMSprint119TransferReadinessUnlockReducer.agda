module DASHI.Physics.Closure.YMSprint119TransferReadinessUnlockReducer where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint118TransferBlockerMatrix
  as Matrix118
import DASHI.Physics.Closure.YMSprint118CriterionFeedAggregator
  as Feed118
import DASHI.Physics.Closure.YMSprint118MoscoCompactnessReadinessAggregator
  as Mosco118
import DASHI.Physics.Closure.YMSprint118TransferCalculusReadinessAggregator
  as Calculus118
import DASHI.Physics.Closure.YMSprint118CommonCarrierConstructionReadiness
  as Carrier118

------------------------------------------------------------------------
-- Sprint119 transfer-readiness unlock reducer.
--
-- This module reduces the Sprint118 transfer-readiness surface to the exact
-- unlock inputs required before a transfer lower-bound route may be reopened.
-- It imports only canonical Sprint118 receipts and records Sprint119 sibling
-- work as String evidence paths.  The reducer, package, and rows are recorded
-- here, while transfer readiness, transfer theorem, continuum mass gap, and
-- Clay Yang-Mills promotion remain fail-closed.

sprintNumber : Nat
sprintNumber = 119

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint119TransferReadinessUnlockReducer.agda"

reducerRecorded : Bool
reducerRecorded = true

unlockPackageAssembledHere : Bool
unlockPackageAssembledHere = true

unlockRowsRecordedHere : Bool
unlockRowsRecordedHere = true

transferLowerBoundReadyHere : Bool
transferLowerBoundReadyHere = false

transferLowerBoundTheoremProvedHere : Bool
transferLowerBoundTheoremProvedHere = false

continuumMassGapProvedHere : Bool
continuumMassGapProvedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

sprint118MatrixSourcePath : String
sprint118MatrixSourcePath =
  Matrix118.modulePath

sprint118CriterionFeedSourcePath : String
sprint118CriterionFeedSourcePath =
  Feed118.modulePath

sprint118MoscoCompactnessSourcePath : String
sprint118MoscoCompactnessSourcePath =
  Mosco118.modulePath

sprint118TransferCalculusSourcePath : String
sprint118TransferCalculusSourcePath =
  Calculus118.modulePath

sprint118CommonCarrierConstructionSourcePath : String
sprint118CommonCarrierConstructionSourcePath =
  Carrier118.modulePath

sprint119CommonCarrierFeedThroughPath : String
sprint119CommonCarrierFeedThroughPath =
  "DASHI/Physics/Closure/YMSprint119CommonCarrierFeedThroughUnlock.agda"

sprint119ExternalCarrierConstructionPath : String
sprint119ExternalCarrierConstructionPath =
  "DASHI/Physics/Closure/YMSprint119ExternalCommonCarrierConstructionUnlock.agda"

sprint119WeakCompactnessPath : String
sprint119WeakCompactnessPath =
  "DASHI/Physics/Closure/YMSprint119WeakCompactnessUnlock.agda"

sprint119MoscoCompactnessPath : String
sprint119MoscoCompactnessPath =
  "DASHI/Physics/Closure/YMSprint119MoscoCompactnessObligationUnlock.agda"

sprint119TransferCalculusPath : String
sprint119TransferCalculusPath =
  "DASHI/Physics/Closure/YMSprint119TransferCalculusObligationUnlock.agda"

unlockReducerStatementText : String
unlockReducerStatementText =
  "Sprint119 transfer lower-bound readiness is unlocked only by common-carrier feed-through closure, external common-carrier construction closure, weak compactness closure, all Mosco compactness obligations closed, and all transfer-calculus obligations closed."

upstreamBoundaryText : String
upstreamBoundaryText =
  "Sprint119 imports canonical Sprint118 readiness receipts; every upstream input required by the unlock reducer is still false in those receipts and is therefore recorded as an external discharge requirement."

governanceBoundaryText : String
governanceBoundaryText =
  "Governance boundary: this reducer records the readiness unlock conditions only and does not prove a transfer lower-bound theorem, continuum mass gap, or Clay Yang-Mills promotion."

canonicalReceiptText : String
canonicalReceiptText =
  "Canonical Sprint119 receipt: reducer recorded, package assembled, rows recorded, source paths and upstream flags captured, unlock remains fail-closed."

finalReceiptText : String
finalReceiptText =
  "Final Sprint119 receipt: transferLowerBoundReadyHere=false until all five required unlock inputs are supplied by external closing modules and promoted through governance."

data UnlockInput : Set where
  common-carrier-feed-through :
    UnlockInput
  external-common-carrier-construction :
    UnlockInput
  weak-compactness :
    UnlockInput
  all-mosco-compactness-obligations :
    UnlockInput
  all-transfer-calculus-obligations :
    UnlockInput
  final-governance-boundary :
    UnlockInput

data UnlockStatus : Set where
  sprint118-source-imported :
    UnlockStatus
  upstream-flag-recorded :
    UnlockStatus
  external-discharge-required :
    UnlockStatus
  unlock-row-recorded :
    UnlockStatus
  package-assembled :
    UnlockStatus
  readiness-fail-closed :
    UnlockStatus
  theorem-boundary-fail-closed :
    UnlockStatus
  canonical-receipt-recorded :
    UnlockStatus
  final-receipt-recorded :
    UnlockStatus

record UpstreamSprint118Receipts : Setω where
  constructor mkUpstreamSprint118Receipts
  field
    matrixReceipt :
      Matrix118.TransferBlockerMatrixReceipt
    criterionFeedReceipt :
      Feed118.YMSprint118CriterionFeedAggregatorReceipt
    moscoCompactnessReceipt :
      Mosco118.YMSprint118MoscoCompactnessReadinessAggregatorReceipt
    transferCalculusReceipt :
      Calculus118.YMSprint118TransferCalculusReadinessAggregatorReceipt
    commonCarrierConstructionReceipt :
      Carrier118.YMSprint118CommonCarrierConstructionReadinessReceipt
    matrixPath :
      String
    criterionFeedPath :
      String
    moscoCompactnessPath :
      String
    transferCalculusPath :
      String
    commonCarrierConstructionPath :
      String
    receiptsImported :
      Bool
    receiptsImportedIsTrue :
      receiptsImported ≡ true

record UpstreamUnlockFlags : Set where
  constructor mkUpstreamUnlockFlags
  field
    commonCarrierFeedThroughClosed :
      Bool
    commonCarrierFeedThroughClosedIsFalse :
      commonCarrierFeedThroughClosed ≡ false
    externalCommonCarrierConstructionClosed :
      Bool
    externalCommonCarrierConstructionClosedIsFalse :
      externalCommonCarrierConstructionClosed ≡ false
    weakCompactnessClosed :
      Bool
    weakCompactnessClosedIsFalse :
      weakCompactnessClosed ≡ false
    allMoscoCompactnessObligationsClosed :
      Bool
    allMoscoCompactnessObligationsClosedIsFalse :
      allMoscoCompactnessObligationsClosed ≡ false
    allTransferCalculusObligationsClosed :
      Bool
    allTransferCalculusObligationsClosedIsFalse :
      allTransferCalculusObligationsClosed ≡ false
    transferLowerBoundReadyInput :
      Bool
    transferLowerBoundReadyInputIsFalse :
      transferLowerBoundReadyInput ≡ false

record UnlockRow : Set where
  constructor mkUnlockRow
  field
    input :
      UnlockInput
    upstreamSourcePath :
      String
    sprint119EvidencePath :
      String
    upstreamClosedFlag :
      Bool
    upstreamClosedFlagIsFalse :
      upstreamClosedFlag ≡ false
    requiredForTransferLowerBoundReady :
      Bool
    requiredForTransferLowerBoundReadyIsTrue :
      requiredForTransferLowerBoundReady ≡ true
    rowRecorded :
      Bool
    rowRecordedIsTrue :
      rowRecorded ≡ true
    status :
      UnlockStatus
    evidenceText :
      String

record TransferReadinessRequirement : Set where
  constructor mkTransferReadinessRequirement
  field
    commonCarrierFeedThroughClosed :
      Bool
    commonCarrierFeedThroughClosedIsFalse :
      commonCarrierFeedThroughClosed ≡ false
    externalCommonCarrierConstructionClosed :
      Bool
    externalCommonCarrierConstructionClosedIsFalse :
      externalCommonCarrierConstructionClosed ≡ false
    weakCompactnessClosed :
      Bool
    weakCompactnessClosedIsFalse :
      weakCompactnessClosed ≡ false
    allMoscoCompactnessObligationsClosed :
      Bool
    allMoscoCompactnessObligationsClosedIsFalse :
      allMoscoCompactnessObligationsClosed ≡ false
    allTransferCalculusObligationsClosed :
      Bool
    allTransferCalculusObligationsClosedIsFalse :
      allTransferCalculusObligationsClosed ≡ false
    transferLowerBoundReady :
      Bool
    transferLowerBoundReadyIsFalse :
      transferLowerBoundReady ≡ false
    requirementStatement :
      String
    status :
      UnlockStatus

record GovernanceBoundary : Set where
  constructor mkGovernanceBoundary
  field
    boundaryText :
      String
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

record UnlockPackage : Setω where
  constructor mkUnlockPackage
  field
    upstreamReceipts :
      UpstreamSprint118Receipts
    upstreamFlags :
      UpstreamUnlockFlags
    requirement :
      TransferReadinessRequirement
    rows :
      List UnlockRow
    rowCount :
      Nat
    reducerRecordedHere :
      Bool
    reducerRecordedHereIsTrue :
      reducerRecordedHere ≡ true
    packageAssembledHere :
      Bool
    packageAssembledHereIsTrue :
      packageAssembledHere ≡ true
    rowsRecordedHere :
      Bool
    rowsRecordedHereIsTrue :
      rowsRecordedHere ≡ true
    sourcePaths :
      List String
    evidenceLedger :
      List String
    status :
      UnlockStatus

record CanonicalReceipt : Setω where
  constructor mkCanonicalReceipt
  field
    receiptText :
      String
    package :
      UnlockPackage
    governanceBoundary :
      GovernanceBoundary
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
    status :
      UnlockStatus

record FinalReceipt : Setω where
  constructor mkFinalReceipt
  field
    receiptText :
      String
    canonicalReceipt :
      CanonicalReceipt
    finalReceiptRecordedHere :
      Bool
    finalReceiptRecordedHereIsTrue :
      finalReceiptRecordedHere ≡ true
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
    status :
      UnlockStatus

record YMSprint119TransferReadinessUnlockReducerReceipt : Setω where
  constructor mkYMSprint119TransferReadinessUnlockReducerReceipt
  field
    currentModulePath :
      String
    reducerPackage :
      UnlockPackage
    canonicalReducerReceipt :
      CanonicalReceipt
    finalReducerReceipt :
      FinalReceipt
    reducerRecordedHere :
      Bool
    reducerRecordedHereIsTrue :
      reducerRecordedHere ≡ true
    packageAssembledHere :
      Bool
    packageAssembledHereIsTrue :
      packageAssembledHere ≡ true
    rowsRecordedHere :
      Bool
    rowsRecordedHereIsTrue :
      rowsRecordedHere ≡ true
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

open UpstreamSprint118Receipts public
open UpstreamUnlockFlags public
open UnlockRow public
open TransferReadinessRequirement public
open GovernanceBoundary public
open UnlockPackage public
open CanonicalReceipt public
open YMSprint119TransferReadinessUnlockReducerReceipt public

canonicalUpstreamSprint118Receipts : UpstreamSprint118Receipts
canonicalUpstreamSprint118Receipts =
  mkUpstreamSprint118Receipts
    Matrix118.canonicalReceipt
    Feed118.canonicalReceipt
    Mosco118.canonicalReceipt
    Calculus118.canonicalReceipt
    Carrier118.canonicalReceipt
    sprint118MatrixSourcePath
    sprint118CriterionFeedSourcePath
    sprint118MoscoCompactnessSourcePath
    sprint118TransferCalculusSourcePath
    sprint118CommonCarrierConstructionSourcePath
    true
    refl

canonicalUpstreamUnlockFlags : UpstreamUnlockFlags
canonicalUpstreamUnlockFlags =
  mkUpstreamUnlockFlags
    Carrier118.commonCarrierFeedThroughClosedHere
    Carrier118.canonicalCommonCarrierFeedThroughClosedHereIsFalse
    Carrier118.externalCommonCarrierConstructionClosedHere
    Carrier118.canonicalExternalCommonCarrierConstructionClosedHereIsFalse
    Mosco118.weakCompactnessClosedHere
    Mosco118.canonicalReceiptWeakCompactnessClosedHereIsFalse
    Mosco118.allMoscoCompactnessObligationsClosedHere
    refl
    Calculus118.allTransferCalculusObligationsClosedHere
    refl
    Matrix118.transferLowerBoundReadyHere
    Matrix118.canonicalReceiptTransferLowerBoundReadyHereIsFalse

commonCarrierFeedThroughRow : UnlockRow
commonCarrierFeedThroughRow =
  mkUnlockRow
    common-carrier-feed-through
    sprint118CommonCarrierConstructionSourcePath
    sprint119CommonCarrierFeedThroughPath
    Carrier118.commonCarrierFeedThroughClosedHere
    Carrier118.canonicalCommonCarrierFeedThroughClosedHereIsFalse
    true
    refl
    true
    refl
    external-discharge-required
    "Common-carrier feed-through closure is a required unlock input and remains false in the Sprint118 construction-readiness receipt."

externalCarrierConstructionRow : UnlockRow
externalCarrierConstructionRow =
  mkUnlockRow
    external-common-carrier-construction
    sprint118CommonCarrierConstructionSourcePath
    sprint119ExternalCarrierConstructionPath
    Carrier118.externalCommonCarrierConstructionClosedHere
    Carrier118.canonicalExternalCommonCarrierConstructionClosedHereIsFalse
    true
    refl
    true
    refl
    external-discharge-required
    "External common-carrier construction closure is a required unlock input and remains false in the Sprint118 construction-readiness receipt."

weakCompactnessRow : UnlockRow
weakCompactnessRow =
  mkUnlockRow
    weak-compactness
    sprint118MoscoCompactnessSourcePath
    sprint119WeakCompactnessPath
    Mosco118.weakCompactnessClosedHere
    Mosco118.canonicalReceiptWeakCompactnessClosedHereIsFalse
    true
    refl
    true
    refl
    external-discharge-required
    "Weak compactness closure is a required unlock input and remains false in the Sprint118 Mosco compactness-readiness receipt."

moscoCompactnessRow : UnlockRow
moscoCompactnessRow =
  mkUnlockRow
    all-mosco-compactness-obligations
    sprint118MoscoCompactnessSourcePath
    sprint119MoscoCompactnessPath
    Mosco118.allMoscoCompactnessObligationsClosedHere
    refl
    true
    refl
    true
    refl
    external-discharge-required
    "All Mosco compactness obligations must be closed before readiness can unlock; the Sprint118 aggregate flag remains false."

transferCalculusRow : UnlockRow
transferCalculusRow =
  mkUnlockRow
    all-transfer-calculus-obligations
    sprint118TransferCalculusSourcePath
    sprint119TransferCalculusPath
    Calculus118.allTransferCalculusObligationsClosedHere
    refl
    true
    refl
    true
    refl
    external-discharge-required
    "All transfer-calculus obligations must be closed before readiness can unlock; the Sprint118 aggregate flag remains false."

governanceBoundaryRow : UnlockRow
governanceBoundaryRow =
  mkUnlockRow
    final-governance-boundary
    sprint118MatrixSourcePath
    "DASHI/Physics/Closure/YMSprint119ClayGovernancePromotionBoundary.agda"
    Matrix118.transferLowerBoundReadyHere
    Matrix118.canonicalReceiptTransferLowerBoundReadyHereIsFalse
    true
    refl
    true
    refl
    theorem-boundary-fail-closed
    governanceBoundaryText

canonicalUnlockRows : List UnlockRow
canonicalUnlockRows =
  commonCarrierFeedThroughRow
  ∷ externalCarrierConstructionRow
  ∷ weakCompactnessRow
  ∷ moscoCompactnessRow
  ∷ transferCalculusRow
  ∷ governanceBoundaryRow
  ∷ []

canonicalTransferReadinessRequirement : TransferReadinessRequirement
canonicalTransferReadinessRequirement =
  mkTransferReadinessRequirement
    Carrier118.commonCarrierFeedThroughClosedHere
    Carrier118.canonicalCommonCarrierFeedThroughClosedHereIsFalse
    Carrier118.externalCommonCarrierConstructionClosedHere
    Carrier118.canonicalExternalCommonCarrierConstructionClosedHereIsFalse
    Mosco118.weakCompactnessClosedHere
    Mosco118.canonicalReceiptWeakCompactnessClosedHereIsFalse
    Mosco118.allMoscoCompactnessObligationsClosedHere
    refl
    Calculus118.allTransferCalculusObligationsClosedHere
    refl
    transferLowerBoundReadyHere
    refl
    unlockReducerStatementText
    readiness-fail-closed

canonicalGovernanceBoundary : GovernanceBoundary
canonicalGovernanceBoundary =
  mkGovernanceBoundary
    governanceBoundaryText
    transferLowerBoundReadyHere
    refl
    transferLowerBoundTheoremProvedHere
    refl
    continuumMassGapProvedHere
    refl
    clayYangMillsPromoted
    refl
    theorem-boundary-fail-closed

canonicalSourcePaths : List String
canonicalSourcePaths =
  sprint118MatrixSourcePath
  ∷ sprint118CriterionFeedSourcePath
  ∷ sprint118MoscoCompactnessSourcePath
  ∷ sprint118TransferCalculusSourcePath
  ∷ sprint118CommonCarrierConstructionSourcePath
  ∷ sprint119CommonCarrierFeedThroughPath
  ∷ sprint119ExternalCarrierConstructionPath
  ∷ sprint119WeakCompactnessPath
  ∷ sprint119MoscoCompactnessPath
  ∷ sprint119TransferCalculusPath
  ∷ []

canonicalEvidenceLedger : List String
canonicalEvidenceLedger =
  unlockReducerStatementText
  ∷ upstreamBoundaryText
  ∷ governanceBoundaryText
  ∷ canonicalReceiptText
  ∷ finalReceiptText
  ∷ Matrix118.matrixSummaryText
  ∷ Feed118.finalReceiptText
  ∷ Mosco118.nonPromotionBoundaryText
  ∷ Calculus118.failClosedBoundaryText
  ∷ Carrier118.finalReceiptText
  ∷ []

canonicalUnlockPackage : UnlockPackage
canonicalUnlockPackage =
  mkUnlockPackage
    canonicalUpstreamSprint118Receipts
    canonicalUpstreamUnlockFlags
    canonicalTransferReadinessRequirement
    canonicalUnlockRows
    6
    reducerRecorded
    refl
    unlockPackageAssembledHere
    refl
    unlockRowsRecordedHere
    refl
    canonicalSourcePaths
    canonicalEvidenceLedger
    package-assembled

canonicalReducerReceiptValue : CanonicalReceipt
canonicalReducerReceiptValue =
  mkCanonicalReceipt
    canonicalReceiptText
    canonicalUnlockPackage
    canonicalGovernanceBoundary
    transferLowerBoundReadyHere
    refl
    transferLowerBoundTheoremProvedHere
    refl
    continuumMassGapProvedHere
    refl
    clayYangMillsPromoted
    refl
    canonical-receipt-recorded

finalReducerReceiptValue : FinalReceipt
finalReducerReceiptValue =
  mkFinalReceipt
    finalReceiptText
    canonicalReducerReceiptValue
    true
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

canonicalReceipt :
  YMSprint119TransferReadinessUnlockReducerReceipt
canonicalReceipt =
  mkYMSprint119TransferReadinessUnlockReducerReceipt
    modulePath
    canonicalUnlockPackage
    canonicalReducerReceiptValue
    finalReducerReceiptValue
    reducerRecorded
    refl
    unlockPackageAssembledHere
    refl
    unlockRowsRecordedHere
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
  finalReducerReceiptValue

canonicalReducerRecordedHereIsTrue :
  reducerRecordedHere canonicalReceipt ≡ true
canonicalReducerRecordedHereIsTrue =
  refl

canonicalPackageAssembledHereIsTrue :
  packageAssembledHere canonicalReceipt ≡ true
canonicalPackageAssembledHereIsTrue =
  refl

canonicalRowsRecordedHereIsTrue :
  rowsRecordedHere canonicalReceipt ≡ true
canonicalRowsRecordedHereIsTrue =
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

canonicalRequirementTransferLowerBoundReadyIsFalse :
  TransferReadinessRequirement.transferLowerBoundReady
    canonicalTransferReadinessRequirement ≡ false
canonicalRequirementTransferLowerBoundReadyIsFalse =
  refl

canonicalFinalReceiptTransferLowerBoundReadyHereIsFalse :
  FinalReceipt.transferLowerBoundReadyHereFlag finalReceipt ≡ false
canonicalFinalReceiptTransferLowerBoundReadyHereIsFalse =
  refl

canonicalFinalReceiptClayYangMillsPromotedIsFalse :
  FinalReceipt.clayYangMillsPromotedHere finalReceipt ≡ false
canonicalFinalReceiptClayYangMillsPromotedIsFalse =
  refl
