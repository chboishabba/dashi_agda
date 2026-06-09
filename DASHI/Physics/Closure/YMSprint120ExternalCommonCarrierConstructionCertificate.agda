module DASHI.Physics.Closure.YMSprint120ExternalCommonCarrierConstructionCertificate where

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
import DASHI.Physics.Closure.YMSprint118CommonCarrierConstructionReadiness
  as Readiness118
import DASHI.Physics.Closure.YMSprint119CommonCarrierFeedThroughUnlockAttempt
  as Unlock119

------------------------------------------------------------------------
-- Sprint120 external common-carrier construction certificate.
--
-- This module records the analytic certificate interface needed before the
-- external common-carrier construction can be treated as closed.  It gives
-- exact rows for E_a/P_a construction, quotient descent, norm window,
-- adjointness/approximate inverse, projection stability, weak/recovery
-- feed-through, and estimate closure.  The interface and row ledger are
-- complete, but the actual construction theorem and all downstream theorem
-- flags remain fail-closed.

sprintNumber : Nat
sprintNumber = 120

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint120ExternalCommonCarrierConstructionCertificate.agda"

sprint111ConstructionAssemblyPath : String
sprint111ConstructionAssemblyPath =
  Carrier111.embeddingProjectionMapsSiblingPath

sprint111CarrierAssemblyPath : String
sprint111CarrierAssemblyPath =
  "DASHI/Physics/Closure/YMSprint111CommonCarrierConstructionAssembly.agda"

sprint114EstimateClosurePath : String
sprint114EstimateClosurePath =
  Estimate114.modulePath

sprint118ReadinessPath : String
sprint118ReadinessPath =
  Readiness118.modulePath

sprint119UnlockAttemptPath : String
sprint119UnlockAttemptPath =
  Unlock119.modulePath

certificateInterfaceRecorded : Bool
certificateInterfaceRecorded = true

certificateRowsComplete : Bool
certificateRowsComplete = true

sourcePathLedgerRecorded : Bool
sourcePathLedgerRecorded = true

readinessInputsRecorded : Bool
readinessInputsRecorded = true

absentCertificateReasonsRecorded : Bool
absentCertificateReasonsRecorded = true

canonicalReceiptRecorded : Bool
canonicalReceiptRecorded = true

finalReceiptRecorded : Bool
finalReceiptRecorded = true

externalCommonCarrierConstructionClosedHere : Bool
externalCommonCarrierConstructionClosedHere = false

externalCommonCarrierConstructionTheoremProvedHere : Bool
externalCommonCarrierConstructionTheoremProvedHere = false

commonCarrierConstructionTheoremProvedHere : Bool
commonCarrierConstructionTheoremProvedHere = false

commonCarrierFeedThroughClosedHere : Bool
commonCarrierFeedThroughClosedHere = false

transferLowerBoundReadyHere : Bool
transferLowerBoundReadyHere = false

transferLowerBoundTheoremProvedHere : Bool
transferLowerBoundTheoremProvedHere = false

continuumMassGapProvedHere : Bool
continuumMassGapProvedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

readiness118Imported : Bool
readiness118Imported =
  Readiness118.constructionReadinessPackageAssembledHere

unlock119Imported : Bool
unlock119Imported =
  Unlock119.feedThroughUnlockAttemptRecorded

carrier111Imported : Bool
carrier111Imported =
  Carrier111.sprint111AssemblyRecorded

estimate114Imported : Bool
estimate114Imported =
  Estimate114.assemblyRecorded

readiness118ExternalConstructionClosedInput : Bool
readiness118ExternalConstructionClosedInput =
  Readiness118.externalCommonCarrierConstructionClosedHere

readiness118ConstructionTheoremInput : Bool
readiness118ConstructionTheoremInput =
  Readiness118.commonCarrierConstructionTheoremProvedHere

readiness118FeedThroughClosedInput : Bool
readiness118FeedThroughClosedInput =
  Readiness118.commonCarrierFeedThroughClosedHere

readiness118TransferReadyInput : Bool
readiness118TransferReadyInput =
  Readiness118.transferLowerBoundReadyHere

unlock119ExternalConstructionTheoremInput : Bool
unlock119ExternalConstructionTheoremInput =
  Unlock119.externalCommonCarrierConstructionTheoremProvedHere

unlock119FeedThroughClosedInput : Bool
unlock119FeedThroughClosedInput =
  Unlock119.commonCarrierFeedThroughClosedHere

unlock119TransferReadyInput : Bool
unlock119TransferReadyInput =
  Unlock119.transferLowerBoundReadyHere

carrier111ConstructionClosedInput : Bool
carrier111ConstructionClosedInput =
  Carrier111.commonCarrierConstructionClosedHere

estimate114ClosureClosedInput : Bool
estimate114ClosureClosedInput =
  Estimate114.commonCarrierEstimateClosureClosedHere

interfaceStatementText : String
interfaceStatementText =
  "Sprint120 records the complete external common-carrier construction certificate interface: every analytic row is named, sourced, and bound to readiness inputs, while no external construction theorem is proved here."

sourcePathLedgerText : String
sourcePathLedgerText =
  "Source ledger: Sprint120 consumes Sprint118 construction readiness, Sprint119 unlock attempt, Sprint111 carrier construction assembly, and Sprint114 estimate closure assembly."

readinessInputText : String
readinessInputText =
  "Readiness input ledger: Sprint118 readiness is true as an assembled interface, Sprint119 unlock attempt is true as a blocker ledger, and the imported closure/theorem flags remain false."

eAPaConstructionRowText : String
eAPaConstructionRowText =
  "Certificate row A: construct concrete E_a and P_a maps on the shared finite and continuum physical quotient carriers using the Sprint111 renormalized convention."

quotientDescentRowText : String
quotientDescentRowText =
  "Certificate row B: prove finite representative independence, continuum quotient descent, gauge covariance, and physical-sector compatibility for the same E_a/P_a maps."

normWindowRowText : String
normWindowRowText =
  "Certificate row C: prove the cutoff-uniform upper and lower norm window over the admissible a-range using the Sprint114 constant package C_package=645120."

adjointnessApproxInverseRowText : String
adjointnessApproxInverseRowText =
  "Certificate row D: prove E_a/P_a adjointness residuals or left/right approximate inverse residuals vanish in the quotient Hilbert norms."

projectionStabilityRowText : String
projectionStabilityRowText =
  "Certificate row E: prove physical projection commutators, quotient projection stability, and vacuum/non-vacuum sector stability."

weakRecoveryFeedThroughRowText : String
weakRecoveryFeedThroughRowText =
  "Certificate row F: feed the same completed carrier through weak compactness, lower semicontinuity, recovery strong convergence, and recovery energy limsup."

estimateClosureRowText : String
estimateClosureRowText =
  "Certificate row G: close the Sprint114 common-carrier estimate package, including gauge quotient, norm constants, quadrature residual, inverse/projection, and weak/recovery requirements."

externalConstructionAbsentReasonText : String
externalConstructionAbsentReasonText =
  "Absent certificate reason: the seven analytic rows are specified but not supplied as proofs, so external common-carrier construction closure stays false."

feedThroughAbsentReasonText : String
feedThroughAbsentReasonText =
  "Absent certificate reason: Sprint119 still lacks the external construction theorem, weak/Mosco aggregate, transfer calculus aggregate, and readiness propagation closure."

transferAbsentReasonText : String
transferAbsentReasonText =
  "Absent certificate reason: transfer lower-bound readiness requires closed external construction and feed-through; both remain false in the imported receipts and here."

promotionAbsentReasonText : String
promotionAbsentReasonText =
  "Absent certificate reason: Clay Yang-Mills promotion is not available because no transfer lower-bound theorem, continuum mass gap theorem, or external construction theorem is proved here."

canonicalReceiptText : String
canonicalReceiptText =
  "Canonical Sprint120 receipt: certificate interface and rows are complete, source paths and readiness inputs are recorded, absent-certificate reasons are explicit, and all theorem flags remain false."

finalReceiptText : String
finalReceiptText =
  "Final Sprint120 receipt: the analytic certificate surface is fully inhabited as a ledger only; it proves no external construction closure, no feed-through closure, no transfer theorem, no mass gap, and no Clay promotion."

data CertificateLane : Set where
  source-path-lane :
    CertificateLane
  readiness-input-lane :
    CertificateLane
  e-a-p-a-construction-lane :
    CertificateLane
  quotient-descent-lane :
    CertificateLane
  norm-window-lane :
    CertificateLane
  adjointness-approx-inverse-lane :
    CertificateLane
  projection-stability-lane :
    CertificateLane
  weak-recovery-feed-through-lane :
    CertificateLane
  estimate-closure-lane :
    CertificateLane
  absent-certificate-reason-lane :
    CertificateLane
  theorem-boundary-lane :
    CertificateLane
  receipt-lane :
    CertificateLane

data CertificateStatus : Set where
  source-paths-recorded :
    CertificateStatus
  readiness-inputs-recorded :
    CertificateStatus
  certificate-row-recorded :
    CertificateStatus
  certificate-row-interface-complete :
    CertificateStatus
  absent-certificate-reason-recorded :
    CertificateStatus
  theorem-boundary-fail-closed :
    CertificateStatus
  canonical-receipt-recorded :
    CertificateStatus
  final-receipt-recorded :
    CertificateStatus

data CertificateRowKind : Set where
  e-a-p-a-construction :
    CertificateRowKind
  quotient-descent :
    CertificateRowKind
  norm-window :
    CertificateRowKind
  adjointness-approx-inverse :
    CertificateRowKind
  projection-stability :
    CertificateRowKind
  weak-recovery-feed-through :
    CertificateRowKind
  estimate-closure :
    CertificateRowKind

data AbsentCertificateKind : Set where
  external-construction-certificate-absent :
    AbsentCertificateKind
  feed-through-certificate-absent :
    AbsentCertificateKind
  transfer-certificate-absent :
    AbsentCertificateKind
  promotion-certificate-absent :
    AbsentCertificateKind

canonicalCertificateLanes : List CertificateLane
canonicalCertificateLanes =
  source-path-lane
  ∷ readiness-input-lane
  ∷ e-a-p-a-construction-lane
  ∷ quotient-descent-lane
  ∷ norm-window-lane
  ∷ adjointness-approx-inverse-lane
  ∷ projection-stability-lane
  ∷ weak-recovery-feed-through-lane
  ∷ estimate-closure-lane
  ∷ absent-certificate-reason-lane
  ∷ theorem-boundary-lane
  ∷ receipt-lane
  ∷ []

record SourcePathLedger : Set where
  constructor mkSourcePathLedger
  field
    currentModulePath :
      String
    sprint111CarrierAssembly :
      String
    sprint111ConstructionAssembly :
      String
    sprint114EstimateClosure :
      String
    sprint118Readiness :
      String
    sprint119UnlockAttempt :
      String
    statement :
      String
    ledgerRecorded :
      Bool
    ledgerRecordedIsTrue :
      ledgerRecorded ≡ true
    status :
      CertificateStatus

record ReadinessInputs : Setω where
  constructor mkReadinessInputs
  field
    readiness118Receipt :
      Readiness118.YMSprint118CommonCarrierConstructionReadinessReceipt
    unlock119Receipt :
      Unlock119.YMSprint119CommonCarrierFeedThroughUnlockAttemptReceipt
    carrier111Receipt :
      Carrier111.AssemblyReceipt
    estimate114Receipt :
      Estimate114.YMSprint114CommonCarrierEstimateClosureAssemblyReceipt
    statement :
      String
    readiness118Assembled :
      Bool
    readiness118AssembledIsTrue :
      readiness118Assembled ≡ true
    unlock119Recorded :
      Bool
    unlock119RecordedIsTrue :
      unlock119Recorded ≡ true
    carrier111Recorded :
      Bool
    carrier111RecordedIsTrue :
      carrier111Recorded ≡ true
    estimate114Recorded :
      Bool
    estimate114RecordedIsTrue :
      estimate114Recorded ≡ true
    readiness118ExternalConstructionClosed :
      Bool
    readiness118ExternalConstructionClosedIsFalse :
      readiness118ExternalConstructionClosed ≡ false
    unlock119ExternalConstructionTheorem :
      Bool
    unlock119ExternalConstructionTheoremIsFalse :
      unlock119ExternalConstructionTheorem ≡ false
    carrier111ConstructionClosed :
      Bool
    carrier111ConstructionClosedIsFalse :
      carrier111ConstructionClosed ≡ false
    estimate114ClosureClosed :
      Bool
    estimate114ClosureClosedIsFalse :
      estimate114ClosureClosed ≡ false
    status :
      CertificateStatus

record CertificateRow : Set where
  constructor mkCertificateRow
  field
    kind :
      CertificateRowKind
    lane :
      CertificateLane
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
    interfaceRecorded :
      Bool
    interfaceRecordedIsTrue :
      interfaceRecorded ≡ true
    rowComplete :
      Bool
    rowCompleteIsTrue :
      rowComplete ≡ true
    certificateSuppliedHere :
      Bool
    certificateSuppliedHereIsFalse :
      certificateSuppliedHere ≡ false
    status :
      CertificateStatus

record CertificateRows : Set where
  constructor mkCertificateRows
  field
    eAPaConstruction :
      CertificateRow
    quotientDescent :
      CertificateRow
    normWindow :
      CertificateRow
    adjointnessApproxInverse :
      CertificateRow
    projectionStability :
      CertificateRow
    weakRecoveryFeedThrough :
      CertificateRow
    estimateClosure :
      CertificateRow
    rows :
      List CertificateRow
    certificateInterfaceRecordedHere :
      Bool
    certificateInterfaceRecordedHereIsTrue :
      certificateInterfaceRecordedHere ≡ true
    certificateRowsCompleteHere :
      Bool
    certificateRowsCompleteHereIsTrue :
      certificateRowsCompleteHere ≡ true
    externalConstructionClosed :
      Bool
    externalConstructionClosedIsFalse :
      externalConstructionClosed ≡ false
    feedThroughClosed :
      Bool
    feedThroughClosedIsFalse :
      feedThroughClosed ≡ false
    transferReady :
      Bool
    transferReadyIsFalse :
      transferReady ≡ false
    status :
      CertificateStatus

record AbsentCertificateReason : Set where
  constructor mkAbsentCertificateReason
  field
    kind :
      AbsentCertificateKind
    lane :
      CertificateLane
    statement :
      String
    sourcePath :
      String
    reasonRecorded :
      Bool
    reasonRecordedIsTrue :
      reasonRecorded ≡ true
    targetClosedHere :
      Bool
    targetClosedHereIsFalse :
      targetClosedHere ≡ false
    status :
      CertificateStatus

record AbsentCertificateLedger : Set where
  constructor mkAbsentCertificateLedger
  field
    externalConstructionReason :
      AbsentCertificateReason
    feedThroughReason :
      AbsentCertificateReason
    transferReason :
      AbsentCertificateReason
    promotionReason :
      AbsentCertificateReason
    reasons :
      List AbsentCertificateReason
    reasonsRecorded :
      Bool
    reasonsRecordedIsTrue :
      reasonsRecorded ≡ true
    status :
      CertificateStatus

record TheoremBoundary : Set where
  constructor mkTheoremBoundary
  field
    boundaryStatement :
      String
    externalCommonCarrierConstructionClosed :
      Bool
    externalCommonCarrierConstructionClosedIsFalse :
      externalCommonCarrierConstructionClosed ≡ false
    externalCommonCarrierConstructionTheoremProved :
      Bool
    externalCommonCarrierConstructionTheoremProvedIsFalse :
      externalCommonCarrierConstructionTheoremProved ≡ false
    commonCarrierConstructionTheoremProved :
      Bool
    commonCarrierConstructionTheoremProvedIsFalse :
      commonCarrierConstructionTheoremProved ≡ false
    commonCarrierFeedThroughClosed :
      Bool
    commonCarrierFeedThroughClosedIsFalse :
      commonCarrierFeedThroughClosed ≡ false
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
      CertificateStatus

record CanonicalReceipt : Setω where
  constructor mkCanonicalReceipt
  field
    statement :
      String
    sourcePaths :
      SourcePathLedger
    readinessInputs :
      ReadinessInputs
    certificateRows :
      CertificateRows
    absentCertificateLedger :
      AbsentCertificateLedger
    theoremBoundary :
      TheoremBoundary
    lanes :
      List CertificateLane
    evidenceLedger :
      List String
    receiptRecorded :
      Bool
    receiptRecordedIsTrue :
      receiptRecorded ≡ true
    interfaceRecorded :
      Bool
    interfaceRecordedIsTrue :
      interfaceRecorded ≡ true
    rowsComplete :
      Bool
    rowsCompleteIsTrue :
      rowsComplete ≡ true
    externalConstructionClosed :
      Bool
    externalConstructionClosedIsFalse :
      externalConstructionClosed ≡ false
    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false
    status :
      CertificateStatus

record FinalReceipt : Setω where
  constructor mkFinalReceipt
  field
    statement :
      String
    canonical :
      CanonicalReceipt
    finalReceiptRecordedHere :
      Bool
    finalReceiptRecordedHereIsTrue :
      finalReceiptRecordedHere ≡ true
    certificateInterfaceRecordedHere :
      Bool
    certificateInterfaceRecordedHereIsTrue :
      certificateInterfaceRecordedHere ≡ true
    certificateRowsCompleteHere :
      Bool
    certificateRowsCompleteHereIsTrue :
      certificateRowsCompleteHere ≡ true
    externalCommonCarrierConstructionClosed :
      Bool
    externalCommonCarrierConstructionClosedIsFalse :
      externalCommonCarrierConstructionClosed ≡ false
    externalCommonCarrierConstructionTheoremProved :
      Bool
    externalCommonCarrierConstructionTheoremProvedIsFalse :
      externalCommonCarrierConstructionTheoremProved ≡ false
    commonCarrierFeedThroughClosed :
      Bool
    commonCarrierFeedThroughClosedIsFalse :
      commonCarrierFeedThroughClosed ≡ false
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
      CertificateStatus

record YMSprint120ExternalCommonCarrierConstructionCertificateReceipt :
  Setω where
  constructor mkYMSprint120ExternalCommonCarrierConstructionCertificateReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    canonicalCertificate :
      CanonicalReceipt
    finalCertificate :
      FinalReceipt
    receiptRecorded :
      Bool
    receiptRecordedIsTrue :
      receiptRecorded ≡ true
    certificateInterfaceRecordedHere :
      Bool
    certificateInterfaceRecordedHereIsTrue :
      certificateInterfaceRecordedHere ≡ true
    certificateRowsCompleteHere :
      Bool
    certificateRowsCompleteHereIsTrue :
      certificateRowsCompleteHere ≡ true
    externalCommonCarrierConstructionClosedHereFlag :
      Bool
    externalCommonCarrierConstructionClosedHereFlagIsFalse :
      externalCommonCarrierConstructionClosedHereFlag ≡ false
    externalCommonCarrierConstructionTheoremProvedHereFlag :
      Bool
    externalCommonCarrierConstructionTheoremProvedHereFlagIsFalse :
      externalCommonCarrierConstructionTheoremProvedHereFlag ≡ false
    commonCarrierFeedThroughClosedHereFlag :
      Bool
    commonCarrierFeedThroughClosedHereFlagIsFalse :
      commonCarrierFeedThroughClosedHereFlag ≡ false
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
open ReadinessInputs public
open CertificateRow public
open CertificateRows public
open AbsentCertificateReason public
open AbsentCertificateLedger public
open TheoremBoundary public
open CanonicalReceipt public
open FinalReceipt public
open YMSprint120ExternalCommonCarrierConstructionCertificateReceipt public

canonicalSourcePathLedger : SourcePathLedger
canonicalSourcePathLedger =
  mkSourcePathLedger
    modulePath
    sprint111CarrierAssemblyPath
    sprint111ConstructionAssemblyPath
    sprint114EstimateClosurePath
    sprint118ReadinessPath
    sprint119UnlockAttemptPath
    sourcePathLedgerText
    sourcePathLedgerRecorded
    refl
    source-paths-recorded

canonicalReadinessInputs : ReadinessInputs
canonicalReadinessInputs =
  mkReadinessInputs
    Readiness118.canonicalReceipt
    Unlock119.canonicalReceipt
    Carrier111.canonicalAssemblyReceipt
    Estimate114.canonicalReceipt
    readinessInputText
    readiness118Imported
    refl
    unlock119Imported
    refl
    carrier111Imported
    refl
    estimate114Imported
    refl
    readiness118ExternalConstructionClosedInput
    refl
    unlock119ExternalConstructionTheoremInput
    refl
    carrier111ConstructionClosedInput
    refl
    estimate114ClosureClosedInput
    refl
    readiness-inputs-recorded

canonicalEAPaConstructionRow : CertificateRow
canonicalEAPaConstructionRow =
  mkCertificateRow
    e-a-p-a-construction
    e-a-p-a-construction-lane
    sprint111CarrierAssemblyPath
    eAPaConstructionRowText
    true
    true
    true
    certificateInterfaceRecorded
    refl
    certificateRowsComplete
    refl
    externalCommonCarrierConstructionClosedHere
    refl
    certificate-row-recorded

canonicalQuotientDescentRow : CertificateRow
canonicalQuotientDescentRow =
  mkCertificateRow
    quotient-descent
    quotient-descent-lane
    sprint118ReadinessPath
    quotientDescentRowText
    true
    true
    true
    certificateInterfaceRecorded
    refl
    certificateRowsComplete
    refl
    externalCommonCarrierConstructionClosedHere
    refl
    certificate-row-recorded

canonicalNormWindowRow : CertificateRow
canonicalNormWindowRow =
  mkCertificateRow
    norm-window
    norm-window-lane
    sprint114EstimateClosurePath
    normWindowRowText
    true
    true
    true
    certificateInterfaceRecorded
    refl
    certificateRowsComplete
    refl
    transferLowerBoundReadyHere
    refl
    certificate-row-recorded

canonicalAdjointnessApproxInverseRow : CertificateRow
canonicalAdjointnessApproxInverseRow =
  mkCertificateRow
    adjointness-approx-inverse
    adjointness-approx-inverse-lane
    sprint114EstimateClosurePath
    adjointnessApproxInverseRowText
    true
    true
    true
    certificateInterfaceRecorded
    refl
    certificateRowsComplete
    refl
    externalCommonCarrierConstructionTheoremProvedHere
    refl
    certificate-row-recorded

canonicalProjectionStabilityRow : CertificateRow
canonicalProjectionStabilityRow =
  mkCertificateRow
    projection-stability
    projection-stability-lane
    sprint118ReadinessPath
    projectionStabilityRowText
    true
    true
    true
    certificateInterfaceRecorded
    refl
    certificateRowsComplete
    refl
    externalCommonCarrierConstructionClosedHere
    refl
    certificate-row-recorded

canonicalWeakRecoveryFeedThroughRow : CertificateRow
canonicalWeakRecoveryFeedThroughRow =
  mkCertificateRow
    weak-recovery-feed-through
    weak-recovery-feed-through-lane
    sprint119UnlockAttemptPath
    weakRecoveryFeedThroughRowText
    true
    true
    true
    certificateInterfaceRecorded
    refl
    certificateRowsComplete
    refl
    commonCarrierFeedThroughClosedHere
    refl
    certificate-row-recorded

canonicalEstimateClosureRow : CertificateRow
canonicalEstimateClosureRow =
  mkCertificateRow
    estimate-closure
    estimate-closure-lane
    sprint114EstimateClosurePath
    estimateClosureRowText
    true
    true
    true
    certificateInterfaceRecorded
    refl
    certificateRowsComplete
    refl
    estimate114ClosureClosedInput
    refl
    certificate-row-recorded

canonicalCertificateRowList : List CertificateRow
canonicalCertificateRowList =
  canonicalEAPaConstructionRow
  ∷ canonicalQuotientDescentRow
  ∷ canonicalNormWindowRow
  ∷ canonicalAdjointnessApproxInverseRow
  ∷ canonicalProjectionStabilityRow
  ∷ canonicalWeakRecoveryFeedThroughRow
  ∷ canonicalEstimateClosureRow
  ∷ []

canonicalCertificateRows : CertificateRows
canonicalCertificateRows =
  mkCertificateRows
    canonicalEAPaConstructionRow
    canonicalQuotientDescentRow
    canonicalNormWindowRow
    canonicalAdjointnessApproxInverseRow
    canonicalProjectionStabilityRow
    canonicalWeakRecoveryFeedThroughRow
    canonicalEstimateClosureRow
    canonicalCertificateRowList
    certificateInterfaceRecorded
    refl
    certificateRowsComplete
    refl
    externalCommonCarrierConstructionClosedHere
    refl
    commonCarrierFeedThroughClosedHere
    refl
    transferLowerBoundReadyHere
    refl
    certificate-row-interface-complete

canonicalExternalConstructionAbsentReason : AbsentCertificateReason
canonicalExternalConstructionAbsentReason =
  mkAbsentCertificateReason
    external-construction-certificate-absent
    absent-certificate-reason-lane
    externalConstructionAbsentReasonText
    modulePath
    absentCertificateReasonsRecorded
    refl
    externalCommonCarrierConstructionClosedHere
    refl
    absent-certificate-reason-recorded

canonicalFeedThroughAbsentReason : AbsentCertificateReason
canonicalFeedThroughAbsentReason =
  mkAbsentCertificateReason
    feed-through-certificate-absent
    absent-certificate-reason-lane
    feedThroughAbsentReasonText
    sprint119UnlockAttemptPath
    absentCertificateReasonsRecorded
    refl
    commonCarrierFeedThroughClosedHere
    refl
    absent-certificate-reason-recorded

canonicalTransferAbsentReason : AbsentCertificateReason
canonicalTransferAbsentReason =
  mkAbsentCertificateReason
    transfer-certificate-absent
    absent-certificate-reason-lane
    transferAbsentReasonText
    sprint119UnlockAttemptPath
    absentCertificateReasonsRecorded
    refl
    transferLowerBoundReadyHere
    refl
    absent-certificate-reason-recorded

canonicalPromotionAbsentReason : AbsentCertificateReason
canonicalPromotionAbsentReason =
  mkAbsentCertificateReason
    promotion-certificate-absent
    absent-certificate-reason-lane
    promotionAbsentReasonText
    modulePath
    absentCertificateReasonsRecorded
    refl
    clayYangMillsPromoted
    refl
    absent-certificate-reason-recorded

canonicalAbsentCertificateReasons : List AbsentCertificateReason
canonicalAbsentCertificateReasons =
  canonicalExternalConstructionAbsentReason
  ∷ canonicalFeedThroughAbsentReason
  ∷ canonicalTransferAbsentReason
  ∷ canonicalPromotionAbsentReason
  ∷ []

canonicalAbsentCertificateLedger : AbsentCertificateLedger
canonicalAbsentCertificateLedger =
  mkAbsentCertificateLedger
    canonicalExternalConstructionAbsentReason
    canonicalFeedThroughAbsentReason
    canonicalTransferAbsentReason
    canonicalPromotionAbsentReason
    canonicalAbsentCertificateReasons
    absentCertificateReasonsRecorded
    refl
    absent-certificate-reason-recorded

canonicalTheoremBoundary : TheoremBoundary
canonicalTheoremBoundary =
  mkTheoremBoundary
    finalReceiptText
    externalCommonCarrierConstructionClosedHere
    refl
    externalCommonCarrierConstructionTheoremProvedHere
    refl
    commonCarrierConstructionTheoremProvedHere
    refl
    commonCarrierFeedThroughClosedHere
    refl
    transferLowerBoundReadyHere
    refl
    transferLowerBoundTheoremProvedHere
    refl
    continuumMassGapProvedHere
    refl
    clayYangMillsPromoted
    refl
    theorem-boundary-fail-closed

canonicalEvidenceLedger : List String
canonicalEvidenceLedger =
  modulePath
  ∷ sprint111CarrierAssemblyPath
  ∷ sprint111ConstructionAssemblyPath
  ∷ sprint114EstimateClosurePath
  ∷ sprint118ReadinessPath
  ∷ sprint119UnlockAttemptPath
  ∷ interfaceStatementText
  ∷ sourcePathLedgerText
  ∷ readinessInputText
  ∷ eAPaConstructionRowText
  ∷ quotientDescentRowText
  ∷ normWindowRowText
  ∷ adjointnessApproxInverseRowText
  ∷ projectionStabilityRowText
  ∷ weakRecoveryFeedThroughRowText
  ∷ estimateClosureRowText
  ∷ externalConstructionAbsentReasonText
  ∷ feedThroughAbsentReasonText
  ∷ transferAbsentReasonText
  ∷ promotionAbsentReasonText
  ∷ canonicalReceiptText
  ∷ finalReceiptText
  ∷ Readiness118.finalReceiptText
  ∷ Unlock119.finalReceiptText
  ∷ []

canonicalCertificateReceipt : CanonicalReceipt
canonicalCertificateReceipt =
  mkCanonicalReceipt
    canonicalReceiptText
    canonicalSourcePathLedger
    canonicalReadinessInputs
    canonicalCertificateRows
    canonicalAbsentCertificateLedger
    canonicalTheoremBoundary
    canonicalCertificateLanes
    canonicalEvidenceLedger
    canonicalReceiptRecorded
    refl
    certificateInterfaceRecorded
    refl
    certificateRowsComplete
    refl
    externalCommonCarrierConstructionClosedHere
    refl
    clayYangMillsPromoted
    refl
    canonical-receipt-recorded

canonicalFinalReceipt : FinalReceipt
canonicalFinalReceipt =
  mkFinalReceipt
    finalReceiptText
    canonicalCertificateReceipt
    finalReceiptRecorded
    refl
    certificateInterfaceRecorded
    refl
    certificateRowsComplete
    refl
    externalCommonCarrierConstructionClosedHere
    refl
    externalCommonCarrierConstructionTheoremProvedHere
    refl
    commonCarrierFeedThroughClosedHere
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

canonicalYMSprint120ExternalCommonCarrierConstructionCertificateReceipt :
  YMSprint120ExternalCommonCarrierConstructionCertificateReceipt
canonicalYMSprint120ExternalCommonCarrierConstructionCertificateReceipt =
  mkYMSprint120ExternalCommonCarrierConstructionCertificateReceipt
    sprintNumber
    modulePath
    canonicalCertificateReceipt
    canonicalFinalReceipt
    finalReceiptRecorded
    refl
    certificateInterfaceRecorded
    refl
    certificateRowsComplete
    refl
    externalCommonCarrierConstructionClosedHere
    refl
    externalCommonCarrierConstructionTheoremProvedHere
    refl
    commonCarrierFeedThroughClosedHere
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
  YMSprint120ExternalCommonCarrierConstructionCertificateReceipt
canonicalReceipt =
  canonicalYMSprint120ExternalCommonCarrierConstructionCertificateReceipt

finalReceipt : FinalReceipt
finalReceipt =
  canonicalFinalReceipt

canonicalCertificateInterfaceRecordedIsTrue :
  certificateInterfaceRecordedHere canonicalReceipt ≡ true
canonicalCertificateInterfaceRecordedIsTrue =
  refl

canonicalCertificateRowsCompleteIsTrue :
  certificateRowsCompleteHere canonicalReceipt ≡ true
canonicalCertificateRowsCompleteIsTrue =
  refl

canonicalExternalCommonCarrierConstructionClosedHereIsFalse :
  externalCommonCarrierConstructionClosedHereFlag canonicalReceipt ≡ false
canonicalExternalCommonCarrierConstructionClosedHereIsFalse =
  refl

canonicalExternalCommonCarrierConstructionTheoremProvedHereIsFalse :
  externalCommonCarrierConstructionTheoremProvedHereFlag canonicalReceipt ≡ false
canonicalExternalCommonCarrierConstructionTheoremProvedHereIsFalse =
  refl

canonicalCommonCarrierFeedThroughClosedHereIsFalse :
  commonCarrierFeedThroughClosedHereFlag canonicalReceipt ≡ false
canonicalCommonCarrierFeedThroughClosedHereIsFalse =
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
