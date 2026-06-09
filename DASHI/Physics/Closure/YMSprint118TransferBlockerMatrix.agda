module DASHI.Physics.Closure.YMSprint118TransferBlockerMatrix where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint117TransferReadinessObligationReducer
  as Reducer117
import DASHI.Physics.Closure.YMSprint117CommonCarrierFeedThroughPropagator
  as Feed117

------------------------------------------------------------------------
-- Sprint118 transfer blocker matrix.
--
-- This module normalizes the false Sprint117 readiness/proof boundary into
-- owner lanes, upstream source paths, required resolutions, and blocker
-- classes.  It imports only the two stable Sprint117 receipts named above.
-- Parallel Sprint118 work is referenced only by String paths.

sprintNumber : Nat
sprintNumber = 118

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint118TransferBlockerMatrix.agda"

transferLowerBoundReadyHere : Bool
transferLowerBoundReadyHere = false

transferLowerBoundTheoremProvedHere : Bool
transferLowerBoundTheoremProvedHere = false

continuumMassGapProvedHere : Bool
continuumMassGapProvedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

blockerMatrixRecorded : Bool
blockerMatrixRecorded = true

sprint118NormLanePath : String
sprint118NormLanePath =
  "DASHI/Physics/Closure/YMSprint118NormFeedResolution.agda"

sprint118ResidualLanePath : String
sprint118ResidualLanePath =
  "DASHI/Physics/Closure/YMSprint118ResidualFeedResolution.agda"

sprint118SectorLanePath : String
sprint118SectorLanePath =
  "DASHI/Physics/Closure/YMSprint118SectorFeedResolution.agda"

sprint118CarrierLanePath : String
sprint118CarrierLanePath =
  "DASHI/Physics/Closure/YMSprint118ExternalCarrierResolution.agda"

sprint118SpectrumLanePath : String
sprint118SpectrumLanePath =
  "DASHI/Physics/Closure/YMSprint118SpectrumPollutionResolution.agda"

sprint118CompactnessLanePath : String
sprint118CompactnessLanePath =
  "DASHI/Physics/Closure/YMSprint118CompactnessRecoveryResolution.agda"

sprint118TransportLanePath : String
sprint118TransportLanePath =
  "DASHI/Physics/Closure/YMSprint118UniformTransportResolution.agda"

sprint118ReadinessLanePath : String
sprint118ReadinessLanePath =
  "DASHI/Physics/Closure/YMSprint118ReadinessIntegrator.agda"

sprint118GovernanceLanePath : String
sprint118GovernanceLanePath =
  "DASHI/Physics/Closure/YMSprint118ClayGovernancePromotionGate.agda"

matrixSummaryText : String
matrixSummaryText =
  "Sprint118 blocker matrix normalizes every false Sprint117 transfer-readiness and proof flag into an owner lane, upstream source path, required resolution, and blocker class."

readinessStillFalseText : String
readinessStillFalseText =
  "Transfer lower-bound readiness stays false here because this module records blockers only and consumes no Sprint118 sibling proof."

theoremStillFalseText : String
theoremStillFalseText =
  "Transfer lower-bound theorem, continuum mass gap, and Clay Yang-Mills promotion remain false until all blocker rows are discharged by their owner lanes."

data OwnerLane : Set where
  norm-feed-lane :
    OwnerLane
  residual-feed-lane :
    OwnerLane
  sector-feed-lane :
    OwnerLane
  common-carrier-feed-lane :
    OwnerLane
  external-carrier-lane :
    OwnerLane
  spectral-bottom-lane :
    OwnerLane
  closed-form-lsc-lane :
    OwnerLane
  recovery-limsup-lane :
    OwnerLane
  weak-compactness-lane :
    OwnerLane
  uniform-form-lane :
    OwnerLane
  log-generator-lane :
    OwnerLane
  spectral-transport-lane :
    OwnerLane
  readiness-integrator-lane :
    OwnerLane
  clay-governance-lane :
    OwnerLane

data BlockerKind : Set where
  internal-feed :
    BlockerKind
  external-analytic :
    BlockerKind
  Clay-governance :
    BlockerKind

data Sprint117FalseFlag : Set where
  feed117-norm-feed-closed :
    Sprint117FalseFlag
  feed117-residual-feed-closed :
    Sprint117FalseFlag
  feed117-sector-feed-closed :
    Sprint117FalseFlag
  feed117-common-carrier-feed-through-closed :
    Sprint117FalseFlag
  feed117-external-common-carrier-closed :
    Sprint117FalseFlag
  reducer117-common-carrier-feed-through-closed :
    Sprint117FalseFlag
  reducer117-all-obligations-discharged :
    Sprint117FalseFlag
  reducer117-external-common-carrier-construction :
    Sprint117FalseFlag
  reducer117-no-bottom-spectrum-pollution :
    Sprint117FalseFlag
  reducer117-no-collapse-at-zero :
    Sprint117FalseFlag
  reducer117-closed-form-lower-semicontinuity :
    Sprint117FalseFlag
  reducer117-recovery-limsup :
    Sprint117FalseFlag
  reducer117-weak-compactness :
    Sprint117FalseFlag
  reducer117-uniform-form-lower-bound :
    Sprint117FalseFlag
  reducer117-log-generator-calculus :
    Sprint117FalseFlag
  reducer117-spectral-transport :
    Sprint117FalseFlag
  reducer117-mosco-no-pollution-bridge :
    Sprint117FalseFlag
  feed117-transfer-lower-bound-ready :
    Sprint117FalseFlag
  reducer117-transfer-lower-bound-ready :
    Sprint117FalseFlag
  feed117-transfer-lower-bound-theorem :
    Sprint117FalseFlag
  reducer117-transfer-lower-bound-theorem :
    Sprint117FalseFlag
  feed117-continuum-mass-gap :
    Sprint117FalseFlag
  reducer117-continuum-mass-gap :
    Sprint117FalseFlag
  feed117-clay-promotion :
    Sprint117FalseFlag
  reducer117-clay-promotion :
    Sprint117FalseFlag

data MatrixStatus : Set where
  blocker-row-recorded :
    MatrixStatus
  upstream-false-confirmed :
    MatrixStatus
  source-path-only :
    MatrixStatus
  resolution-required :
    MatrixStatus
  matrix-fail-closed :
    MatrixStatus
  receipt-final :
    MatrixStatus

record BlockerRow : Set where
  constructor mkBlockerRow
  field
    falseFlag :
      Sprint117FalseFlag
    ownerLane :
      OwnerLane
    ownerLanePath :
      String
    upstreamSourcePath :
      String
    requiredResolution :
      String
    blockerKind :
      BlockerKind
    evidenceString :
      String
    upstreamFalseFlag :
      Bool
    upstreamFalseFlagIsFalse :
      upstreamFalseFlag ≡ false
    rowRecorded :
      Bool
    status :
      MatrixStatus

record MatrixCoverage : Set where
  constructor mkMatrixCoverage
  field
    rowCount :
      Nat
    rows :
      List BlockerRow
    coversSprint117FalseReadinessFlags :
      Bool
    coversSprint117FalseProofFlags :
      Bool
    usesOnlyStringPathsForSprint118Siblings :
      Bool
    normalizedOwnerLanes :
      Bool
    blockerClassesExhausted :
      List BlockerKind
    status :
      MatrixStatus

record ImportedSprint117Receipts : Setω where
  constructor mkImportedSprint117Receipts
  field
    reducerReceipt :
      Reducer117.YMSprint117TransferReadinessObligationReducerReceipt
    feedThroughReceipt :
      Feed117.YMSprint117CommonCarrierFeedThroughPropagatorReceipt
    reducerSourcePath :
      String
    feedThroughSourcePath :
      String
    reducerTransferReady :
      Bool
    feedTransferReady :
      Bool
    reducerTransferReadyIsFalse :
      reducerTransferReady ≡ false
    feedTransferReadyIsFalse :
      feedTransferReady ≡ false
    reducerTheorem :
      Bool
    feedTheorem :
      Bool
    reducerTheoremIsFalse :
      reducerTheorem ≡ false
    feedTheoremIsFalse :
      feedTheorem ≡ false
    reducerClayPromoted :
      Bool
    feedClayPromoted :
      Bool
    reducerClayPromotedIsFalse :
      reducerClayPromoted ≡ false
    feedClayPromotedIsFalse :
      feedClayPromoted ≡ false

record TransferBlockerMatrixReceipt : Setω where
  constructor mkTransferBlockerMatrixReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    importedReceipts :
      ImportedSprint117Receipts
    matrixCoverage :
      MatrixCoverage
    canonicalRows :
      List BlockerRow
    evidenceLedger :
      List String
    matrixStatement :
      String
    receiptRecorded :
      Bool
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
    finalStatus :
      MatrixStatus

open TransferBlockerMatrixReceipt public

mkInternalFeedRow :
  Sprint117FalseFlag →
  OwnerLane →
  String →
  String →
  String →
  String →
  (upstreamFlag : Bool) →
  upstreamFlag ≡ false →
  BlockerRow
mkInternalFeedRow flag lane lanePath upstream resolution evidence upstreamFlag upstreamFlagIsFalse =
  mkBlockerRow
    flag
    lane
    lanePath
    upstream
    resolution
    internal-feed
    evidence
    upstreamFlag
    upstreamFlagIsFalse
    true
    upstream-false-confirmed

mkExternalAnalyticRow :
  Sprint117FalseFlag →
  OwnerLane →
  String →
  String →
  String →
  String →
  (upstreamFlag : Bool) →
  upstreamFlag ≡ false →
  BlockerRow
mkExternalAnalyticRow flag lane lanePath upstream resolution evidence upstreamFlag upstreamFlagIsFalse =
  mkBlockerRow
    flag
    lane
    lanePath
    upstream
    resolution
    external-analytic
    evidence
    upstreamFlag
    upstreamFlagIsFalse
    true
    resolution-required

mkClayGovernanceRow :
  Sprint117FalseFlag →
  String →
  String →
  String →
  (upstreamFlag : Bool) →
  upstreamFlag ≡ false →
  BlockerRow
mkClayGovernanceRow flag upstream resolution evidence upstreamFlag upstreamFlagIsFalse =
  mkBlockerRow
    flag
    clay-governance-lane
    sprint118GovernanceLanePath
    upstream
    resolution
    Clay-governance
    evidence
    upstreamFlag
    upstreamFlagIsFalse
    true
    matrix-fail-closed

normFeedRow : BlockerRow
normFeedRow =
  mkInternalFeedRow
    feed117-norm-feed-closed
    norm-feed-lane
    sprint118NormLanePath
    Feed117.sprint117NormFeedSourcePath
    "Close Sprint117 norm feed in the referenced lane, then expose a stable receipt for transfer integration."
    Feed117.normFeedDependencyText
    Feed117.normFeedClosedHere
    refl

residualFeedRow : BlockerRow
residualFeedRow =
  mkInternalFeedRow
    feed117-residual-feed-closed
    residual-feed-lane
    sprint118ResidualLanePath
    Feed117.sprint117ResidualFeedSourcePath
    "Close Sprint117 residual feed for quadrature, inverse/projection, E_a/P_a, and renormalized form residuals."
    Feed117.residualFeedDependencyText
    Feed117.residualFeedClosedHere
    refl

sectorFeedRow : BlockerRow
sectorFeedRow =
  mkInternalFeedRow
    feed117-sector-feed-closed
    sector-feed-lane
    sprint118SectorLanePath
    Feed117.sprint117SectorFeedSourcePath
    "Close Sprint117 sector feed for gauge quotient independence, physical projection compatibility, and sector stability."
    Feed117.sectorFeedDependencyText
    Feed117.sectorFeedClosedHere
    refl

feedThroughRow : BlockerRow
feedThroughRow =
  mkInternalFeedRow
    feed117-common-carrier-feed-through-closed
    common-carrier-feed-lane
    sprint118ReadinessLanePath
    Feed117.modulePath
    "Integrate norm, residual, sector, and external carrier closures into the common-carrier feed-through receipt."
    Feed117.propagationRouteText
    Feed117.commonCarrierFeedThroughClosedHere
    refl

reducerFeedThroughRow : BlockerRow
reducerFeedThroughRow =
  mkInternalFeedRow
    reducer117-common-carrier-feed-through-closed
    common-carrier-feed-lane
    sprint118ReadinessLanePath
    Reducer117.modulePath
    "Discharge the Sprint117 reducer common-carrier feed-through blocker after feed propagation closes."
    Reducer117.commonCarrierFeedThroughText
    Reducer117.commonCarrierFeedThroughClosedHere
    refl

allObligationsRow : BlockerRow
allObligationsRow =
  mkInternalFeedRow
    reducer117-all-obligations-discharged
    readiness-integrator-lane
    sprint118ReadinessLanePath
    Reducer117.modulePath
    "Compute all-obligations-discharge only after every matrix row is externally or internally resolved."
    Reducer117.failClosedReadinessText
    Reducer117.allObligationsDischargedHere
    refl

externalCarrierFeedRow : BlockerRow
externalCarrierFeedRow =
  mkExternalAnalyticRow
    feed117-external-common-carrier-closed
    external-carrier-lane
    sprint118CarrierLanePath
    Feed117.sprint117ExternalCommonCarrierSourcePath
    "Construct and certify the external common carrier consumed by the Sprint117 feed-through propagator."
    Feed117.nonPromotionBoundaryText
    Feed117.externalCommonCarrierClosedHere
    refl

externalCarrierReducerRow : BlockerRow
externalCarrierReducerRow =
  mkExternalAnalyticRow
    reducer117-external-common-carrier-construction
    external-carrier-lane
    sprint118CarrierLanePath
    Reducer117.sprint110CarrierSourcePath
    "Construct the physical Hilbert carrier, finite carriers, E_a/P_a maps, gauge quotient compatibility, sector split, and norm window."
    Reducer117.externalCommonCarrierConstructionText
    Reducer117.externalCommonCarrierConstructionClosedHere
    refl

noBottomRow : BlockerRow
noBottomRow =
  mkExternalAnalyticRow
    reducer117-no-bottom-spectrum-pollution
    spectral-bottom-lane
    sprint118SpectrumLanePath
    Reducer117.sprint109NoBottomSourcePath
    "Prove no spurious low-energy branches enter the continuum bottom sector."
    Reducer117.noBottomNoCollapseText
    Reducer117.noBottomSpectrumPollutionClosedHere
    refl

noCollapseRow : BlockerRow
noCollapseRow =
  mkExternalAnalyticRow
    reducer117-no-collapse-at-zero
    spectral-bottom-lane
    sprint118SpectrumLanePath
    Reducer117.sprint110NoCollapseSourcePath
    "Prove non-vacuum eigenbranches cannot collapse to zero in the bottom sector threshold."
    Reducer117.noBottomNoCollapseText
    Reducer117.noCollapseAtZeroClosedHere
    refl

closedFormRow : BlockerRow
closedFormRow =
  mkExternalAnalyticRow
    reducer117-closed-form-lower-semicontinuity
    closed-form-lsc-lane
    sprint118CompactnessLanePath
    Reducer117.sprint110ClosedFormSourcePath
    "Prove common-carrier domain identification, closedness, semiboundedness, and liminf lower semicontinuity."
    Reducer117.closedFormLSCText
    Reducer117.closedFormLowerSemicontinuityClosedHere
    refl

recoveryRow : BlockerRow
recoveryRow =
  mkExternalAnalyticRow
    reducer117-recovery-limsup
    recovery-limsup-lane
    sprint118CompactnessLanePath
    Reducer117.sprint110RecoverySourcePath
    "Prove dense finite physical core recovery, strong norm recovery, and energy limsup."
    Reducer117.recoveryLimsupText
    Reducer117.recoveryLimsupClosedHere
    refl

weakCompactnessRow : BlockerRow
weakCompactnessRow =
  mkExternalAnalyticRow
    reducer117-weak-compactness
    weak-compactness-lane
    sprint118CompactnessLanePath
    Reducer117.sprint110WeakSourcePath
    "Prove bounded-energy finite-carrier sequences admit physical weak subsequences on the common carrier."
    Reducer117.weakCompactnessText
    Reducer117.weakCompactnessClosedHere
    refl

uniformFormRow : BlockerRow
uniformFormRow =
  mkExternalAnalyticRow
    reducer117-uniform-form-lower-bound
    uniform-form-lane
    sprint118TransportLanePath
    Reducer117.sprint108UniformFormSourcePath
    "Prove uniform form coercivity and lower-bound stability in the common-carrier convention."
    Reducer117.uniformFormLogSpectralText
    Reducer117.uniformFormLowerBoundClosedHere
    refl

logGeneratorRow : BlockerRow
logGeneratorRow =
  mkExternalAnalyticRow
    reducer117-log-generator-calculus
    log-generator-lane
    sprint118TransportLanePath
    Reducer117.sprint108LogGeneratorSourcePath
    "Prove logarithmic-generator functional calculus on a common core compatible with transfer."
    Reducer117.uniformFormLogSpectralText
    Reducer117.logGeneratorCalculusClosedHere
    refl

spectralTransportRow : BlockerRow
spectralTransportRow =
  mkExternalAnalyticRow
    reducer117-spectral-transport
    spectral-transport-lane
    sprint118TransportLanePath
    Reducer117.sprint108SpectralTransportSourcePath
    "Prove finite-threshold spectral transport to the continuum physical spectrum."
    Reducer117.uniformFormLogSpectralText
    Reducer117.spectralTransportClosedHere
    refl

moscoBridgeRow : BlockerRow
moscoBridgeRow =
  mkExternalAnalyticRow
    reducer117-mosco-no-pollution-bridge
    spectral-transport-lane
    sprint118TransportLanePath
    Reducer117.sprint108MoscoSourcePath
    "Close the Mosco no-pollution bridge before transfer readiness can be integrated."
    Reducer117.noBottomNoCollapseText
    Reducer117.moscoNoPollutionBridgeClosedHere
    refl

feedReadinessRow : BlockerRow
feedReadinessRow =
  mkInternalFeedRow
    feed117-transfer-lower-bound-ready
    readiness-integrator-lane
    sprint118ReadinessLanePath
    Feed117.modulePath
    "Set feed-through readiness only after feed and external carrier blockers are closed by their owner lanes."
    readinessStillFalseText
    Feed117.transferLowerBoundReadyHere
    refl

reducerReadinessRow : BlockerRow
reducerReadinessRow =
  mkInternalFeedRow
    reducer117-transfer-lower-bound-ready
    readiness-integrator-lane
    sprint118ReadinessLanePath
    Reducer117.modulePath
    "Set reducer readiness only after all reducer obligations are discharged and normalized through this matrix."
    Reducer117.failClosedReadinessText
    Reducer117.transferLowerBoundReadyHere
    refl

feedTheoremRow : BlockerRow
feedTheoremRow =
  mkClayGovernanceRow
    feed117-transfer-lower-bound-theorem
    Feed117.modulePath
    "Promote no theorem from feed propagation; require a separate transfer lower-bound proof receipt."
    theoremStillFalseText
    Feed117.transferLowerBoundTheoremProvedHere
    refl

reducerTheoremRow : BlockerRow
reducerTheoremRow =
  mkClayGovernanceRow
    reducer117-transfer-lower-bound-theorem
    Reducer117.modulePath
    "Promote no theorem from the reducer; require a separate lower-bound theorem after readiness is true."
    Reducer117.nonPromotionBoundaryText
    Reducer117.transferLowerBoundTheoremProvedHere
    refl

feedMassGapRow : BlockerRow
feedMassGapRow =
  mkClayGovernanceRow
    feed117-continuum-mass-gap
    Feed117.modulePath
    "Continuum mass gap remains blocked until a proved transfer lower bound is governance-accepted."
    theoremStillFalseText
    Feed117.continuumMassGapProvedHere
    refl

reducerMassGapRow : BlockerRow
reducerMassGapRow =
  mkClayGovernanceRow
    reducer117-continuum-mass-gap
    Reducer117.modulePath
    "Reducer evidence alone cannot assert the continuum mass gap; require final proof and governance gate."
    Reducer117.nonPromotionBoundaryText
    Reducer117.continuumMassGapProvedHere
    refl

feedClayRow : BlockerRow
feedClayRow =
  mkClayGovernanceRow
    feed117-clay-promotion
    Feed117.modulePath
    "Clay Yang-Mills promotion stays false for feed propagation until all analytic and governance criteria close."
    Feed117.nonPromotionBoundaryText
    Feed117.clayYangMillsPromoted
    refl

reducerClayRow : BlockerRow
reducerClayRow =
  mkClayGovernanceRow
    reducer117-clay-promotion
    Reducer117.modulePath
    "Clay Yang-Mills promotion stays false for the reducer until theorem and mass-gap gates are closed."
    Reducer117.nonPromotionBoundaryText
    Reducer117.clayYangMillsPromoted
    refl

canonicalBlockerRows : List BlockerRow
canonicalBlockerRows =
  normFeedRow
  ∷ residualFeedRow
  ∷ sectorFeedRow
  ∷ feedThroughRow
  ∷ reducerFeedThroughRow
  ∷ allObligationsRow
  ∷ externalCarrierFeedRow
  ∷ externalCarrierReducerRow
  ∷ noBottomRow
  ∷ noCollapseRow
  ∷ closedFormRow
  ∷ recoveryRow
  ∷ weakCompactnessRow
  ∷ uniformFormRow
  ∷ logGeneratorRow
  ∷ spectralTransportRow
  ∷ moscoBridgeRow
  ∷ feedReadinessRow
  ∷ reducerReadinessRow
  ∷ feedTheoremRow
  ∷ reducerTheoremRow
  ∷ feedMassGapRow
  ∷ reducerMassGapRow
  ∷ feedClayRow
  ∷ reducerClayRow
  ∷ []

canonicalEvidenceLedger : List String
canonicalEvidenceLedger =
  matrixSummaryText
  ∷ readinessStillFalseText
  ∷ theoremStillFalseText
  ∷ Feed117.normFeedDependencyText
  ∷ Feed117.residualFeedDependencyText
  ∷ Feed117.sectorFeedDependencyText
  ∷ Feed117.propagationRouteText
  ∷ Reducer117.commonCarrierFeedThroughText
  ∷ Reducer117.externalCommonCarrierConstructionText
  ∷ Reducer117.noBottomNoCollapseText
  ∷ Reducer117.closedFormLSCText
  ∷ Reducer117.recoveryLimsupText
  ∷ Reducer117.weakCompactnessText
  ∷ Reducer117.uniformFormLogSpectralText
  ∷ Reducer117.failClosedReadinessText
  ∷ Reducer117.nonPromotionBoundaryText
  ∷ []

canonicalImportedSprint117Receipts : ImportedSprint117Receipts
canonicalImportedSprint117Receipts =
  mkImportedSprint117Receipts
    Reducer117.canonicalReceipt
    Feed117.canonicalReceipt
    Reducer117.modulePath
    Feed117.modulePath
    Reducer117.transferLowerBoundReadyHere
    Feed117.transferLowerBoundReadyHere
    refl
    refl
    Reducer117.transferLowerBoundTheoremProvedHere
    Feed117.transferLowerBoundTheoremProvedHere
    refl
    refl
    Reducer117.clayYangMillsPromoted
    Feed117.clayYangMillsPromoted
    refl
    refl

canonicalMatrixCoverage : MatrixCoverage
canonicalMatrixCoverage =
  mkMatrixCoverage
    25
    canonicalBlockerRows
    true
    true
    true
    true
    (internal-feed ∷ external-analytic ∷ Clay-governance ∷ [])
    blocker-row-recorded

canonicalReceipt : TransferBlockerMatrixReceipt
canonicalReceipt =
  mkTransferBlockerMatrixReceipt
    sprintNumber
    modulePath
    canonicalImportedSprint117Receipts
    canonicalMatrixCoverage
    canonicalBlockerRows
    canonicalEvidenceLedger
    matrixSummaryText
    blockerMatrixRecorded
    transferLowerBoundReadyHere
    refl
    transferLowerBoundTheoremProvedHere
    refl
    continuumMassGapProvedHere
    refl
    clayYangMillsPromoted
    refl
    receipt-final

finalReceipt : TransferBlockerMatrixReceipt
finalReceipt =
  canonicalReceipt

canonicalReceiptTransferLowerBoundReadyHereIsFalse :
  transferLowerBoundReadyHereFlag canonicalReceipt ≡ false
canonicalReceiptTransferLowerBoundReadyHereIsFalse =
  refl

canonicalReceiptTransferLowerBoundTheoremProvedHereIsFalse :
  transferLowerBoundTheoremProvedHereFlag canonicalReceipt ≡ false
canonicalReceiptTransferLowerBoundTheoremProvedHereIsFalse =
  refl

canonicalReceiptContinuumMassGapProvedHereIsFalse :
  continuumMassGapProvedHereFlag canonicalReceipt ≡ false
canonicalReceiptContinuumMassGapProvedHereIsFalse =
  refl

canonicalReceiptClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalReceiptClayYangMillsPromotedIsFalse =
  refl

canonicalReceiptRowCount : Nat
canonicalReceiptRowCount =
  MatrixCoverage.rowCount (matrixCoverage canonicalReceipt)
