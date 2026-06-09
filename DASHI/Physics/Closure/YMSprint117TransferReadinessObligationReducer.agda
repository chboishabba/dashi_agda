module DASHI.Physics.Closure.YMSprint117TransferReadinessObligationReducer where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint108LogGeneratorCalculusBridge
  as Log108
import DASHI.Physics.Closure.YMSprint108MoscoNoPollutionBridge
  as Mosco108
import DASHI.Physics.Closure.YMSprint108SpectralGapTransport
  as Spectral108
import DASHI.Physics.Closure.YMSprint108TransferLowerBoundAssembly
  as Transfer108
import DASHI.Physics.Closure.YMSprint108UniformFormLowerBound
  as Form108
import DASHI.Physics.Closure.YMSprint109NoBottomSpectrumPollutionCompactness
  as Compact109
import DASHI.Physics.Closure.YMSprint109TransferLowerBoundCriticalAssembly
  as Critical109
import DASHI.Physics.Closure.YMSprint110BottomSectorThresholdNoCollapse
  as Collapse110
import DASHI.Physics.Closure.YMSprint110ClosedFormLowerSemicontinuityCriterion
  as Closed110
import DASHI.Physics.Closure.YMSprint110CommonCarrierHilbertIdentification
  as Carrier110
import DASHI.Physics.Closure.YMSprint110RecoveryCoreDensityEnergyLimsup
  as Recovery110
import DASHI.Physics.Closure.YMSprint110WeakCompactnessEnergyCore
  as Weak110
import DASHI.Physics.Closure.YMSprint116CommonCarrierTransferClosureReducer
  as Reducer116

------------------------------------------------------------------------
-- Sprint117 transfer-readiness obligation reducer.
--
-- This module does not prove a transfer lower bound.  It reduces readiness
-- for that lower bound to the exact external obligations still needed by the
-- common-carrier route:
--
--   common-carrier feed-through,
--   external common-carrier construction,
--   no bottom spectrum pollution / no collapse,
--   closed-form lower semicontinuity,
--   recovery limsup,
--   weak compactness,
--   uniform form, logarithmic generator, and spectral transport.
--
-- It is fail-closed and non-promotional.  All theorem flags remain false.

sprintNumber : Nat
sprintNumber = 117

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint117TransferReadinessObligationReducer.agda"

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

transferLowerBoundTheoremProvedHere : Bool
transferLowerBoundTheoremProvedHere = false

continuumMassGapProvedHere : Bool
continuumMassGapProvedHere = false

transferReadinessObligationReducerRecorded : Bool
transferReadinessObligationReducerRecorded = true

transferLowerBoundReadyHere : Bool
transferLowerBoundReadyHere = false

allObligationsDischargedHere : Bool
allObligationsDischargedHere = false

commonCarrierFeedThroughClosedHere : Bool
commonCarrierFeedThroughClosedHere =
  Reducer116.commonCarrierFeedThroughClosedHere

externalCommonCarrierConstructionClosedHere : Bool
externalCommonCarrierConstructionClosedHere =
  Reducer116.externalCommonCarrierClosedHere

noBottomSpectrumPollutionClosedHere : Bool
noBottomSpectrumPollutionClosedHere =
  Compact109.noBottomSpectrumPollutionCompactnessTheoremProved

noCollapseAtZeroClosedHere : Bool
noCollapseAtZeroClosedHere =
  Collapse110.noCollapseAtZeroClosed

closedFormLowerSemicontinuityClosedHere : Bool
closedFormLowerSemicontinuityClosedHere =
  Closed110.closedFormCriterionClosedHere

recoveryLimsupClosedHere : Bool
recoveryLimsupClosedHere =
  Recovery110.moscoRecoverySideClosedHere

weakCompactnessClosedHere : Bool
weakCompactnessClosedHere =
  Weak110.weakSubsequenceExtractionProvedHere

uniformFormLowerBoundClosedHere : Bool
uniformFormLowerBoundClosedHere =
  Form108.uniformFormLowerBoundTheoremProved

logGeneratorCalculusClosedHere : Bool
logGeneratorCalculusClosedHere =
  Log108.functionalCalculusTheoremProvedHere

spectralTransportClosedHere : Bool
spectralTransportClosedHere =
  Spectral108.transportTheoremProvedHere

moscoNoPollutionBridgeClosedHere : Bool
moscoNoPollutionBridgeClosedHere =
  Mosco108.uniformTransferTargetProvedHere

sprint116ReducerSourcePath : String
sprint116ReducerSourcePath =
  "DASHI/Physics/Closure/YMSprint116CommonCarrierTransferClosureReducer.agda"

sprint108TransferAssemblySourcePath : String
sprint108TransferAssemblySourcePath =
  "DASHI/Physics/Closure/YMSprint108TransferLowerBoundAssembly.agda"

sprint109CriticalAssemblySourcePath : String
sprint109CriticalAssemblySourcePath =
  "DASHI/Physics/Closure/YMSprint109TransferLowerBoundCriticalAssembly.agda"

sprint108MoscoSourcePath : String
sprint108MoscoSourcePath =
  "DASHI/Physics/Closure/YMSprint108MoscoNoPollutionBridge.agda"

sprint109NoBottomSourcePath : String
sprint109NoBottomSourcePath =
  "DASHI/Physics/Closure/YMSprint109NoBottomSpectrumPollutionCompactness.agda"

sprint110NoCollapseSourcePath : String
sprint110NoCollapseSourcePath =
  "DASHI/Physics/Closure/YMSprint110BottomSectorThresholdNoCollapse.agda"

sprint110CarrierSourcePath : String
sprint110CarrierSourcePath =
  "DASHI/Physics/Closure/YMSprint110CommonCarrierHilbertIdentification.agda"

sprint110ClosedFormSourcePath : String
sprint110ClosedFormSourcePath =
  "DASHI/Physics/Closure/YMSprint110ClosedFormLowerSemicontinuityCriterion.agda"

sprint110RecoverySourcePath : String
sprint110RecoverySourcePath =
  "DASHI/Physics/Closure/YMSprint110RecoveryCoreDensityEnergyLimsup.agda"

sprint110WeakSourcePath : String
sprint110WeakSourcePath =
  "DASHI/Physics/Closure/YMSprint110WeakCompactnessEnergyCore.agda"

sprint108UniformFormSourcePath : String
sprint108UniformFormSourcePath =
  "DASHI/Physics/Closure/YMSprint108UniformFormLowerBound.agda"

sprint108LogGeneratorSourcePath : String
sprint108LogGeneratorSourcePath =
  "DASHI/Physics/Closure/YMSprint108LogGeneratorCalculusBridge.agda"

sprint108SpectralTransportSourcePath : String
sprint108SpectralTransportSourcePath =
  "DASHI/Physics/Closure/YMSprint108SpectralGapTransport.agda"

commonCarrierFeedThroughText : String
commonCarrierFeedThroughText =
  "Common-carrier feed-through obligation: Sprint116 must receive closed external construction, weak compactness, closed-form LSC, recovery limsup, uniform norm/residual closure, and sector stability on one carrier before transfer readiness can be true."

externalCommonCarrierConstructionText : String
externalCommonCarrierConstructionText =
  "External common-carrier construction obligation: construct the physical Hilbert carrier, finite carriers, E_a/P_a maps, gauge quotient compatibility, sector split, and norm window outside this reducer."

noBottomNoCollapseText : String
noBottomNoCollapseText =
  "No bottom pollution/no collapse obligation: exclude spurious low-energy branches, identify the isolated bottom sector, and prove non-vacuum eigenbranches cannot collapse to zero."

closedFormLSCText : String
closedFormLSCText =
  "Closed-form lower-semicontinuity obligation: prove domain identification, closedness, semiboundedness, gauge-sector preservation, and the liminf inequality in the common carrier."

recoveryLimsupText : String
recoveryLimsupText =
  "Recovery limsup obligation: prove dense finite physical core recovery, strong norm recovery, interpolation/sampling compatibility, and energy limsup."

weakCompactnessText : String
weakCompactnessText =
  "Weak compactness obligation: prove bounded-energy finite-carrier sequences admit physical weak subsequences on the same common carrier."

uniformFormLogSpectralText : String
uniformFormLogSpectralText =
  "Uniform form/log generator/spectral transport obligation: prove uniform form coercivity, logarithmic-generator functional calculus on a common core, and finite-threshold transport to the continuum physical spectrum."

failClosedReadinessText : String
failClosedReadinessText =
  "Readiness is exact and fail-closed: if any listed obligation is not externally discharged, transferLowerBoundReadyHere remains false."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint117 records the exact obligation reducer only; transfer lower-bound theorem, continuum mass gap, and Clay Yang-Mills promotion remain false."

data TransferReadinessObligation : Set where
  common-carrier-feed-through :
    TransferReadinessObligation
  external-common-carrier-construction :
    TransferReadinessObligation
  no-bottom-spectrum-pollution-no-collapse :
    TransferReadinessObligation
  closed-form-lower-semicontinuity :
    TransferReadinessObligation
  recovery-limsup :
    TransferReadinessObligation
  weak-compactness :
    TransferReadinessObligation
  uniform-form-log-generator-spectral-transport :
    TransferReadinessObligation
  theorem-nonpromotion-boundary :
    TransferReadinessObligation

data ObligationStatus : Set where
  imported-reducer-input :
    ObligationStatus
  source-path-recorded :
    ObligationStatus
  exact-obligation-recorded :
    ObligationStatus
  external-discharge-required :
    ObligationStatus
  readiness-fail-closed :
    ObligationStatus
  theorem-open :
    ObligationStatus
  nonpromotion-boundary :
    ObligationStatus

record PriorTransferReceipts : Setω where
  constructor mkPriorTransferReceipts
  field
    reducer116Receipt :
      Reducer116.YMSprint116CommonCarrierTransferClosureReducerReceipt
    transfer108Receipt :
      Transfer108.YMSprint108TransferLowerBoundAssemblyReceipt
    critical109Receipt :
      Critical109.YMSprint109TransferLowerBoundCriticalAssemblyReceipt
    imported :
      Bool
    reducer116Path :
      String
    transfer108Path :
      String
    critical109Path :
      String
    reducer116Readiness :
      Bool
    reducer116ReadinessIsFalse :
      reducer116Readiness ≡ false
    transfer108TheoremProved :
      Bool
    transfer108TheoremProvedIsFalse :
      transfer108TheoremProved ≡ false
    critical109TheoremProved :
      Bool
    critical109TheoremProvedIsFalse :
      critical109TheoremProved ≡ false

record MoscoSpectrumReceipts : Setω where
  constructor mkMoscoSpectrumReceipts
  field
    mosco108Receipt :
      Mosco108.YMSprint108MoscoNoPollutionBridgeReceipt
    compact109Receipt :
      Compact109.YMSprint109NoBottomSpectrumPollutionCompactnessReceipt
    collapse110Receipt :
      Collapse110.YMSprint110BottomSectorThresholdNoCollapseReceipt
    moscoPath :
      String
    compactPath :
      String
    collapsePath :
      String
    moscoBridgeClosed :
      Bool
    moscoBridgeClosedIsFalse :
      moscoBridgeClosed ≡ false
    noBottomPollutionClosed :
      Bool
    noBottomPollutionClosedIsFalse :
      noBottomPollutionClosed ≡ false
    noCollapseClosed :
      Bool
    noCollapseClosedIsFalse :
      noCollapseClosed ≡ false

record CarrierAnalyticReceipts : Setω where
  constructor mkCarrierAnalyticReceipts
  field
    carrier110Receipt :
      Carrier110.YMSprint110CommonCarrierHilbertIdentificationReceipt
    closed110Receipt :
      Closed110.YMSprint110ClosedFormLowerSemicontinuityCriterionReceipt
    recovery110Receipt :
      Recovery110.YMSprint110RecoveryCoreDensityEnergyLimsupReceipt
    weak110Receipt :
      Weak110.YMSprint110WeakCompactnessEnergyCoreReceipt
    carrierPath :
      String
    closedPath :
      String
    recoveryPath :
      String
    weakPath :
      String
    commonCarrierRecorded :
      Bool
    closedFormClosed :
      Bool
    closedFormClosedIsFalse :
      closedFormClosed ≡ false
    recoveryClosed :
      Bool
    recoveryClosedIsFalse :
      recoveryClosed ≡ false
    weakCompactnessClosed :
      Bool
    weakCompactnessClosedIsFalse :
      weakCompactnessClosed ≡ false

record TransportAnalyticReceipts : Setω where
  constructor mkTransportAnalyticReceipts
  field
    uniformForm108Receipt :
      Form108.YMSprint108UniformFormLowerBoundReceipt
    logGenerator108Receipt :
      Log108.YMSprint108LogGeneratorCalculusBridgeReceipt
    spectral108Receipt :
      Spectral108.YMSprint108SpectralGapTransportReceipt
    uniformFormPath :
      String
    logGeneratorPath :
      String
    spectralTransportPath :
      String
    uniformFormClosed :
      Bool
    uniformFormClosedIsFalse :
      uniformFormClosed ≡ false
    logGeneratorClosed :
      Bool
    logGeneratorClosedIsFalse :
      logGeneratorClosed ≡ false
    spectralTransportClosed :
      Bool
    spectralTransportClosedIsFalse :
      spectralTransportClosed ≡ false

record ObligationRow : Set where
  constructor mkObligationRow
  field
    obligation :
      TransferReadinessObligation
    status :
      ObligationStatus
    sourcePath :
      String
    evidenceString :
      String
    importedEvidence :
      Bool
    requiredForReadiness :
      Bool
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false

record ReadinessExactness : Set where
  constructor mkReadinessExactness
  field
    rowCount :
      Nat
    rows :
      List ObligationRow
    exactReducerStatement :
      String
    allRequired :
      Bool
    allDischargedHere :
      Bool
    allDischargedHereIsFalse :
      allDischargedHere ≡ false
    transferLowerBoundReady :
      Bool
    transferLowerBoundReadyIsFalse :
      transferLowerBoundReady ≡ false
    status :
      ObligationStatus

record FinalTheoremBoundary : Set where
  constructor mkFinalTheoremBoundary
  field
    boundaryStatement :
      String
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
      ObligationStatus

record YMSprint117TransferReadinessObligationReducerReceipt : Setω where
  constructor mkYMSprint117TransferReadinessObligationReducerReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    priorTransferReceipts :
      PriorTransferReceipts
    moscoSpectrumReceipts :
      MoscoSpectrumReceipts
    carrierAnalyticReceipts :
      CarrierAnalyticReceipts
    transportAnalyticReceipts :
      TransportAnalyticReceipts
    obligationRows :
      List ObligationRow
    readinessExactness :
      ReadinessExactness
    theoremBoundary :
      FinalTheoremBoundary
    sourcePaths :
      List String
    evidenceLedger :
      List String
    receiptRecorded :
      Bool
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open YMSprint117TransferReadinessObligationReducerReceipt public

canonicalPriorTransferReceipts : PriorTransferReceipts
canonicalPriorTransferReceipts =
  mkPriorTransferReceipts
    Reducer116.canonicalReceipt
    Transfer108.canonicalYMSprint108TransferLowerBoundAssemblyReceipt
    Critical109.canonicalReceipt
    true
    sprint116ReducerSourcePath
    sprint108TransferAssemblySourcePath
    sprint109CriticalAssemblySourcePath
    Reducer116.transferLowerBoundReadyHere
    refl
    Transfer108.transferLowerBoundTheoremProvedHere
    refl
    Critical109.transferLowerBoundTheoremProvedHere
    refl

canonicalMoscoSpectrumReceipts : MoscoSpectrumReceipts
canonicalMoscoSpectrumReceipts =
  mkMoscoSpectrumReceipts
    Mosco108.canonicalReceipt
    Compact109.canonicalReceipt
    Collapse110.canonicalReceipt
    sprint108MoscoSourcePath
    sprint109NoBottomSourcePath
    sprint110NoCollapseSourcePath
    moscoNoPollutionBridgeClosedHere
    refl
    noBottomSpectrumPollutionClosedHere
    refl
    noCollapseAtZeroClosedHere
    refl

canonicalCarrierAnalyticReceipts : CarrierAnalyticReceipts
canonicalCarrierAnalyticReceipts =
  mkCarrierAnalyticReceipts
    Carrier110.canonicalReceipt
    Closed110.canonicalReceipt
    Recovery110.canonicalReceipt
    Weak110.canonicalReceipt
    sprint110CarrierSourcePath
    sprint110ClosedFormSourcePath
    sprint110RecoverySourcePath
    sprint110WeakSourcePath
    Carrier110.commonCarrierReceiptRecorded
    closedFormLowerSemicontinuityClosedHere
    refl
    recoveryLimsupClosedHere
    refl
    weakCompactnessClosedHere
    refl

canonicalTransportAnalyticReceipts : TransportAnalyticReceipts
canonicalTransportAnalyticReceipts =
  mkTransportAnalyticReceipts
    Form108.canonicalReceipt
    Log108.canonicalReceipt
    Spectral108.canonicalReceipt
    sprint108UniformFormSourcePath
    sprint108LogGeneratorSourcePath
    sprint108SpectralTransportSourcePath
    uniformFormLowerBoundClosedHere
    refl
    logGeneratorCalculusClosedHere
    refl
    spectralTransportClosedHere
    refl

commonCarrierFeedThroughRow : ObligationRow
commonCarrierFeedThroughRow =
  mkObligationRow
    common-carrier-feed-through
    external-discharge-required
    sprint116ReducerSourcePath
    commonCarrierFeedThroughText
    true
    true
    commonCarrierFeedThroughClosedHere
    refl

externalCommonCarrierConstructionRow : ObligationRow
externalCommonCarrierConstructionRow =
  mkObligationRow
    external-common-carrier-construction
    external-discharge-required
    sprint110CarrierSourcePath
    externalCommonCarrierConstructionText
    true
    true
    externalCommonCarrierConstructionClosedHere
    refl

noBottomNoCollapseRow : ObligationRow
noBottomNoCollapseRow =
  mkObligationRow
    no-bottom-spectrum-pollution-no-collapse
    external-discharge-required
    sprint110NoCollapseSourcePath
    noBottomNoCollapseText
    true
    true
    noCollapseAtZeroClosedHere
    refl

closedFormLSCRow : ObligationRow
closedFormLSCRow =
  mkObligationRow
    closed-form-lower-semicontinuity
    external-discharge-required
    sprint110ClosedFormSourcePath
    closedFormLSCText
    true
    true
    closedFormLowerSemicontinuityClosedHere
    refl

recoveryLimsupRow : ObligationRow
recoveryLimsupRow =
  mkObligationRow
    recovery-limsup
    external-discharge-required
    sprint110RecoverySourcePath
    recoveryLimsupText
    true
    true
    recoveryLimsupClosedHere
    refl

weakCompactnessRow : ObligationRow
weakCompactnessRow =
  mkObligationRow
    weak-compactness
    external-discharge-required
    sprint110WeakSourcePath
    weakCompactnessText
    true
    true
    weakCompactnessClosedHere
    refl

uniformFormLogSpectralRow : ObligationRow
uniformFormLogSpectralRow =
  mkObligationRow
    uniform-form-log-generator-spectral-transport
    external-discharge-required
    sprint108SpectralTransportSourcePath
    uniformFormLogSpectralText
    true
    true
    spectralTransportClosedHere
    refl

theoremBoundaryRow : ObligationRow
theoremBoundaryRow =
  mkObligationRow
    theorem-nonpromotion-boundary
    nonpromotion-boundary
    modulePath
    nonPromotionBoundaryText
    true
    true
    transferLowerBoundTheoremProvedHere
    refl

canonicalObligationRows : List ObligationRow
canonicalObligationRows =
  commonCarrierFeedThroughRow
  ∷ externalCommonCarrierConstructionRow
  ∷ noBottomNoCollapseRow
  ∷ closedFormLSCRow
  ∷ recoveryLimsupRow
  ∷ weakCompactnessRow
  ∷ uniformFormLogSpectralRow
  ∷ theoremBoundaryRow
  ∷ []

canonicalReadinessExactness : ReadinessExactness
canonicalReadinessExactness =
  mkReadinessExactness
    8
    canonicalObligationRows
    failClosedReadinessText
    true
    allObligationsDischargedHere
    refl
    transferLowerBoundReadyHere
    refl
    readiness-fail-closed

canonicalFinalTheoremBoundary : FinalTheoremBoundary
canonicalFinalTheoremBoundary =
  mkFinalTheoremBoundary
    nonPromotionBoundaryText
    transferLowerBoundTheoremProvedHere
    refl
    continuumMassGapProvedHere
    refl
    clayYangMillsPromoted
    refl
    theorem-open

canonicalSourcePaths : List String
canonicalSourcePaths =
  modulePath
  ∷ sprint116ReducerSourcePath
  ∷ sprint108TransferAssemblySourcePath
  ∷ sprint109CriticalAssemblySourcePath
  ∷ sprint108MoscoSourcePath
  ∷ sprint109NoBottomSourcePath
  ∷ sprint110NoCollapseSourcePath
  ∷ sprint110CarrierSourcePath
  ∷ sprint110ClosedFormSourcePath
  ∷ sprint110RecoverySourcePath
  ∷ sprint110WeakSourcePath
  ∷ sprint108UniformFormSourcePath
  ∷ sprint108LogGeneratorSourcePath
  ∷ sprint108SpectralTransportSourcePath
  ∷ []

canonicalEvidenceLedger : List String
canonicalEvidenceLedger =
  commonCarrierFeedThroughText
  ∷ externalCommonCarrierConstructionText
  ∷ noBottomNoCollapseText
  ∷ closedFormLSCText
  ∷ recoveryLimsupText
  ∷ weakCompactnessText
  ∷ uniformFormLogSpectralText
  ∷ failClosedReadinessText
  ∷ nonPromotionBoundaryText
  ∷ []

canonicalYMSprint117TransferReadinessObligationReducerReceipt :
  YMSprint117TransferReadinessObligationReducerReceipt
canonicalYMSprint117TransferReadinessObligationReducerReceipt =
  mkYMSprint117TransferReadinessObligationReducerReceipt
    sprintNumber
    modulePath
    canonicalPriorTransferReceipts
    canonicalMoscoSpectrumReceipts
    canonicalCarrierAnalyticReceipts
    canonicalTransportAnalyticReceipts
    canonicalObligationRows
    canonicalReadinessExactness
    canonicalFinalTheoremBoundary
    canonicalSourcePaths
    canonicalEvidenceLedger
    transferReadinessObligationReducerRecorded
    clayYangMillsPromoted
    refl

canonicalReceipt :
  YMSprint117TransferReadinessObligationReducerReceipt
canonicalReceipt =
  canonicalYMSprint117TransferReadinessObligationReducerReceipt

finalReceipt :
  YMSprint117TransferReadinessObligationReducerReceipt
finalReceipt =
  canonicalReceipt

canonicalReceiptTransferReadinessIsFalse :
  transferLowerBoundReadyHere ≡ false
canonicalReceiptTransferReadinessIsFalse =
  refl

canonicalReceiptAllObligationsDischargedHereIsFalse :
  allObligationsDischargedHere ≡ false
canonicalReceiptAllObligationsDischargedHereIsFalse =
  refl

canonicalReceiptCommonCarrierFeedThroughClosedHereIsFalse :
  commonCarrierFeedThroughClosedHere ≡ false
canonicalReceiptCommonCarrierFeedThroughClosedHereIsFalse =
  refl

canonicalReceiptExternalCommonCarrierConstructionClosedHereIsFalse :
  externalCommonCarrierConstructionClosedHere ≡ false
canonicalReceiptExternalCommonCarrierConstructionClosedHereIsFalse =
  refl

canonicalReceiptNoBottomSpectrumPollutionClosedHereIsFalse :
  noBottomSpectrumPollutionClosedHere ≡ false
canonicalReceiptNoBottomSpectrumPollutionClosedHereIsFalse =
  refl

canonicalReceiptNoCollapseAtZeroClosedHereIsFalse :
  noCollapseAtZeroClosedHere ≡ false
canonicalReceiptNoCollapseAtZeroClosedHereIsFalse =
  refl

canonicalReceiptClosedFormLowerSemicontinuityClosedHereIsFalse :
  closedFormLowerSemicontinuityClosedHere ≡ false
canonicalReceiptClosedFormLowerSemicontinuityClosedHereIsFalse =
  refl

canonicalReceiptRecoveryLimsupClosedHereIsFalse :
  recoveryLimsupClosedHere ≡ false
canonicalReceiptRecoveryLimsupClosedHereIsFalse =
  refl

canonicalReceiptWeakCompactnessClosedHereIsFalse :
  weakCompactnessClosedHere ≡ false
canonicalReceiptWeakCompactnessClosedHereIsFalse =
  refl

canonicalReceiptUniformFormLowerBoundClosedHereIsFalse :
  uniformFormLowerBoundClosedHere ≡ false
canonicalReceiptUniformFormLowerBoundClosedHereIsFalse =
  refl

canonicalReceiptLogGeneratorCalculusClosedHereIsFalse :
  logGeneratorCalculusClosedHere ≡ false
canonicalReceiptLogGeneratorCalculusClosedHereIsFalse =
  refl

canonicalReceiptSpectralTransportClosedHereIsFalse :
  spectralTransportClosedHere ≡ false
canonicalReceiptSpectralTransportClosedHereIsFalse =
  refl

canonicalReceiptTransferLowerBoundTheoremProvedHereIsFalse :
  transferLowerBoundTheoremProvedHere ≡ false
canonicalReceiptTransferLowerBoundTheoremProvedHereIsFalse =
  refl

canonicalReceiptContinuumMassGapProvedHereIsFalse :
  continuumMassGapProvedHere ≡ false
canonicalReceiptContinuumMassGapProvedHereIsFalse =
  refl

canonicalReceiptClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalReceiptClayYangMillsPromotedIsFalse =
  refl
