module DASHI.Physics.Closure.YMSprint119WeakCompactnessObligationReducer where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint118MoscoCompactnessReadinessAggregator
  as Readiness118
import DASHI.Physics.Closure.YMSprint110WeakCompactnessEnergyCore
  as Weak110
import DASHI.Physics.Closure.YMSprint109NoBottomSpectrumPollutionCompactness
  as Compact109
import DASHI.Physics.Closure.YMSprint110CommonCarrierHilbertIdentification
  as Carrier110

------------------------------------------------------------------------
-- Sprint119 weak-compactness obligation reducer.
--
-- This module reduces the still-open weak compactness lane to the exact
-- inputs that must be supplied before the Sprint118 Mosco/form package can
-- close its compactness half. Weak compactness is treated only as a Mosco
-- liminf input: it does not by itself close the corrected continuum-transfer
-- chain, does not imply H3a or H3b, and does not imply no-spectral-pollution.
-- The reducer rows and assembly receipts are true, while every theorem and
-- promotion gate remains false.

sprintNumber : Nat
sprintNumber = 119

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint119WeakCompactnessObligationReducer.agda"

reducerInhabitedHere : Bool
reducerInhabitedHere = true

assembledHere : Bool
assembledHere = true

rowFlagsTrueHere : Bool
rowFlagsTrueHere = true

weakCompactnessClosedHere : Bool
weakCompactnessClosedHere = false

allMoscoCompactnessObligationsClosedHere : Bool
allMoscoCompactnessObligationsClosedHere = false

transferLowerBoundReadyHere : Bool
transferLowerBoundReadyHere = false

transferLowerBoundTheoremProvedHere : Bool
transferLowerBoundTheoremProvedHere = false

continuumMassGapProvedHere : Bool
continuumMassGapProvedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

readiness118SourcePath : String
readiness118SourcePath =
  "DASHI/Physics/Closure/YMSprint118MoscoCompactnessReadinessAggregator.agda"

weak110SourcePath : String
weak110SourcePath =
  "DASHI/Physics/Closure/YMSprint110WeakCompactnessEnergyCore.agda"

compact109SourcePath : String
compact109SourcePath =
  "DASHI/Physics/Closure/YMSprint109NoBottomSpectrumPollutionCompactness.agda"

carrier110SourcePath : String
carrier110SourcePath =
  "DASHI/Physics/Closure/YMSprint110CommonCarrierHilbertIdentification.agda"

correctedTransferBoundarySourcePath : String
correctedTransferBoundarySourcePath =
  "DASHI/Physics/Closure/YMBruhatTitsToOSLatticeTransferBoundary.agda"

boundaryDownstreamH3aStillOpen : Bool
boundaryDownstreamH3aStillOpen = false

boundaryDownstreamH3bStillOpen : Bool
boundaryDownstreamH3bStillOpen = false

boundaryDownstreamNoSpectralPollutionStillOpen : Bool
boundaryDownstreamNoSpectralPollutionStillOpen = false

reducerStatementText : String
reducerStatementText =
  "Sprint119 reduces weak compactness to six exact inputs for the compactness half of Mosco/form convergence: bounded-energy tightness, common carrier Hilbert identification, subsequence extraction, gauge quotient sector compatibility, no escape to the null sector, and feed-through into Mosco liminf."

boundedEnergyTightnessText : String
boundedEnergyTightnessText =
  "Bounded-energy tightness input: normalized finite physical vectors with a uniform transfer-form energy ceiling must have uniformly controlled tails, gauge leakage, cutoff-interface residuals, and carrier-identification residuals."

commonCarrierHilbertIdentificationText : String
commonCarrierHilbertIdentificationText =
  "Common carrier Hilbert identification input: finite physical quotient carriers and the continuum physical Hilbert carrier must be compared through one embedding/projection convention shared by liminf and recovery."

subsequenceExtractionText : String
subsequenceExtractionText =
  "Subsequence extraction input: bounded tight finite-carrier branches must admit a weakly convergent subsequence after transport to the common physical carrier."

gaugeQuotientSectorCompatibilityText : String
gaugeQuotientSectorCompatibilityText =
  "Gauge quotient sector compatibility input: the extraction, embedding, and projection surfaces must respect physical projection, gauge quotienting, and the vacuum/non-vacuum split."

noEscapeToNullSectorText : String
noEscapeToNullSectorText =
  "No escape to null sector input: non-vacuum low-energy branches must not converge to the null or collapsed bottom sector during compact extraction."

moscoLiminfFeedThroughText : String
moscoLiminfFeedThroughText =
  "Mosco liminf feed-through input: the extracted weak limit must be a valid continuum form-domain candidate for the closed-form lower semicontinuity lane. This is only the compactness half of Mosco/form convergence and does not by itself imply H3a transfer convergence, H3b vacuum-projection continuity, or no-spectral-pollution."

downstreamH3aBoundaryText : String
downstreamH3aBoundaryText =
  "Downstream H3a boundary: after weak compactness and the rest of the Mosco package, the corrected continuum-transfer route still requires transfer-matrix or norm-resolvent convergence on the vacuum-orthogonal sector."

downstreamH3bBoundaryText : String
downstreamH3bBoundaryText =
  "Downstream H3b boundary: after weak compactness and the rest of the Mosco package, the corrected continuum-transfer route still requires RP.4-compatible vacuum-projection continuity for the limiting vacuum."

downstreamNoSpectralPollutionBoundaryText : String
downstreamNoSpectralPollutionBoundaryText =
  "Downstream no-spectral-pollution boundary: weak compactness feeds Mosco liminf only; exclusion of spurious low spectrum is recorded only after H3a and H3b, not from compactness alone."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint119 assembles the weak-compactness reducer only. Weak compactness is upstream evidence for Mosco liminf and form convergence only; it does not by itself close the corrected continuum-transfer step. H3a transfer convergence, H3b vacuum-projection continuity, no-spectral-pollution, transfer lower-bound readiness, transfer lower-bound theorem, continuum mass gap, and Clay Yang-Mills promotion remain false."

data WeakCompactnessInput : Set where
  bounded-energy-tightness :
    WeakCompactnessInput
  common-carrier-hilbert-identification :
    WeakCompactnessInput
  subsequence-extraction :
    WeakCompactnessInput
  gauge-quotient-sector-compatibility :
    WeakCompactnessInput
  no-escape-to-null-sector :
    WeakCompactnessInput
  mosco-liminf-feed-through :
    WeakCompactnessInput

data ReducerStatus : Set where
  imported-receipt :
    ReducerStatus
  exact-input-recorded :
    ReducerStatus
  assembled-reducer-row :
    ReducerStatus
  upstream-open :
    ReducerStatus
  feed-through-recorded :
    ReducerStatus
  fail-closed-nonpromotion :
    ReducerStatus

record ImportedWeakCompactnessReceipts : Setω where
  constructor mkImportedWeakCompactnessReceipts
  field
    readiness118Receipt :
      Readiness118.YMSprint118MoscoCompactnessReadinessAggregatorReceipt
    weak110Receipt :
      Weak110.YMSprint110WeakCompactnessEnergyCoreReceipt
    compact109Receipt :
      Compact109.YMSprint109NoBottomSpectrumPollutionCompactnessReceipt
    carrier110Receipt :
      Carrier110.YMSprint110CommonCarrierHilbertIdentificationReceipt
    readiness118Path :
      String
    weak110Path :
      String
    compact109Path :
      String
    carrier110Path :
      String
    allImported :
      Bool
    readinessWeakCompactnessClosedFlag :
      Bool
    readinessWeakCompactnessClosedFlagIsFalse :
      readinessWeakCompactnessClosedFlag ≡ false
    weakSubsequenceExtractionProvedFlag :
      Bool
    weakSubsequenceExtractionProvedFlagIsFalse :
      weakSubsequenceExtractionProvedFlag ≡ false
    noBottomPollutionCompactnessProvedFlag :
      Bool
    noBottomPollutionCompactnessProvedFlagIsFalse :
      noBottomPollutionCompactnessProvedFlag ≡ false
    commonCarrierClosedFlag :
      Bool
    commonCarrierClosedFlagIsFalse :
      commonCarrierClosedFlag ≡ false

record ReducerInputRow : Set where
  constructor mkReducerInputRow
  field
    input :
      WeakCompactnessInput
    statement :
      String
    sourcePath :
      String
    importedEvidence :
      Bool
    rowRecorded :
      Bool
    rowRecordedIsTrue :
      rowRecorded ≡ true
    requiredForWeakCompactness :
      Bool
    upstreamClosedFlag :
      Bool
    upstreamClosedFlagIsFalse :
      upstreamClosedFlag ≡ false
    status :
      ReducerStatus

record WeakCompactnessReducer : Set where
  constructor mkWeakCompactnessReducer
  field
    statement :
      String
    boundedEnergyTightness :
      ReducerInputRow
    commonCarrierHilbertIdentification :
      ReducerInputRow
    subsequenceExtraction :
      ReducerInputRow
    gaugeQuotientSectorCompatibility :
      ReducerInputRow
    noEscapeToNullSector :
      ReducerInputRow
    moscoLiminfFeedThrough :
      ReducerInputRow
    rows :
      List ReducerInputRow
    rowCount :
      Nat
    reducerInhabited :
      Bool
    reducerInhabitedIsTrue :
      reducerInhabited ≡ true
    assembled :
      Bool
    assembledIsTrue :
      assembled ≡ true
    rowFlagsTrue :
      Bool
    rowFlagsTrueIsTrue :
      rowFlagsTrue ≡ true
    weakCompactnessClosed :
      Bool
    weakCompactnessClosedIsFalse :
      weakCompactnessClosed ≡ false

record MoscoFeedThroughBoundary : Set where
  constructor mkMoscoFeedThroughBoundary
  field
    statement :
      String
    readiness118WeakCompactnessClosed :
      Bool
    readiness118WeakCompactnessClosedIsFalse :
      readiness118WeakCompactnessClosed ≡ false
    readiness118AllMoscoObligationsClosed :
      Bool
    readiness118AllMoscoObligationsClosedIsFalse :
      readiness118AllMoscoObligationsClosed ≡ false
    weak110MoscoLiminfFed :
      Bool
    weak110MoscoLiminfFedIsFalse :
      weak110MoscoLiminfFed ≡ false
    correctedTransferBoundaryPath :
      String
    downstreamH3aStillOpen :
      Bool
    downstreamH3aStillOpenIsFalse :
      downstreamH3aStillOpen ≡ false
    downstreamH3bStillOpen :
      Bool
    downstreamH3bStillOpenIsFalse :
      downstreamH3bStillOpen ≡ false
    downstreamNoSpectralPollutionStillOpen :
      Bool
    downstreamNoSpectralPollutionStillOpenIsFalse :
      downstreamNoSpectralPollutionStillOpen ≡ false
    transferLowerBoundReady :
      Bool
    transferLowerBoundReadyIsFalse :
      transferLowerBoundReady ≡ false

record TheoremAndPromotionBoundary : Set where
  constructor mkTheoremAndPromotionBoundary
  field
    statement :
      String
    weakCompactnessClosed :
      Bool
    weakCompactnessClosedIsFalse :
      weakCompactnessClosed ≡ false
    allMoscoCompactnessObligationsClosed :
      Bool
    allMoscoCompactnessObligationsClosedIsFalse :
      allMoscoCompactnessObligationsClosed ≡ false
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

record YMSprint119WeakCompactnessObligationReducerReceipt : Setω where
  constructor mkYMSprint119WeakCompactnessObligationReducerReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    importedReceipts :
      ImportedWeakCompactnessReceipts
    reducer :
      WeakCompactnessReducer
    moscoFeedThroughBoundary :
      MoscoFeedThroughBoundary
    theoremAndPromotionBoundary :
      TheoremAndPromotionBoundary
    sourcePaths :
      List String
    evidenceLedger :
      List String
    receiptRecorded :
      Bool
    reducerInhabitedHereFlag :
      Bool
    reducerInhabitedHereFlagIsTrue :
      reducerInhabitedHereFlag ≡ true
    assembledHereFlag :
      Bool
    assembledHereFlagIsTrue :
      assembledHereFlag ≡ true
    rowFlagsTrueHereFlag :
      Bool
    rowFlagsTrueHereFlagIsTrue :
      rowFlagsTrueHereFlag ≡ true
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open YMSprint119WeakCompactnessObligationReducerReceipt public

canonicalImportedWeakCompactnessReceipts :
  ImportedWeakCompactnessReceipts
canonicalImportedWeakCompactnessReceipts =
  mkImportedWeakCompactnessReceipts
    Readiness118.canonicalReceipt
    Weak110.canonicalReceipt
    Compact109.canonicalReceipt
    Carrier110.canonicalReceipt
    readiness118SourcePath
    weak110SourcePath
    compact109SourcePath
    carrier110SourcePath
    true
    Readiness118.weakCompactnessClosedHere
    refl
    Weak110.weakSubsequenceExtractionProvedHere
    refl
    Compact109.noBottomSpectrumPollutionCompactnessTheoremProved
    refl
    (Carrier110.commonCarrierClosedHere Carrier110.canonicalReceipt)
    refl

boundedEnergyTightnessRow : ReducerInputRow
boundedEnergyTightnessRow =
  mkReducerInputRow
    bounded-energy-tightness
    boundedEnergyTightnessText
    weak110SourcePath
    true
    true
    refl
    true
    Weak110.tightnessAloneEnoughForMoscoLiminf
    refl
    exact-input-recorded

commonCarrierHilbertIdentificationRow : ReducerInputRow
commonCarrierHilbertIdentificationRow =
  mkReducerInputRow
    common-carrier-hilbert-identification
    commonCarrierHilbertIdentificationText
    carrier110SourcePath
    true
    true
    refl
    true
    (Carrier110.commonCarrierClosedHere Carrier110.canonicalReceipt)
    refl
    upstream-open

subsequenceExtractionRow : ReducerInputRow
subsequenceExtractionRow =
  mkReducerInputRow
    subsequence-extraction
    subsequenceExtractionText
    weak110SourcePath
    true
    true
    refl
    true
    Weak110.weakSubsequenceExtractionProvedHere
    refl
    upstream-open

gaugeQuotientSectorCompatibilityRow : ReducerInputRow
gaugeQuotientSectorCompatibilityRow =
  mkReducerInputRow
    gauge-quotient-sector-compatibility
    gaugeQuotientSectorCompatibilityText
    carrier110SourcePath
    true
    true
    refl
    true
    Carrier110.gaugeQuotientCompatibilityProvedHere
    refl
    exact-input-recorded

noEscapeToNullSectorRow : ReducerInputRow
noEscapeToNullSectorRow =
  mkReducerInputRow
    no-escape-to-null-sector
    noEscapeToNullSectorText
    compact109SourcePath
    true
    true
    refl
    true
    Compact109.noCollapseAtZeroProvedHere
    refl
    upstream-open

moscoLiminfFeedThroughRow : ReducerInputRow
moscoLiminfFeedThroughRow =
  mkReducerInputRow
    mosco-liminf-feed-through
    moscoLiminfFeedThroughText
    weak110SourcePath
    true
    true
    refl
    true
    Weak110.moscoLiminfFedHere
    refl
    feed-through-recorded

canonicalReducerRows : List ReducerInputRow
canonicalReducerRows =
  boundedEnergyTightnessRow
  ∷ commonCarrierHilbertIdentificationRow
  ∷ subsequenceExtractionRow
  ∷ gaugeQuotientSectorCompatibilityRow
  ∷ noEscapeToNullSectorRow
  ∷ moscoLiminfFeedThroughRow
  ∷ []

canonicalWeakCompactnessReducer : WeakCompactnessReducer
canonicalWeakCompactnessReducer =
  mkWeakCompactnessReducer
    reducerStatementText
    boundedEnergyTightnessRow
    commonCarrierHilbertIdentificationRow
    subsequenceExtractionRow
    gaugeQuotientSectorCompatibilityRow
    noEscapeToNullSectorRow
    moscoLiminfFeedThroughRow
    canonicalReducerRows
    6
    reducerInhabitedHere
    refl
    assembledHere
    refl
    rowFlagsTrueHere
    refl
    weakCompactnessClosedHere
    refl

canonicalMoscoFeedThroughBoundary : MoscoFeedThroughBoundary
canonicalMoscoFeedThroughBoundary =
  mkMoscoFeedThroughBoundary
    moscoLiminfFeedThroughText
    Readiness118.weakCompactnessClosedHere
    refl
    Readiness118.allMoscoCompactnessObligationsClosedHere
    refl
    Weak110.moscoLiminfFedHere
    refl
    correctedTransferBoundarySourcePath
    boundaryDownstreamH3aStillOpen
    refl
    boundaryDownstreamH3bStillOpen
    refl
    boundaryDownstreamNoSpectralPollutionStillOpen
    refl
    transferLowerBoundReadyHere
    refl

canonicalTheoremAndPromotionBoundary : TheoremAndPromotionBoundary
canonicalTheoremAndPromotionBoundary =
  mkTheoremAndPromotionBoundary
    nonPromotionBoundaryText
    weakCompactnessClosedHere
    refl
    allMoscoCompactnessObligationsClosedHere
    refl
    transferLowerBoundReadyHere
    refl
    transferLowerBoundTheoremProvedHere
    refl
    continuumMassGapProvedHere
    refl
    clayYangMillsPromoted
    refl

canonicalSourcePaths : List String
canonicalSourcePaths =
  modulePath
  ∷ readiness118SourcePath
  ∷ weak110SourcePath
  ∷ compact109SourcePath
  ∷ carrier110SourcePath
  ∷ correctedTransferBoundarySourcePath
  ∷ []

canonicalEvidenceLedger : List String
canonicalEvidenceLedger =
  reducerStatementText
  ∷ boundedEnergyTightnessText
  ∷ commonCarrierHilbertIdentificationText
  ∷ subsequenceExtractionText
  ∷ gaugeQuotientSectorCompatibilityText
  ∷ noEscapeToNullSectorText
  ∷ moscoLiminfFeedThroughText
  ∷ downstreamH3aBoundaryText
  ∷ downstreamH3bBoundaryText
  ∷ downstreamNoSpectralPollutionBoundaryText
  ∷ nonPromotionBoundaryText
  ∷ []

canonicalYMSprint119WeakCompactnessObligationReducerReceipt :
  YMSprint119WeakCompactnessObligationReducerReceipt
canonicalYMSprint119WeakCompactnessObligationReducerReceipt =
  mkYMSprint119WeakCompactnessObligationReducerReceipt
    sprintNumber
    modulePath
    canonicalImportedWeakCompactnessReceipts
    canonicalWeakCompactnessReducer
    canonicalMoscoFeedThroughBoundary
    canonicalTheoremAndPromotionBoundary
    canonicalSourcePaths
    canonicalEvidenceLedger
    true
    reducerInhabitedHere
    refl
    assembledHere
    refl
    rowFlagsTrueHere
    refl
    clayYangMillsPromoted
    refl

canonicalReceipt :
  YMSprint119WeakCompactnessObligationReducerReceipt
canonicalReceipt =
  canonicalYMSprint119WeakCompactnessObligationReducerReceipt

finalReceiptAlias :
  YMSprint119WeakCompactnessObligationReducerReceipt
finalReceiptAlias =
  canonicalReceipt

canonicalReceiptReducerInhabitedHereIsTrue :
  reducerInhabitedHereFlag canonicalReceipt ≡ true
canonicalReceiptReducerInhabitedHereIsTrue =
  refl

canonicalReceiptAssembledHereIsTrue :
  assembledHereFlag canonicalReceipt ≡ true
canonicalReceiptAssembledHereIsTrue =
  refl

canonicalReceiptRowFlagsTrueHereIsTrue :
  rowFlagsTrueHereFlag canonicalReceipt ≡ true
canonicalReceiptRowFlagsTrueHereIsTrue =
  refl

canonicalReceiptWeakCompactnessClosedHereIsFalse :
  weakCompactnessClosedHere ≡ false
canonicalReceiptWeakCompactnessClosedHereIsFalse =
  refl

canonicalReceiptAllMoscoCompactnessObligationsClosedHereIsFalse :
  allMoscoCompactnessObligationsClosedHere ≡ false
canonicalReceiptAllMoscoCompactnessObligationsClosedHereIsFalse =
  refl

canonicalReceiptTransferLowerBoundReadyHereIsFalse :
  transferLowerBoundReadyHere ≡ false
canonicalReceiptTransferLowerBoundReadyHereIsFalse =
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
