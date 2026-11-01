module DASHI.Physics.QFT.SU2LevelMismatchResolutionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- SU(2) level-mismatch resolution receipt.
--
-- This receipt records a candidate resolution of the p3-lane SU(2)_3 versus
-- Standard Model SU(2)_1 mismatch by the Chern-Simons one-loop shifted level
-- convention k_eff = k - h_vee.  For SU(2), h_vee = 2, so the p3-lane
-- candidate k=3 gives k_eff=1.
--
-- The Witten/Chern-Simons level-shift entry is a citation-authority statement
-- only.  It does not promote an exact SU2_L carrier, exact Standard Model
-- match, or exact G_DHR ~= G_SM identification.

data SU2LevelSource : Set where
  p3LaneSU2Three :
    SU2LevelSource

  standardModelSU2One :
    SU2LevelSource

data SU2LevelMismatchStatus : Set where
  unresolvedBeforeShift :
    SU2LevelMismatchStatus

  candidateResolvedByCSShift :
    SU2LevelMismatchStatus

data CSLevelShiftConvention : Set where
  wittenOneLoopDualCoxeterShift :
    CSLevelShiftConvention

data CSLevelShiftAuthorityCitation : Set where
  wittenChernSimonsJonesAuthority :
    CSLevelShiftAuthorityCitation

canonicalCSLevelShiftAuthorityCitations :
  List CSLevelShiftAuthorityCitation
canonicalCSLevelShiftAuthorityCitations =
  wittenChernSimonsJonesAuthority
  ∷ []

record SU2LevelReading : Set where
  field
    source :
      SU2LevelSource

    recordedLevel :
      Nat

    sourceLabel :
      String

open SU2LevelReading public

p3LaneSU2Level3Reading :
  SU2LevelReading
p3LaneSU2Level3Reading =
  record
    { source =
        p3LaneSU2Three
    ; recordedLevel =
        3
    ; sourceLabel =
        "p3-lane SU(2)_3 candidate"
    }

standardModelSU2Level1Reading :
  SU2LevelReading
standardModelSU2Level1Reading =
  record
    { source =
        standardModelSU2One
    ; recordedLevel =
        1
    ; sourceLabel =
        "Standard Model SU(2)_1 weak candidate"
    }

canonicalSU2LevelMismatchReadings :
  List SU2LevelReading
canonicalSU2LevelMismatchReadings =
  p3LaneSU2Level3Reading
  ∷ standardModelSU2Level1Reading
  ∷ []

su2DualCoxeterNumber :
  Nat
su2DualCoxeterNumber =
  2

p3LaneChernSimonsBareLevel :
  Nat
p3LaneChernSimonsBareLevel =
  3

p3LaneShiftedEffectiveLevel :
  Nat
p3LaneShiftedEffectiveLevel =
  1

csLevelShiftFormulaLabel :
  String
csLevelShiftFormulaLabel =
  "k_eff = k - h_vee"

su2ShiftComputationLabel :
  String
su2ShiftComputationLabel =
  "for SU(2), h_vee=2 and p3 k=3 gives k_eff=3-2=1"

su2LevelMismatchLabel :
  String
su2LevelMismatchLabel =
  "p3-lane SU(2)_3 and Standard Model SU(2)_1 are mismatched before the candidate CS level shift"

wittenCSLevelShiftAuthorityLabel :
  String
wittenCSLevelShiftAuthorityLabel =
  "Witten/Chern-Simons authority records the quantum level shift by the dual Coxeter number; used here as citation authority only"

noExactPromotionLabel :
  String
noExactPromotionLabel =
  "exact SU2_L, Standard Model, and G_DHR ~= G_SM promotion flags remain false"

canonicalSU2LevelMismatchResolutionBoundary :
  List String
canonicalSU2LevelMismatchResolutionBoundary =
  su2LevelMismatchLabel
  ∷ csLevelShiftFormulaLabel
  ∷ su2ShiftComputationLabel
  ∷ wittenCSLevelShiftAuthorityLabel
  ∷ noExactPromotionLabel
  ∷ []

record SU2LevelMismatchResolutionReceipt : Set where
  field
    levelReadings :
      List SU2LevelReading

    levelReadingsAreCanonical :
      levelReadings ≡ canonicalSU2LevelMismatchReadings

    p3LaneReading :
      SU2LevelReading

    p3LaneReadingIsCanonical :
      p3LaneReading ≡ p3LaneSU2Level3Reading

    p3LaneLevelIsThree :
      recordedLevel p3LaneReading ≡ 3

    standardModelReading :
      SU2LevelReading

    standardModelReadingIsCanonical :
      standardModelReading ≡ standardModelSU2Level1Reading

    standardModelLevelIsOne :
      recordedLevel standardModelReading ≡ 1

    mismatchStatusBeforeShift :
      SU2LevelMismatchStatus

    mismatchStatusBeforeShiftIsUnresolved :
      mismatchStatusBeforeShift ≡ unresolvedBeforeShift

    shiftConvention :
      CSLevelShiftConvention

    shiftConventionIsWittenDualCoxeter :
      shiftConvention ≡ wittenOneLoopDualCoxeterShift

    shiftFormula :
      String

    shiftFormulaIsCanonical :
      shiftFormula ≡ csLevelShiftFormulaLabel

    bareChernSimonsLevel :
      Nat

    bareChernSimonsLevelIsP3LevelThree :
      bareChernSimonsLevel ≡ p3LaneChernSimonsBareLevel

    su2HVee :
      Nat

    su2HVeeIsTwo :
      su2HVee ≡ su2DualCoxeterNumber

    effectiveChernSimonsLevel :
      Nat

    effectiveChernSimonsLevelIsOne :
      effectiveChernSimonsLevel ≡ p3LaneShiftedEffectiveLevel

    candidateResolutionStatus :
      SU2LevelMismatchStatus

    candidateResolutionStatusIsShifted :
      candidateResolutionStatus ≡ candidateResolvedByCSShift

    candidateShiftMatchesSMLevelOne :
      Bool

    candidateShiftMatchesSMLevelOneIsTrue :
      candidateShiftMatchesSMLevelOne ≡ true

    authorityCitations :
      List CSLevelShiftAuthorityCitation

    authorityCitationsAreCanonical :
      authorityCitations ≡ canonicalCSLevelShiftAuthorityCitations

    authorityStatement :
      String

    authorityStatementIsCanonical :
      authorityStatement ≡ wittenCSLevelShiftAuthorityLabel

    citationAuthorityOnly :
      Bool

    citationAuthorityOnlyIsTrue :
      citationAuthorityOnly ≡ true

    exactSU2LPromotion :
      Bool

    exactSU2LPromotionIsFalse :
      exactSU2LPromotion ≡ false

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    exactGDHREqualsGSMPromotion :
      Bool

    exactGDHREqualsGSMPromotionIsFalse :
      exactGDHREqualsGSMPromotion ≡ false

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalSU2LevelMismatchResolutionBoundary

open SU2LevelMismatchResolutionReceipt public

canonicalSU2LevelMismatchResolutionReceipt :
  SU2LevelMismatchResolutionReceipt
canonicalSU2LevelMismatchResolutionReceipt =
  record
    { levelReadings =
        canonicalSU2LevelMismatchReadings
    ; levelReadingsAreCanonical =
        refl
    ; p3LaneReading =
        p3LaneSU2Level3Reading
    ; p3LaneReadingIsCanonical =
        refl
    ; p3LaneLevelIsThree =
        refl
    ; standardModelReading =
        standardModelSU2Level1Reading
    ; standardModelReadingIsCanonical =
        refl
    ; standardModelLevelIsOne =
        refl
    ; mismatchStatusBeforeShift =
        unresolvedBeforeShift
    ; mismatchStatusBeforeShiftIsUnresolved =
        refl
    ; shiftConvention =
        wittenOneLoopDualCoxeterShift
    ; shiftConventionIsWittenDualCoxeter =
        refl
    ; shiftFormula =
        csLevelShiftFormulaLabel
    ; shiftFormulaIsCanonical =
        refl
    ; bareChernSimonsLevel =
        p3LaneChernSimonsBareLevel
    ; bareChernSimonsLevelIsP3LevelThree =
        refl
    ; su2HVee =
        su2DualCoxeterNumber
    ; su2HVeeIsTwo =
        refl
    ; effectiveChernSimonsLevel =
        p3LaneShiftedEffectiveLevel
    ; effectiveChernSimonsLevelIsOne =
        refl
    ; candidateResolutionStatus =
        candidateResolvedByCSShift
    ; candidateResolutionStatusIsShifted =
        refl
    ; candidateShiftMatchesSMLevelOne =
        true
    ; candidateShiftMatchesSMLevelOneIsTrue =
        refl
    ; authorityCitations =
        canonicalCSLevelShiftAuthorityCitations
    ; authorityCitationsAreCanonical =
        refl
    ; authorityStatement =
        wittenCSLevelShiftAuthorityLabel
    ; authorityStatementIsCanonical =
        refl
    ; citationAuthorityOnly =
        true
    ; citationAuthorityOnlyIsTrue =
        refl
    ; exactSU2LPromotion =
        false
    ; exactSU2LPromotionIsFalse =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; exactGDHREqualsGSMPromotion =
        false
    ; exactGDHREqualsGSMPromotionIsFalse =
        refl
    ; receiptBoundary =
        canonicalSU2LevelMismatchResolutionBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

p3LaneBareLevelRecordedAsThree :
  bareChernSimonsLevel canonicalSU2LevelMismatchResolutionReceipt
  ≡
  3
p3LaneBareLevelRecordedAsThree =
  bareChernSimonsLevelIsP3LevelThree canonicalSU2LevelMismatchResolutionReceipt

su2DualCoxeterRecordedAsTwo :
  su2HVee canonicalSU2LevelMismatchResolutionReceipt
  ≡
  2
su2DualCoxeterRecordedAsTwo =
  su2HVeeIsTwo canonicalSU2LevelMismatchResolutionReceipt

p3LaneEffectiveLevelRecordedAsOne :
  effectiveChernSimonsLevel canonicalSU2LevelMismatchResolutionReceipt
  ≡
  1
p3LaneEffectiveLevelRecordedAsOne =
  effectiveChernSimonsLevelIsOne canonicalSU2LevelMismatchResolutionReceipt

su2LevelMismatchResolutionDoesNotPromoteExactSU2L :
  exactSU2LPromotion canonicalSU2LevelMismatchResolutionReceipt
  ≡
  false
su2LevelMismatchResolutionDoesNotPromoteExactSU2L =
  exactSU2LPromotionIsFalse canonicalSU2LevelMismatchResolutionReceipt

su2LevelMismatchResolutionDoesNotPromoteExactSM :
  exactStandardModelPromotion canonicalSU2LevelMismatchResolutionReceipt
  ≡
  false
su2LevelMismatchResolutionDoesNotPromoteExactSM =
  exactStandardModelPromotionIsFalse canonicalSU2LevelMismatchResolutionReceipt

su2LevelMismatchResolutionDoesNotPromoteExactGDHR :
  exactGDHREqualsGSMPromotion canonicalSU2LevelMismatchResolutionReceipt
  ≡
  false
su2LevelMismatchResolutionDoesNotPromoteExactGDHR =
  exactGDHREqualsGSMPromotionIsFalse canonicalSU2LevelMismatchResolutionReceipt
