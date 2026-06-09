module DASHI.Physics.Closure.YukawaProgrammeStatusReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Yukawa programme status receipt.
--
-- This receipt records the opened Yukawa programme and its present carrier
-- diagnostics.  It is explicitly non-promoting: no physical Yukawa
-- eigenbasis, CKM diagonalisation, terminal claim, or Clay claim is asserted.

data YukawaProgrammeStatus : Set where
  opened :
    YukawaProgrammeStatus

data CandidateStatus : Set where
  candidate :
    CandidateStatus

data YukawaProgrammeOpenItem : Set where
  downType23StillOpen :
    YukawaProgrammeOpenItem

  leptonYukawaStillOpen :
    YukawaProgrammeOpenItem

  ckmFull3x3MismatchDiagonalisationStillOpen :
    YukawaProgrammeOpenItem

canonicalYukawaProgrammeOpenItems :
  List YukawaProgrammeOpenItem
canonicalYukawaProgrammeOpenItems =
  downType23StillOpen
  ∷ leptonYukawaStillOpen
  ∷ ckmFull3x3MismatchDiagonalisationStillOpen
  ∷ []

data YukawaProgrammePromotion : Set where

yukawaProgrammePromotionImpossibleHere :
  YukawaProgrammePromotion →
  ⊥
yukawaProgrammePromotionImpossibleHere ()

alpha1UpTypeFormula : String
alpha1UpTypeFormula =
  "alpha1 = sqrt(m_u/m_c)"

alpha2UpTypeFormula : String
alpha2UpTypeFormula =
  "alpha2 = sqrt(m_c/m_t)"

georgiJarlskogCarrierDepthSeparationLabel : String
georgiJarlskogCarrierDepthSeparationLabel =
  "Georgi-Jarlskog explained as carrier depth separation"

ckmFull3x3MismatchDiagonalisationOpenLabel : String
ckmFull3x3MismatchDiagonalisationOpenLabel =
  "full 3x3 CKM mismatch diagonalisation open"

record YukawaProgrammeStatusReceipt : Set where
  field
    status :
      YukawaProgrammeStatus

    yukawaProgramme :
      YukawaProgrammeStatus

    yukawaProgrammeIsOpened :
      yukawaProgramme ≡ opened

    programmeOpenedRecorded :
      Bool

    programmeOpenedRecordedIsTrue :
      programmeOpenedRecorded ≡ true

    upTypeHierarchyDerived :
      CandidateStatus

    upTypeHierarchyDerivedIsCandidate :
      upTypeHierarchyDerived ≡ candidate

    alpha1Formula :
      String

    alpha1FormulaIsCanonical :
      alpha1Formula ≡ alpha1UpTypeFormula

    alpha1RelativeErrorPercent :
      Float

    alpha1RelativeErrorPercentLabel :
      String

    alpha2Formula :
      String

    alpha2FormulaIsCanonical :
      alpha2Formula ≡ alpha2UpTypeFormula

    alpha2RelativeErrorPercent :
      Float

    alpha2RelativeErrorPercentLabel :
      String

    georgiJarlskogExplained :
      CandidateStatus

    georgiJarlskogExplainedIsCandidate :
      georgiJarlskogExplained ≡ candidate

    georgiJarlskogExplanation :
      String

    georgiJarlskogExplanationIsCanonical :
      georgiJarlskogExplanation
      ≡
      georgiJarlskogCarrierDepthSeparationLabel

    downType23Open :
      Bool

    downType23OpenIsTrue :
      downType23Open ≡ true

    leptonYukawaOpen :
      Bool

    leptonYukawaOpenIsTrue :
      leptonYukawaOpen ≡ true

    ckmFull3x3MismatchDiagonalisationOpen :
      Bool

    ckmFull3x3MismatchDiagonalisationOpenIsTrue :
      ckmFull3x3MismatchDiagonalisationOpen ≡ true

    ckmFull3x3MismatchDiagonalisationStatus :
      String

    ckmFull3x3MismatchDiagonalisationStatusIsCanonical :
      ckmFull3x3MismatchDiagonalisationStatus
      ≡
      ckmFull3x3MismatchDiagonalisationOpenLabel

    openItems :
      List YukawaProgrammeOpenItem

    openItemsAreCanonical :
      openItems ≡ canonicalYukawaProgrammeOpenItems

    physicalYukawaPromoted :
      Bool

    physicalYukawaPromotedIsFalse :
      physicalYukawaPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    promotionFlags :
      List YukawaProgrammePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YukawaProgrammeStatusReceipt public

canonicalYukawaProgrammeStatusReceipt :
  YukawaProgrammeStatusReceipt
canonicalYukawaProgrammeStatusReceipt =
  record
    { status =
        opened
    ; yukawaProgramme =
        opened
    ; yukawaProgrammeIsOpened =
        refl
    ; programmeOpenedRecorded =
        true
    ; programmeOpenedRecordedIsTrue =
        refl
    ; upTypeHierarchyDerived =
        candidate
    ; upTypeHierarchyDerivedIsCandidate =
        refl
    ; alpha1Formula =
        alpha1UpTypeFormula
    ; alpha1FormulaIsCanonical =
        refl
    ; alpha1RelativeErrorPercent =
        0.58
    ; alpha1RelativeErrorPercentLabel =
        "alpha1=sqrt(m_u/m_c) at 0.58 percent"
    ; alpha2Formula =
        alpha2UpTypeFormula
    ; alpha2FormulaIsCanonical =
        refl
    ; alpha2RelativeErrorPercent =
        0.29
    ; alpha2RelativeErrorPercentLabel =
        "alpha2=sqrt(m_c/m_t) at 0.29 percent"
    ; georgiJarlskogExplained =
        candidate
    ; georgiJarlskogExplainedIsCandidate =
        refl
    ; georgiJarlskogExplanation =
        georgiJarlskogCarrierDepthSeparationLabel
    ; georgiJarlskogExplanationIsCanonical =
        refl
    ; downType23Open =
        true
    ; downType23OpenIsTrue =
        refl
    ; leptonYukawaOpen =
        true
    ; leptonYukawaOpenIsTrue =
        refl
    ; ckmFull3x3MismatchDiagonalisationOpen =
        true
    ; ckmFull3x3MismatchDiagonalisationOpenIsTrue =
        refl
    ; ckmFull3x3MismatchDiagonalisationStatus =
        ckmFull3x3MismatchDiagonalisationOpenLabel
    ; ckmFull3x3MismatchDiagonalisationStatusIsCanonical =
        refl
    ; openItems =
        canonicalYukawaProgrammeOpenItems
    ; openItemsAreCanonical =
        refl
    ; physicalYukawaPromoted =
        false
    ; physicalYukawaPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Yukawa programme is opened"
        ∷ "Up-type hierarchy is recorded as candidate: alpha1=sqrt(m_u/m_c) at 0.58 percent and alpha2=sqrt(m_c/m_t) at 0.29 percent"
        ∷ "Georgi-Jarlskog is recorded as carrier depth separation candidate"
        ∷ "Down-type 23, lepton Yukawa, and full 3x3 CKM mismatch diagonalisation remain open"
        ∷ "No physical Yukawa, CKM, terminal, or Clay promotion is asserted"
        ∷ []
    }

yukawaProgrammeOpened :
  yukawaProgramme canonicalYukawaProgrammeStatusReceipt ≡ opened
yukawaProgrammeOpened =
  refl

upTypeHierarchyCandidate :
  upTypeHierarchyDerived canonicalYukawaProgrammeStatusReceipt ≡ candidate
upTypeHierarchyCandidate =
  refl

georgiJarlskogCandidate :
  georgiJarlskogExplained canonicalYukawaProgrammeStatusReceipt ≡ candidate
georgiJarlskogCandidate =
  refl

yukawaProgrammeOpenItemsRemainOpen :
  downType23Open canonicalYukawaProgrammeStatusReceipt
  ≡
  true
yukawaProgrammeOpenItemsRemainOpen =
  refl

yukawaProgrammeDoesNotPromoteCKM :
  physicalCKMPromoted canonicalYukawaProgrammeStatusReceipt ≡ false
yukawaProgrammeDoesNotPromoteCKM =
  refl
