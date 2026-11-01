module DASHI.Physics.Closure.YukawaAlphaIdentificationReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Yukawa alpha identification receipt.
--
-- This receipt records the requested alpha identifications as diagnostic
-- Yukawa readbacks.  It deliberately rejects a common-alpha promotion and
-- does not reinterpret these quantities as Wolfenstein parameters.

data YukawaAlphaIdentificationStatus : Set where
  yukawaAlphaIdentificationRecordedDiagnosticOnly :
    YukawaAlphaIdentificationStatus

data YukawaAlphaIdentificationBlocker : Set where
  commonAlphaFitRejected :
    YukawaAlphaIdentificationBlocker

  physicalYukawaAuthorityMissing :
    YukawaAlphaIdentificationBlocker

  physicalCKMAuthorityMissing :
    YukawaAlphaIdentificationBlocker

  wolfensteinParameterPromotionRejected :
    YukawaAlphaIdentificationBlocker

canonicalYukawaAlphaIdentificationBlockers :
  List YukawaAlphaIdentificationBlocker
canonicalYukawaAlphaIdentificationBlockers =
  commonAlphaFitRejected
  ∷ physicalYukawaAuthorityMissing
  ∷ physicalCKMAuthorityMissing
  ∷ wolfensteinParameterPromotionRejected
  ∷ []

data YukawaAlphaIdentificationPromotion : Set where

yukawaAlphaIdentificationPromotionImpossibleHere :
  YukawaAlphaIdentificationPromotion →
  ⊥
yukawaAlphaIdentificationPromotionImpossibleHere ()

alpha1FormulaLabel : String
alpha1FormulaLabel =
  "alpha1 = sqrt(m_u/m_c) = 0.04124"

alpha2FormulaLabel : String
alpha2FormulaLabel =
  "alpha2 = sqrt(m_c/m_t) = 0.08575"

alphaDFormulaLabel : String
alphaDFormulaLabel =
  "alpha_d = sqrt(m_d/m_s) = lambda_W"

alpha1ErrorLabel : String
alpha1ErrorLabel =
  "alpha1Error = 0.58pct"

alpha2ErrorLabel : String
alpha2ErrorLabel =
  "alpha2Error = 0.29pct"

canonicalYukawaAlphaIdentificationBoundary :
  List String
canonicalYukawaAlphaIdentificationBoundary =
  "alpha1 and alpha2 are recorded as two independent up-type Yukawa mass-ratio readbacks"
  ∷ "alpha_d is recorded only as the down-type sqrt(m_d/m_s) comparison with lambda_W"
  ∷ "acceptedCommonAlpha is false; the alpha readbacks are not Wolfenstein parameters"
  ∷ "This receipt does not promote physical Yukawa, physical CKM, terminal, or Clay claims"
  ∷ []

record YukawaAlphaIdentificationReceipt : Set where
  field
    status :
      YukawaAlphaIdentificationStatus

    alpha1Formula :
      String

    alpha1FormulaIsCanonical :
      alpha1Formula ≡ alpha1FormulaLabel

    alpha1 :
      Float

    alpha2Formula :
      String

    alpha2FormulaIsCanonical :
      alpha2Formula ≡ alpha2FormulaLabel

    alpha2 :
      Float

    alphaDFormula :
      String

    alphaDFormulaIsCanonical :
      alphaDFormula ≡ alphaDFormulaLabel

    alpha1Error :
      String

    alpha1ErrorIsCanonical :
      alpha1Error ≡ alpha1ErrorLabel

    alpha1ErrorPercent :
      Float

    alpha2Error :
      String

    alpha2ErrorIsCanonical :
      alpha2Error ≡ alpha2ErrorLabel

    alpha2ErrorPercent :
      Float

    acceptedCommonAlpha :
      Bool

    acceptedCommonAlphaIsFalse :
      acceptedCommonAlpha ≡ false

    twoIndependentAlphas :
      Bool

    twoIndependentAlphasIsTrue :
      twoIndependentAlphas ≡ true

    alphasAreUpTypeYukawa :
      Bool

    alphasAreUpTypeYukawaIsTrue :
      alphasAreUpTypeYukawa ≡ true

    notWolfensteinParameters :
      Bool

    notWolfensteinParametersIsTrue :
      notWolfensteinParameters ≡ true

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

    blockers :
      List YukawaAlphaIdentificationBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYukawaAlphaIdentificationBlockers

    promotionFlags :
      List YukawaAlphaIdentificationPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalYukawaAlphaIdentificationBoundary

open YukawaAlphaIdentificationReceipt public

canonicalYukawaAlphaIdentificationReceipt :
  YukawaAlphaIdentificationReceipt
canonicalYukawaAlphaIdentificationReceipt =
  record
    { status =
        yukawaAlphaIdentificationRecordedDiagnosticOnly
    ; alpha1Formula =
        alpha1FormulaLabel
    ; alpha1FormulaIsCanonical =
        refl
    ; alpha1 =
        0.04124
    ; alpha2Formula =
        alpha2FormulaLabel
    ; alpha2FormulaIsCanonical =
        refl
    ; alpha2 =
        0.08575
    ; alphaDFormula =
        alphaDFormulaLabel
    ; alphaDFormulaIsCanonical =
        refl
    ; alpha1Error =
        alpha1ErrorLabel
    ; alpha1ErrorIsCanonical =
        refl
    ; alpha1ErrorPercent =
        0.58
    ; alpha2Error =
        alpha2ErrorLabel
    ; alpha2ErrorIsCanonical =
        refl
    ; alpha2ErrorPercent =
        0.29
    ; acceptedCommonAlpha =
        false
    ; acceptedCommonAlphaIsFalse =
        refl
    ; twoIndependentAlphas =
        true
    ; twoIndependentAlphasIsTrue =
        refl
    ; alphasAreUpTypeYukawa =
        true
    ; alphasAreUpTypeYukawaIsTrue =
        refl
    ; notWolfensteinParameters =
        true
    ; notWolfensteinParametersIsTrue =
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
    ; blockers =
        canonicalYukawaAlphaIdentificationBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        canonicalYukawaAlphaIdentificationBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

yukawaAlphaIdentificationRejectsCommonAlpha :
  acceptedCommonAlpha canonicalYukawaAlphaIdentificationReceipt ≡ false
yukawaAlphaIdentificationRejectsCommonAlpha =
  refl

yukawaAlphaIdentificationHasTwoIndependentAlphas :
  twoIndependentAlphas canonicalYukawaAlphaIdentificationReceipt ≡ true
yukawaAlphaIdentificationHasTwoIndependentAlphas =
  refl

yukawaAlphaIdentificationDoesNotPromotePhysicalYukawa :
  physicalYukawaPromoted canonicalYukawaAlphaIdentificationReceipt ≡ false
yukawaAlphaIdentificationDoesNotPromotePhysicalYukawa =
  refl

yukawaAlphaIdentificationDoesNotPromoteCKM :
  physicalCKMPromoted canonicalYukawaAlphaIdentificationReceipt ≡ false
yukawaAlphaIdentificationDoesNotPromoteCKM =
  refl

yukawaAlphaIdentificationDoesNotPromoteTerminal :
  terminalClaimPromoted canonicalYukawaAlphaIdentificationReceipt ≡ false
yukawaAlphaIdentificationDoesNotPromoteTerminal =
  refl

yukawaAlphaIdentificationDoesNotPromoteClay :
  clayPromoted canonicalYukawaAlphaIdentificationReceipt ≡ false
yukawaAlphaIdentificationDoesNotPromoteClay =
  refl
