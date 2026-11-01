module DASHI.Physics.Closure.NSKatoConfinementLemmaReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.NSKatoHessianConfinementReceipt
  using
    ( NSKatoHessianConfinementReceipt
    ; canonicalNSKatoHessianConfinementReceipt
    )

------------------------------------------------------------------------
-- Deprecated Kato confinement lemma receipt.
--
-- This module is retained as a fail-closed compatibility shell only.
-- The obsolete negative-cross-derivative vortex-core story is no longer
-- asserted here.  The corrected distinction is recorded explicitly:
--
--   xE / enstrophy maximum: lambda2>0 and negative cross derivative
--   xV / true vortex core:  lambda2<0 and positive Hessian/confinement
--
-- The canonical live confinement receipt is
-- DASHI.Physics.Closure.NSKatoHessianConfinementReceipt.
--
-- No theorem promotion is performed here.  Miller-criterion promotion is
-- explicitly blocked via named blockers and false promotion flags.

data NSKatoConfinementLemmaStatus : Set where
  failClosedShapeOnly : NSKatoConfinementLemmaStatus

data NSKatoConfinementShape : Set where
  katoStrainEigenvalueHessianIdentity : NSKatoConfinementShape
  distinctEigenvalueGapRequirement : NSKatoConfinementShape
  enstrophyMaximumXERouteRecorded : NSKatoConfinementShape
  xELambda2PositiveAndNegativeCrossDerivative : NSKatoConfinementShape
  vortexCoreXVRouteRecorded : NSKatoConfinementShape
  xVLambda2NegativeAndPositiveHessianConfinementSignal : NSKatoConfinementShape
  legacyRouteRedirectedToNSKatoHessianConfinementReceipt : NSKatoConfinementShape
  katoAlignmentBCondition : NSKatoConfinementShape
  thirdOrderRemainderMCondition : NSKatoConfinementShape
  gap12LowerBoundShape : NSKatoConfinementShape

canonicalNSKatoConfinementShape : List NSKatoConfinementShape
canonicalNSKatoConfinementShape =
  katoStrainEigenvalueHessianIdentity
  ∷ distinctEigenvalueGapRequirement
  ∷ enstrophyMaximumXERouteRecorded
  ∷ xELambda2PositiveAndNegativeCrossDerivative
  ∷ vortexCoreXVRouteRecorded
  ∷ xVLambda2NegativeAndPositiveHessianConfinementSignal
  ∷ legacyRouteRedirectedToNSKatoHessianConfinementReceipt
  ∷ katoAlignmentBCondition
  ∷ thirdOrderRemainderMCondition
  ∷ gap12LowerBoundShape
  ∷ []

data NSKatoConfinementMillerBlocker : Set where
  targetSelectorMeasurementMissing : NSKatoConfinementMillerBlocker
  targetSelectorMeasurementRequired : NSKatoConfinementMillerBlocker
  conditionCAtTrueVortexCoreNotYetMeasured : NSKatoConfinementMillerBlocker
  conditionDH3RemainderControlMissing : NSKatoConfinementMillerBlocker
  noMillerBridge : NSKatoConfinementMillerBlocker

canonicalNSKatoConfinementMillerBlockers : List NSKatoConfinementMillerBlocker
canonicalNSKatoConfinementMillerBlockers =
  targetSelectorMeasurementMissing
  ∷ targetSelectorMeasurementRequired
  ∷ conditionCAtTrueVortexCoreNotYetMeasured
  ∷ conditionDH3RemainderControlMissing
  ∷ noMillerBridge
  ∷ []

data NSKatoConfinementPromotion : Set where

katoConfinementPromotionImpossibleHere :
  NSKatoConfinementPromotion →
  ⊥
katoConfinementPromotionImpossibleHere ()

katoShapeText : String
katoShapeText =
  "Deprecated compatibility shell: the old Kato receipt now redirects to NSKatoHessianConfinementReceipt."

eigenvalueGapShapeText : String
eigenvalueGapShapeText =
  "Distinct eigenvalue gap requirement: local gaps (lambda1-lambda2) and (lambda2-lambda3) remain explicit separation inputs and are not proved here."

enstrophyMaximumXERouteText : String
enstrophyMaximumXERouteText =
  "At the enstrophy maximum xE, lambda2>0 and the cross derivative is negative; this is the xE diagnostic lane, not the vortex-core lane."

vortexCoreXVRouteText : String
vortexCoreXVRouteText =
  "At the true vortex core xV, lambda2<0 and the Hessian/confinement signal is positive; the live confinement lane is recorded in NSKatoHessianConfinementReceipt."

legacyRouteRedirectText : String
legacyRouteRedirectText =
  "This legacy receipt is retained only for compatibility and redirects readers to the canonical Hessian confinement receipt."

katoAlignmentBConditionText : String
katoAlignmentBConditionText =
  "Kato alignment condition B is retained as a legacy gate at the true vortex-core target."

thirdOrderRemainderMConditionText : String
thirdOrderRemainderMConditionText =
  "Third-order remainder condition M is retained as a legacy gate; H3 remainder control is not yet measured here."

gap12LowerBoundShapeText : String
gap12LowerBoundShapeText =
  "Legacy gap-preservation candidate shape is retained only as a non-promoting marker; the canonical confinement signal is in NSKatoHessianConfinementReceipt."

theoremCandidateText : String
theoremCandidateText =
  gap12LowerBoundShapeText

millerBlockerText : String
millerBlockerText =
  "Promotion is blocked until target-selector measurement, condition C at the true vortex core, condition D/H3 remainder control, and a Miller bridge are provided."

record NSKatoConfinementLemmaORCSLPGF : Set where
  constructor mkNSKatoConfinementLemmaORCSLPGF
  field
    O : String
    OIsCanonical : O ≡
      "O: Retain a deprecated Kato receipt as a compatibility shell and redirect to the canonical Hessian confinement receipt."

    R : String
    RIsCanonical : R ≡
      "R: Record the corrected xE/xV distinction, keep the legacy gap-preservation shape non-promoting, and point readers to NSKatoHessianConfinementReceipt."

    C : String
    CIsCanonical : C ≡
      "C: This module is a fail-closed compatibility wrapper; the canonical sign story is exported by NSKatoHessianConfinementReceipt."

    S : String
    SIsCanonical : S ≡
      "S: xE lane records lambda2>0 with negative cross derivative; xV lane records lambda2<0 with positive Hessian/confinement signal; promotion remains blocked."

    L : String
    LIsCanonical : L ≡
      "L: Legacy Kato receipt -> corrected xE/xV distinction -> canonical Hessian receipt for the live confinement signal."

    P : String
    PIsCanonical : P ≡
      "P: Keep this module as deprecated compatibility only; do not promote any theorem from it."

    G : String
    GIsCanonical : G ≡
      "G: No Clay, Miller, or external promotion is introduced here; the canonical module carries the corrected confinement statement."

    F : String
    FIsCanonical : F ≡
      "F: Promotion remains blocked and this file exists only to redirect to NSKatoHessianConfinementReceipt."

record NSKatoConfinementLemmaReceipt : Setω where
  field
    status :
      NSKatoConfinementLemmaStatus

    statusIsFailClosed :
      status ≡ failClosedShapeOnly

    shapeLedger :
      List NSKatoConfinementShape

    shapeLedgerIsCanonical :
      shapeLedger ≡ canonicalNSKatoConfinementShape

    katoShapeRecorded :
      Bool

    katoShapeRecordedIsTrue :
      katoShapeRecorded ≡ true

    katoIdentityText :
      String

    katoIdentityTextIsCanonical :
      katoIdentityText ≡ katoShapeText

    distinctGapShapeRecorded :
      Bool

    distinctGapShapeRecordedIsTrue :
      distinctGapShapeRecorded ≡ true

    eigenvalueGapText :
      String

    eigenvalueGapTextIsCanonical :
      eigenvalueGapText ≡ eigenvalueGapShapeText

    enstrophyMaximumXERouteRecordedFlag :
      Bool

    enstrophyMaximumXERouteRecordedFlagIsTrue :
      enstrophyMaximumXERouteRecordedFlag ≡ true

    enstrophyMaximumXERouteTextRecorded :
      String

    enstrophyMaximumXERouteTextRecordedIsCanonical :
      enstrophyMaximumXERouteTextRecorded ≡ enstrophyMaximumXERouteText

    vortexCoreXVRouteRecordedFlag :
      Bool

    vortexCoreXVRouteRecordedFlagIsTrue :
      vortexCoreXVRouteRecordedFlag ≡ true

    vortexCoreXVRouteTextRecorded :
      String

    vortexCoreXVRouteTextRecordedIsCanonical :
      vortexCoreXVRouteTextRecorded ≡ vortexCoreXVRouteText

    legacyRouteRedirectRecordedFlag :
      Bool

    legacyRouteRedirectRecordedFlagIsTrue :
      legacyRouteRedirectRecordedFlag ≡ true

    legacyRouteRedirectTextRecorded :
      String

    legacyRouteRedirectTextRecordedIsCanonical :
      legacyRouteRedirectTextRecorded ≡ legacyRouteRedirectText

    katoAlignmentBConditionRecorded :
      Bool

    katoAlignmentBConditionRecordedIsTrue :
      katoAlignmentBConditionRecorded ≡ true

    katoAlignmentBConditionTextRecorded :
      String

    katoAlignmentBConditionTextRecordedIsCanonical :
      katoAlignmentBConditionTextRecorded ≡ katoAlignmentBConditionText

    thirdOrderRemainderMConditionRecorded :
      Bool

    thirdOrderRemainderMConditionRecordedIsTrue :
      thirdOrderRemainderMConditionRecorded ≡ true

    thirdOrderRemainderMConditionTextRecorded :
      String

    thirdOrderRemainderMConditionTextRecordedIsCanonical :
      thirdOrderRemainderMConditionTextRecorded ≡ thirdOrderRemainderMConditionText

    gap12LowerBoundShapeRecorded :
      Bool

    gap12LowerBoundShapeRecordedIsTrue :
      gap12LowerBoundShapeRecorded ≡ true

    gap12LowerBoundShapeTextRecorded :
      String

    gap12LowerBoundShapeTextRecordedIsCanonical :
      gap12LowerBoundShapeTextRecorded ≡ gap12LowerBoundShapeText

    millerBlockers :
      List NSKatoConfinementMillerBlocker

    millerBlockersAreCanonical :
      millerBlockers ≡ canonicalNSKatoConfinementMillerBlockers

    millerBlockerExplanation :
      String

    millerBlockerExplanationIsCanonical :
      millerBlockerExplanation ≡ millerBlockerText

    theoremCandidate :
      String

    theoremCandidateIsCanonical :
      theoremCandidate ≡ theoremCandidateText

    canonicalHessianReceipt :
      NSKatoHessianConfinementReceipt

    canonicalHessianReceiptIsCanonical :
      canonicalHessianReceipt ≡ canonicalNSKatoHessianConfinementReceipt

    millerCriterionPromotion :
      Bool

    millerCriterionPromotionIsFalse :
      millerCriterionPromotion ≡ false

    confinementLemmaPromoted :
      Bool

    confinementLemmaPromotedIsFalse :
      confinementLemmaPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    promotionLedger :
      List NSKatoConfinementPromotion

    promotionLedgerIsEmpty :
      promotionLedger ≡ []

    orcslpgf :
      NSKatoConfinementLemmaORCSLPGF

open NSKatoConfinementLemmaReceipt public

canonicalNSKatoConfinementLemmaORCSLPGF :
  NSKatoConfinementLemmaORCSLPGF
canonicalNSKatoConfinementLemmaORCSLPGF =
  mkNSKatoConfinementLemmaORCSLPGF
    "O: Retain a deprecated Kato receipt as a compatibility shell and redirect to the canonical Hessian confinement receipt."
    refl
    "R: Record the corrected xE/xV distinction, keep the legacy gap-preservation shape non-promoting, and point readers to NSKatoHessianConfinementReceipt."
    refl
    "C: This module is a fail-closed compatibility wrapper; the canonical sign story is exported by NSKatoHessianConfinementReceipt."
    refl
    "S: xE lane records lambda2>0 with negative cross derivative; xV lane records lambda2<0 with positive Hessian/confinement signal; promotion remains blocked."
    refl
    "L: Legacy Kato receipt -> corrected xE/xV distinction -> canonical Hessian receipt for the live confinement signal."
    refl
    "P: Keep this module as deprecated compatibility only; do not promote any theorem from it."
    refl
    "G: No Clay, Miller, or external promotion is introduced here; the canonical module carries the corrected confinement statement."
    refl
    "F: Promotion remains blocked and this file exists only to redirect to NSKatoHessianConfinementReceipt."
    refl

canonicalNSKatoConfinementLemmaReceipt :
  NSKatoConfinementLemmaReceipt
canonicalNSKatoConfinementLemmaReceipt =
  record
    { status =
        failClosedShapeOnly
    ; statusIsFailClosed =
        refl
    ; shapeLedger =
        canonicalNSKatoConfinementShape
    ; shapeLedgerIsCanonical =
        refl
    ; katoShapeRecorded =
        true
    ; katoShapeRecordedIsTrue =
        refl
    ; katoIdentityText =
        katoShapeText
    ; katoIdentityTextIsCanonical =
        refl
    ; distinctGapShapeRecorded =
        true
    ; distinctGapShapeRecordedIsTrue =
        refl
    ; eigenvalueGapText =
        eigenvalueGapShapeText
    ; eigenvalueGapTextIsCanonical =
        refl
    ; enstrophyMaximumXERouteRecordedFlag =
        true
    ; enstrophyMaximumXERouteRecordedFlagIsTrue =
        refl
    ; enstrophyMaximumXERouteTextRecorded =
        enstrophyMaximumXERouteText
    ; enstrophyMaximumXERouteTextRecordedIsCanonical =
        refl
    ; vortexCoreXVRouteRecordedFlag =
        true
    ; vortexCoreXVRouteRecordedFlagIsTrue =
        refl
    ; vortexCoreXVRouteTextRecorded =
        vortexCoreXVRouteText
    ; vortexCoreXVRouteTextRecordedIsCanonical =
        refl
    ; legacyRouteRedirectRecordedFlag =
        true
    ; legacyRouteRedirectRecordedFlagIsTrue =
        refl
    ; legacyRouteRedirectTextRecorded =
        legacyRouteRedirectText
    ; legacyRouteRedirectTextRecordedIsCanonical =
        refl
    ; katoAlignmentBConditionRecorded =
        true
    ; katoAlignmentBConditionRecordedIsTrue =
        refl
    ; katoAlignmentBConditionTextRecorded =
        katoAlignmentBConditionText
    ; katoAlignmentBConditionTextRecordedIsCanonical =
        refl
    ; thirdOrderRemainderMConditionRecorded =
        true
    ; thirdOrderRemainderMConditionRecordedIsTrue =
        refl
    ; thirdOrderRemainderMConditionTextRecorded =
        thirdOrderRemainderMConditionText
    ; thirdOrderRemainderMConditionTextRecordedIsCanonical =
        refl
    ; gap12LowerBoundShapeRecorded =
        true
    ; gap12LowerBoundShapeRecordedIsTrue =
        refl
    ; gap12LowerBoundShapeTextRecorded =
        gap12LowerBoundShapeText
    ; gap12LowerBoundShapeTextRecordedIsCanonical =
        refl
    ; millerBlockers =
        canonicalNSKatoConfinementMillerBlockers
    ; millerBlockersAreCanonical =
        refl
    ; millerBlockerExplanation =
        millerBlockerText
    ; millerBlockerExplanationIsCanonical =
        refl
    ; theoremCandidate =
        theoremCandidateText
    ; theoremCandidateIsCanonical =
        refl
    ; canonicalHessianReceipt =
        canonicalNSKatoHessianConfinementReceipt
    ; canonicalHessianReceiptIsCanonical =
        refl
    ; millerCriterionPromotion =
        false
    ; millerCriterionPromotionIsFalse =
        refl
    ; confinementLemmaPromoted =
        false
    ; confinementLemmaPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; promotionLedger =
        []
    ; promotionLedgerIsEmpty =
        refl
    ; orcslpgf =
        canonicalNSKatoConfinementLemmaORCSLPGF
    }
