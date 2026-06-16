module DASHI.Physics.Closure.NSKatoConfinementLemmaReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Kato strain-eigenvalue Hessian identity + vortex-core confinement
-- shape receipt.
--
-- This is a strictly fail-closed shape layer.  It records only the
-- analytic vocabulary for the Kato identity route and confinement radius
-- shape: Kato identity, distinct eigenvalue gaps, λ2 < 0, negative cross
-- derivative K, and the formal Taylor/minimax radius r* = δ0 / K.
-- It also records the corrected distinction between an enstrophy maximum
-- and a true vortex-core target, plus the gap-preservation candidate shape.
--
-- No theorem promotion is performed here.  In particular, Miller-criterion
-- promotion is explicitly blocked via named blockers and false promotion
-- flags.

data NSKatoConfinementLemmaStatus : Set where
  failClosedShapeOnly : NSKatoConfinementLemmaStatus

data NSKatoConfinementShape : Set where
  katoStrainEigenvalueHessianIdentity : NSKatoConfinementShape
  distinctEigenvalueGapRequirement : NSKatoConfinementShape
  lambda2NegativeAtCore : NSKatoConfinementShape
  negativeCrossDerivativeK : NSKatoConfinementShape
  confinementRadiusTaylorMinimaxFormula : NSKatoConfinementShape
  enstrophyMaximumNotNecessarilyVortexCore : NSKatoConfinementShape
  vortexCoreTargetSelectionRequired : NSKatoConfinementShape
  katoAlignmentBCondition : NSKatoConfinementShape
  thirdOrderRemainderMCondition : NSKatoConfinementShape
  gap12LowerBoundShape : NSKatoConfinementShape

canonicalNSKatoConfinementShape : List NSKatoConfinementShape
canonicalNSKatoConfinementShape =
  katoStrainEigenvalueHessianIdentity
  ∷ distinctEigenvalueGapRequirement
  ∷ lambda2NegativeAtCore
  ∷ negativeCrossDerivativeK
  ∷ confinementRadiusTaylorMinimaxFormula
  ∷ enstrophyMaximumNotNecessarilyVortexCore
  ∷ vortexCoreTargetSelectionRequired
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
  "Kato strain-eigenvalue Hessian shape: mixed-direction Hessian for λ2 in the strain eigenframe is the core analytic route, recorded as a local identity shape only."

eigenvalueGapShapeText : String
eigenvalueGapShapeText =
  "Distinct eigenvalue gap requirement: local gaps (λ1-λ2) and (λ2-λ3) are explicit denominators / separation inputs and are not proved here."

lambda2NegativeText : String
lambda2NegativeText =
  "Core sign gate is recorded as lambda2<=-delta0 at the true vortex-core target; this receipt does not claim the current enstrophy maximum already satisfies it."

crossDerivativeNegativeText : String
crossDerivativeNegativeText =
  "Cross-derivative curvature is recorded as cross derivative<=-delta, with the K = T e1 (T e2 λ2) notation kept as a shape tag only."

confinementRadiusText : String
confinementRadiusText =
  "Confinement radius is recorded as a shape formula only: r* = delta0 / K."

enstrophyMaximumText : String
enstrophyMaximumText =
  "Enstrophy maximum is recorded as not necessarily identical to the true vortex-core target."

vortexCoreTargetSelectionText : String
vortexCoreTargetSelectionText =
  "A true vortex-core target selector is required and is not yet supplied by this receipt."

katoAlignmentBConditionText : String
katoAlignmentBConditionText =
  "Kato alignment condition B is recorded as a required gate at the true vortex-core target."

thirdOrderRemainderMConditionText : String
thirdOrderRemainderMConditionText =
  "Third-order remainder condition M is recorded as a required gate; H3 remainder control is not yet measured."

gap12LowerBoundShapeText : String
gap12LowerBoundShapeText =
  "Gap-preservation candidate shape: if lambda2<=-delta0, cross derivative<=-delta, B>=b0>0, and M<delta at a true vortex-core target, then gap12 >= b0/(delta+M), by the Kato identity contradiction on gap collapse."

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
      "O: Record a fail-closed Kato strain-eigenvalue Hessian identity and vortex-core confinement shape receipt."

    R : String
    RIsCanonical : R ≡
      "R: Record shape-only Kato identity, distinct eigenvalue gaps, enstrophy maximum not necessarily true vortex core, true vortex-core target selection required, λ2 gate, B gate, M gate, gap12 lower-bound candidate, and explicit blockers."

    C : String
    CIsCanonical : C ≡
      "C: This module exports route/shape tokens, blocker ledger, and explicit fail-closed promotion guards; it does not claim the enstrophy maximum already satisfies the true vortex-core target gate."

    S : String
    SIsCanonical : S ≡
      "S: Kato identity recorded; distinct-gap gate recorded; lambda2<=-delta0 gate recorded; cross-derivative gate recorded; B>=b0 gate recorded; M<delta gate recorded; gap12 lower-bound candidate recorded; blockers recorded."

    L : String
    LIsCanonical : L ≡
      "L: Kato route -> true vortex-core target selection -> lambda2 gate -> B gate -> M gate -> gap12 lower-bound candidate."

    P : String
    PIsCanonical : P ≡
      "P: Keep this as a shape/receipt layer only. No Miller criterion theorem is promoted."

    G : String
    GIsCanonical : G ≡
      "G: No Clay or terminal promotion and no fake local theorem promotion are introduced."

    F : String
    FIsCanonical : F ≡
      "F: Promotion remains blocked by the explicit blockers: target selector measurement missing or required, condition C at true vortex core not yet measured, condition D/H3 remainder control missing, and no Miller bridge."

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

    lambda2NegativeRecorded :
      Bool

    lambda2NegativeRecordedIsTrue :
      lambda2NegativeRecorded ≡ true

    lambda2NegativeTextRecorded :
      String

    lambda2NegativeTextRecordedIsCanonical :
      lambda2NegativeTextRecorded ≡ lambda2NegativeText

    crossDerivativeNegativeRecorded :
      Bool

    crossDerivativeNegativeRecordedIsTrue :
      crossDerivativeNegativeRecorded ≡ true

    crossDerivativeNegativeTextRecorded :
      String

    crossDerivativeNegativeTextRecordedIsCanonical :
      crossDerivativeNegativeTextRecorded ≡ crossDerivativeNegativeText

    confinementRadiusShapeRecorded :
      Bool

    confinementRadiusShapeRecordedIsTrue :
      confinementRadiusShapeRecorded ≡ true

    confinementRadiusFormula :
      String

    confinementRadiusFormulaIsCanonical :
      confinementRadiusFormula ≡ confinementRadiusText

    enstrophyMaximumShapeRecorded :
      Bool

    enstrophyMaximumShapeRecordedIsTrue :
      enstrophyMaximumShapeRecorded ≡ true

    enstrophyMaximumTextRecorded :
      String

    enstrophyMaximumTextRecordedIsCanonical :
      enstrophyMaximumTextRecorded ≡ enstrophyMaximumText

    vortexCoreTargetSelectionRecorded :
      Bool

    vortexCoreTargetSelectionRecordedIsTrue :
      vortexCoreTargetSelectionRecorded ≡ true

    vortexCoreTargetSelectionTextRecorded :
      String

    vortexCoreTargetSelectionTextRecordedIsCanonical :
      vortexCoreTargetSelectionTextRecorded ≡ vortexCoreTargetSelectionText

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
    "O: Record a fail-closed Kato strain-eigenvalue Hessian identity and vortex-core confinement shape receipt."
    refl
    "R: Record shape-only Kato identity, distinct eigenvalue gaps, enstrophy maximum not necessarily true vortex core, true vortex-core target selection required, λ2 gate, B gate, M gate, gap12 lower-bound candidate, and explicit blockers."
    refl
    "C: This module exports route/shape tokens, blocker ledger, and explicit fail-closed promotion guards; it does not claim the enstrophy maximum already satisfies the true vortex-core target gate."
    refl
    "S: Kato identity recorded; distinct-gap gate recorded; lambda2<=-delta0 gate recorded; cross-derivative gate recorded; B>=b0 gate recorded; M<delta gate recorded; gap12 lower-bound candidate recorded; blockers recorded."
    refl
    "L: Kato route -> true vortex-core target selection -> lambda2 gate -> B gate -> M gate -> gap12 lower-bound candidate."
    refl
    "P: Keep this as a shape/receipt layer only. No Miller criterion theorem is promoted."
    refl
    "G: No Clay or terminal promotion and no fake local theorem promotion are introduced."
    refl
    "F: Promotion remains blocked by the explicit blockers: target selector measurement missing or required, condition C at true vortex core not yet measured, condition D/H3 remainder control missing, and no Miller bridge."
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
    ; lambda2NegativeRecorded =
        true
    ; lambda2NegativeRecordedIsTrue =
        refl
    ; lambda2NegativeTextRecorded =
        lambda2NegativeText
    ; lambda2NegativeTextRecordedIsCanonical =
        refl
    ; crossDerivativeNegativeRecorded =
        true
    ; crossDerivativeNegativeRecordedIsTrue =
        refl
    ; crossDerivativeNegativeTextRecorded =
        crossDerivativeNegativeText
    ; crossDerivativeNegativeTextRecordedIsCanonical =
        refl
    ; confinementRadiusShapeRecorded =
        true
    ; confinementRadiusShapeRecordedIsTrue =
        refl
    ; confinementRadiusFormula =
        confinementRadiusText
    ; confinementRadiusFormulaIsCanonical =
        refl
    ; enstrophyMaximumShapeRecorded =
        true
    ; enstrophyMaximumShapeRecordedIsTrue =
        refl
    ; enstrophyMaximumTextRecorded =
        enstrophyMaximumText
    ; enstrophyMaximumTextRecordedIsCanonical =
        refl
    ; vortexCoreTargetSelectionRecorded =
        true
    ; vortexCoreTargetSelectionRecordedIsTrue =
        refl
    ; vortexCoreTargetSelectionTextRecorded =
        vortexCoreTargetSelectionText
    ; vortexCoreTargetSelectionTextRecordedIsCanonical =
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
