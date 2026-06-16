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

canonicalNSKatoConfinementShape : List NSKatoConfinementShape
canonicalNSKatoConfinementShape =
  katoStrainEigenvalueHessianIdentity
  ∷ distinctEigenvalueGapRequirement
  ∷ lambda2NegativeAtCore
  ∷ negativeCrossDerivativeK
  ∷ confinementRadiusTaylorMinimaxFormula
  ∷ []

data NSKatoConfinementMillerBlocker : Set where
  millerCriterionGapCertificateMissing : NSKatoConfinementMillerBlocker
  millerCriterionTaylorMinimaxControlMissing : NSKatoConfinementMillerBlocker
  millerCriterionNoIndependentMillerTheorem : NSKatoConfinementMillerBlocker

canonicalNSKatoConfinementMillerBlockers : List NSKatoConfinementMillerBlocker
canonicalNSKatoConfinementMillerBlockers =
  millerCriterionGapCertificateMissing
  ∷ millerCriterionTaylorMinimaxControlMissing
  ∷ millerCriterionNoIndependentMillerTheorem
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
  "Core sign gate is recorded as λ2 < 0 for the confined vortex-core region."

crossDerivativeNegativeText : String
crossDerivativeNegativeText =
  "Cross-derivative curvature is recorded as K = T e1 (T e2 λ2) with the shape requirement K < 0."

confinementRadiusText : String
confinementRadiusText =
  "Confinement radius is recorded as a shape formula only: r* = delta0 / K."

millerBlockerText : String
millerBlockerText =
  "Miller-criterion promotion is blocked until an independent Miller-style theorem, gap certificate, and Taylor/minimax control are provided."

record NSKatoConfinementLemmaORCSLPGF : Set where
  constructor mkNSKatoConfinementLemmaORCSLPGF
  field
    O : String
    OIsCanonical : O ≡
      "O: Record a fail-closed Kato strain-eigenvalue Hessian identity and vortex-core confinement shape receipt."

    R : String
    RIsCanonical : R ≡
      "R: Record shape-only Kato identity, distinct eigenvalue gaps, λ2 < 0, K = T e1 (T e2 λ2) < 0, and r* = delta0 / K while keeping Miller-criterion promotion explicit blockers."

    C : String
    CIsCanonical : C ≡
      "C: This module exports route/shape tokens, blocker ledger, and explicit fail-closed promotion guards."

    S : String
    SIsCanonical : S ≡
      "S: Kato identity=true; distinct-gap assumption=true; lambda2<0=true; K<0=true; r*=delta0/K recorded; Miller blockers recorded."

    L : String
    LIsCanonical : L ≡
      "L: Kato route -> gap separation -> λ2<0 -> K<0 -> formal confinement-radius output."

    P : String
    PIsCanonical : P ≡
      "P: Keep this as a shape/receipt layer only. No Miller criterion theorem is promoted."

    G : String
    GIsCanonical : G ≡
      "G: No Clay or terminal promotion and no fake local theorem promotion are introduced."

    F : String
    FIsCanonical : F ≡
      "F: Promotion remains blocked by the explicit Miller blockers: gap certificate missing, minimax control missing, no independent Miller theorem."

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

    millerBlockers :
      List NSKatoConfinementMillerBlocker

    millerBlockersAreCanonical :
      millerBlockers ≡ canonicalNSKatoConfinementMillerBlockers

    millerBlockerExplanation :
      String

    millerBlockerExplanationIsCanonical :
      millerBlockerExplanation ≡ millerBlockerText

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
    "R: Record shape-only Kato identity, distinct eigenvalue gaps, λ2 < 0, K = T e1 (T e2 λ2) < 0, and r* = delta0 / K while keeping Miller-criterion promotion explicit blockers."
    refl
    "C: This module exports route/shape tokens, blocker ledger, and explicit fail-closed promotion guards."
    refl
    "S: Kato identity=true; distinct-gap assumption=true; lambda2<0=true; K<0=true; r*=delta0/K recorded; Miller blockers recorded."
    refl
    "L: Kato route -> gap separation -> λ2<0 -> K<0 -> formal confinement-radius output."
    refl
    "P: Keep this as a shape/receipt layer only. No Miller criterion theorem is promoted."
    refl
    "G: No Clay or terminal promotion and no fake local theorem promotion are introduced."
    refl
    "F: Promotion remains blocked by the explicit Miller blockers: gap certificate missing, minimax control missing, no independent Miller theorem."
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
    ; millerBlockers =
        canonicalNSKatoConfinementMillerBlockers
    ; millerBlockersAreCanonical =
        refl
    ; millerBlockerExplanation =
        millerBlockerText
    ; millerBlockerExplanationIsCanonical =
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
