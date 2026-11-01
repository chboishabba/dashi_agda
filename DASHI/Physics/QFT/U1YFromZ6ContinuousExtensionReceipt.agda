module DASHI.Physics.QFT.U1YFromZ6ContinuousExtensionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- U(1)_Y from Z/6 continuous-extension candidate receipt.
--
-- This receipt records a candidate route from the p3 Z/6 finite sector to a
-- continuous U(1) hypercharge action by a U(1)/Hecke-circle extension.  The
-- extension is only a candidate surface; exact U(1)_Y, exact Standard Model,
-- and G_DHR ~= G_SM promotion remain false.

data Z6ContinuousExtensionStatus : Set where
  candidateU1HeckeCircleExtensionOfP3Z6 :
    Z6ContinuousExtensionStatus

data P3Z6FiniteSector : Set where
  p3Z6FiniteSector :
    P3Z6FiniteSector

data ContinuousActionCandidate : Set where
  u1CircleActionCandidate :
    ContinuousActionCandidate

  heckeCircleActionCandidate :
    ContinuousActionCandidate

canonicalContinuousActionCandidates :
  List ContinuousActionCandidate
canonicalContinuousActionCandidates =
  u1CircleActionCandidate
  ∷ heckeCircleActionCandidate
  ∷ []

z6Order :
  Nat
z6Order =
  6

p3Z6SectorLabel :
  String
p3Z6SectorLabel =
  "p3 finite hypercharge seed is recorded as a Z/6 sector"

u1ExtensionCandidateLabel :
  String
u1ExtensionCandidateLabel =
  "U(1) is recorded as a candidate continuous extension of the finite Z/6 phase action"

heckeCircleActionLabel :
  String
heckeCircleActionLabel =
  "the Hecke-circle action is recorded as the candidate bridge from p3 Z/6 to U(1)"

normalisationOpenLabel :
  String
normalisationOpenLabel =
  "hypercharge normalisation and exact Standard Model charge assignment remain open"

candidateOnlyBoundaryLabel :
  String
candidateOnlyBoundaryLabel =
  "continuous U1Y extension is candidate-only; exact gauge, Standard Model, and G_DHR ~= G_SM flags remain false"

canonicalU1YFromZ6ContinuousExtensionBoundary :
  List String
canonicalU1YFromZ6ContinuousExtensionBoundary =
  p3Z6SectorLabel
  ∷ u1ExtensionCandidateLabel
  ∷ heckeCircleActionLabel
  ∷ normalisationOpenLabel
  ∷ candidateOnlyBoundaryLabel
  ∷ []

record U1YFromZ6ContinuousExtensionReceipt : Set where
  field
    status :
      Z6ContinuousExtensionStatus

    statusIsCandidateU1HeckeCircleExtension :
      status ≡ candidateU1HeckeCircleExtensionOfP3Z6

    finiteSector :
      P3Z6FiniteSector

    finiteSectorIsP3Z6 :
      finiteSector ≡ p3Z6FiniteSector

    finiteSectorOrder :
      Nat

    finiteSectorOrderIsSix :
      finiteSectorOrder ≡ z6Order

    p3Z6SeedPresent :
      Bool

    p3Z6SeedPresentIsTrue :
      p3Z6SeedPresent ≡ true

    continuousActionCandidates :
      List ContinuousActionCandidate

    continuousActionCandidatesAreCanonical :
      continuousActionCandidates ≡ canonicalContinuousActionCandidates

    u1CircleActionCandidatePresent :
      Bool

    u1CircleActionCandidatePresentIsTrue :
      u1CircleActionCandidatePresent ≡ true

    heckeCircleActionCandidatePresent :
      Bool

    heckeCircleActionCandidatePresentIsTrue :
      heckeCircleActionCandidatePresent ≡ true

    candidateContinuousExtension :
      Bool

    candidateContinuousExtensionIsTrue :
      candidateContinuousExtension ≡ true

    exactContinuousU1YConstructed :
      Bool

    exactContinuousU1YConstructedIsFalse :
      exactContinuousU1YConstructed ≡ false

    exactHyperchargeNormalisationDerived :
      Bool

    exactHyperchargeNormalisationDerivedIsFalse :
      exactHyperchargeNormalisationDerived ≡ false

    exactGaugePromotion :
      Bool

    exactGaugePromotionIsFalse :
      exactGaugePromotion ≡ false

    exactU1YPromotion :
      Bool

    exactU1YPromotionIsFalse :
      exactU1YPromotion ≡ false

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    exactGDHREqualsGSMPromotion :
      Bool

    exactGDHREqualsGSMPromotionIsFalse :
      exactGDHREqualsGSMPromotion ≡ false

    p3Z6SectorBoundary :
      String

    p3Z6SectorBoundaryIsCanonical :
      p3Z6SectorBoundary ≡ p3Z6SectorLabel

    u1ExtensionCandidateBoundary :
      String

    u1ExtensionCandidateBoundaryIsCanonical :
      u1ExtensionCandidateBoundary ≡ u1ExtensionCandidateLabel

    heckeCircleActionBoundary :
      String

    heckeCircleActionBoundaryIsCanonical :
      heckeCircleActionBoundary ≡ heckeCircleActionLabel

    normalisationOpenBoundary :
      String

    normalisationOpenBoundaryIsCanonical :
      normalisationOpenBoundary ≡ normalisationOpenLabel

    candidateOnlyBoundary :
      String

    candidateOnlyBoundaryIsCanonical :
      candidateOnlyBoundary ≡ candidateOnlyBoundaryLabel

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalU1YFromZ6ContinuousExtensionBoundary

open U1YFromZ6ContinuousExtensionReceipt public

canonicalU1YFromZ6ContinuousExtensionReceipt :
  U1YFromZ6ContinuousExtensionReceipt
canonicalU1YFromZ6ContinuousExtensionReceipt =
  record
    { status =
        candidateU1HeckeCircleExtensionOfP3Z6
    ; statusIsCandidateU1HeckeCircleExtension =
        refl
    ; finiteSector =
        p3Z6FiniteSector
    ; finiteSectorIsP3Z6 =
        refl
    ; finiteSectorOrder =
        z6Order
    ; finiteSectorOrderIsSix =
        refl
    ; p3Z6SeedPresent =
        true
    ; p3Z6SeedPresentIsTrue =
        refl
    ; continuousActionCandidates =
        canonicalContinuousActionCandidates
    ; continuousActionCandidatesAreCanonical =
        refl
    ; u1CircleActionCandidatePresent =
        true
    ; u1CircleActionCandidatePresentIsTrue =
        refl
    ; heckeCircleActionCandidatePresent =
        true
    ; heckeCircleActionCandidatePresentIsTrue =
        refl
    ; candidateContinuousExtension =
        true
    ; candidateContinuousExtensionIsTrue =
        refl
    ; exactContinuousU1YConstructed =
        false
    ; exactContinuousU1YConstructedIsFalse =
        refl
    ; exactHyperchargeNormalisationDerived =
        false
    ; exactHyperchargeNormalisationDerivedIsFalse =
        refl
    ; exactGaugePromotion =
        false
    ; exactGaugePromotionIsFalse =
        refl
    ; exactU1YPromotion =
        false
    ; exactU1YPromotionIsFalse =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; exactGDHREqualsGSMPromotion =
        false
    ; exactGDHREqualsGSMPromotionIsFalse =
        refl
    ; p3Z6SectorBoundary =
        p3Z6SectorLabel
    ; p3Z6SectorBoundaryIsCanonical =
        refl
    ; u1ExtensionCandidateBoundary =
        u1ExtensionCandidateLabel
    ; u1ExtensionCandidateBoundaryIsCanonical =
        refl
    ; heckeCircleActionBoundary =
        heckeCircleActionLabel
    ; heckeCircleActionBoundaryIsCanonical =
        refl
    ; normalisationOpenBoundary =
        normalisationOpenLabel
    ; normalisationOpenBoundaryIsCanonical =
        refl
    ; candidateOnlyBoundary =
        candidateOnlyBoundaryLabel
    ; candidateOnlyBoundaryIsCanonical =
        refl
    ; receiptBoundary =
        canonicalU1YFromZ6ContinuousExtensionBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

u1YFromZ6FiniteSectorOrderIsSix :
  finiteSectorOrder canonicalU1YFromZ6ContinuousExtensionReceipt
  ≡
  6
u1YFromZ6FiniteSectorOrderIsSix =
  refl

u1YFromZ6CandidateContinuousExtensionPresent :
  candidateContinuousExtension canonicalU1YFromZ6ContinuousExtensionReceipt
  ≡
  true
u1YFromZ6CandidateContinuousExtensionPresent =
  refl

u1YFromZ6ExactContinuousU1YFalse :
  exactContinuousU1YConstructed canonicalU1YFromZ6ContinuousExtensionReceipt
  ≡
  false
u1YFromZ6ExactContinuousU1YFalse =
  refl

u1YFromZ6ExactGaugePromotionFalse :
  exactGaugePromotion canonicalU1YFromZ6ContinuousExtensionReceipt
  ≡
  false
u1YFromZ6ExactGaugePromotionFalse =
  refl

u1YFromZ6ExactSMFalse :
  exactStandardModelPromotion canonicalU1YFromZ6ContinuousExtensionReceipt
  ≡
  false
u1YFromZ6ExactSMFalse =
  refl

u1YFromZ6ExactGDHRGSMFalse :
  exactGDHREqualsGSMPromotion canonicalU1YFromZ6ContinuousExtensionReceipt
  ≡
  false
u1YFromZ6ExactGDHRGSMFalse =
  refl
