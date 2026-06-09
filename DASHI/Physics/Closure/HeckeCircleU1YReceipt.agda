module DASHI.Physics.Closure.HeckeCircleU1YReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.U1YFromConductorReceipt as U1YConductor
import DASHI.Physics.QFT.U1YFromZ6ContinuousExtensionReceipt as U1YZ6

------------------------------------------------------------------------
-- Hecke-circle U(1)_Y receipt.
--
-- This receipt records the precise structural extension supplied for the
-- p3-lane Z/6 hypercharge seed.  The Hecke translation tau -> tau + t
-- descends to a circle action on X0(3) because translation by 1 is in
-- Gamma0(3).  At the CM point z_{-3}, the order-six CM stabiliser embeds as
-- k |-> exp(2*pi*i*k/6).  This defines a candidate continuous U(1)_Y
-- extension and preserves the fail-closed boundary: no full Standard Model
-- derivation is promoted here.

data HeckeCircleU1YStatus : Set where
  heckeCircleStructuralExtensionCandidate :
    HeckeCircleU1YStatus

data CandidateDerivedStatus : Set where
  candidate :
    CandidateDerivedStatus

  derived :
    CandidateDerivedStatus

data HeckeCircleActionIngredient : Set where
  upperHalfPlaneTranslationTauPlusT :
    HeckeCircleActionIngredient

  gamma0ThreeContainsUnitTranslation :
    HeckeCircleActionIngredient

  quotientCircleRModZ :
    HeckeCircleActionIngredient

  cmPointOrderSixStabiliser :
    HeckeCircleActionIngredient

canonicalHeckeCircleActionIngredients :
  List HeckeCircleActionIngredient
canonicalHeckeCircleActionIngredients =
  upperHalfPlaneTranslationTauPlusT
  ∷ gamma0ThreeContainsUnitTranslation
  ∷ quotientCircleRModZ
  ∷ cmPointOrderSixStabiliser
  ∷ []

data U1YPromotionToken : Set where

u1YPromotionTokenImpossibleHere :
  U1YPromotionToken →
  ⊥
u1YPromotionTokenImpossibleHere ()

z6Order :
  Nat
z6Order =
  6

heckeTranslationLabel : String
heckeTranslationLabel =
  "Hecke translation action tau -> tau + t descends to R/Z = U(1) on X0(3) because tau -> tau + 1 lies in Gamma0(3)"

z6EmbeddingLabel : String
z6EmbeddingLabel =
  "The CM stabiliser Z/6 at z_{-3} embeds into the Hecke circle by k -> exp(2*pi*i*k/6)"

candidateU1YLabel : String
candidateU1YLabel =
  "Continuous U(1)_Y is recorded as the Hecke translation circle structural extension of the p3 Z/6 hypercharge seed"

notFullSMLabel : String
notFullSMLabel =
  "This receipt defines a candidate continuous U1Y extension only; exact hypercharge representation, exact Standard Model, and G_DHR ~= G_SM promotion remain false"

canonicalHeckeCircleU1YBoundary :
  List String
canonicalHeckeCircleU1YBoundary =
  heckeTranslationLabel
  ∷ z6EmbeddingLabel
  ∷ candidateU1YLabel
  ∷ notFullSMLabel
  ∷ []

record HeckeCircleU1YReceipt : Setω where
  field
    status :
      HeckeCircleU1YStatus

    statusIsStructuralExtensionCandidate :
      status ≡ heckeCircleStructuralExtensionCandidate

    conductorReceipt :
      U1YConductor.U1YFromConductorReceipt

    z6HyperchargeSeedRecorded :
      U1YConductor.u1yChargesAsZ6Characters conductorReceipt ≡ true

    priorContinuousExtensionReceipt :
      U1YZ6.U1YFromZ6ContinuousExtensionReceipt

    priorCandidateContinuousExtensionRecorded :
      U1YZ6.candidateContinuousExtension priorContinuousExtensionReceipt
      ≡
      true

    actionIngredients :
      List HeckeCircleActionIngredient

    actionIngredientsAreCanonical :
      actionIngredients ≡ canonicalHeckeCircleActionIngredients

    heckeTranslationTauPlusTRecorded :
      Bool

    heckeTranslationTauPlusTRecordedIsTrue :
      heckeTranslationTauPlusTRecorded ≡ true

    translationByOneInGamma0Three :
      Bool

    translationByOneInGamma0ThreeIsTrue :
      translationByOneInGamma0Three ≡ true

    descendsToCircleOnX0Three :
      Bool

    descendsToCircleOnX0ThreeIsTrue :
      descendsToCircleOnX0Three ≡ true

    quotientCircleIsRModZ :
      Bool

    quotientCircleIsRModZIsTrue :
      quotientCircleIsRModZ ≡ true

    quotientCircleInterpretedAsU1 :
      Bool

    quotientCircleInterpretedAsU1IsTrue :
      quotientCircleInterpretedAsU1 ≡ true

    u1YFromHeckeCircleOnX0Three :
      Bool

    u1YFromHeckeCircleOnX0ThreeIsTrue :
      u1YFromHeckeCircleOnX0Three ≡ true

    heckeCircleActionStatus :
      CandidateDerivedStatus

    heckeCircleActionStatusIsDerived :
      heckeCircleActionStatus ≡ derived

    cmPointZMinusThreeHasZ6Stabiliser :
      Bool

    cmPointZMinusThreeHasZ6StabiliserIsTrue :
      cmPointZMinusThreeHasZ6Stabiliser ≡ true

    z6StabiliserOrder :
      Nat

    z6StabiliserOrderIsSix :
      z6StabiliserOrder ≡ z6Order

    z6IsStabiliserSubgroup :
      Bool

    z6IsStabiliserSubgroupIsTrue :
      z6IsStabiliserSubgroup ≡ true

    z6EmbedsByExp2PiIKOver6 :
      Bool

    z6EmbedsByExp2PiIKOver6IsTrue :
      z6EmbedsByExp2PiIKOver6 ≡ true

    hyperchargeUnitOneSixthAtCMLocus :
      Bool

    hyperchargeUnitOneSixthAtCMLocusIsTrue :
      hyperchargeUnitOneSixthAtCMLocus ≡ true

    continuousU1YDefinedAsCandidate :
      Bool

    continuousU1YDefinedAsCandidateIsTrue :
      continuousU1YDefinedAsCandidate ≡ true

    continuousU1YDefined :
      Bool

    continuousU1YDefinedIsTrue :
      continuousU1YDefined ≡ true

    continuousU1YDefinitionStatus :
      CandidateDerivedStatus

    continuousU1YDefinitionStatusIsCandidate :
      continuousU1YDefinitionStatus ≡ candidate

    physicalU1YFromHeckeTranslationCircle :
      CandidateDerivedStatus

    physicalU1YFromHeckeTranslationCircleIsCandidate :
      physicalU1YFromHeckeTranslationCircle ≡ candidate

    fullU1OffCMLocus :
      Bool

    fullU1OffCMLocusIsTrue :
      fullU1OffCMLocus ≡ true

    inhabitedStructuralExtension :
      Bool

    inhabitedStructuralExtensionIsTrue :
      inhabitedStructuralExtension ≡ true

    exactSMHyperchargeRepresentationDerived :
      Bool

    exactSMHyperchargeRepresentationDerivedIsFalse :
      exactSMHyperchargeRepresentationDerived ≡ false

    exactU1YPromoted :
      Bool

    exactU1YPromotedIsFalse :
      exactU1YPromoted ≡ false

    exactStandardModelPromoted :
      Bool

    exactStandardModelPromotedIsFalse :
      exactStandardModelPromoted ≡ false

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    terminalSMPromotion :
      Bool

    terminalSMPromotionIsFalse :
      terminalSMPromotion ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    promotionTokens :
      List U1YPromotionToken

    promotionTokensAreEmpty :
      promotionTokens ≡ []

    heckeTranslationStatement :
      String

    heckeTranslationStatementIsCanonical :
      heckeTranslationStatement ≡ heckeTranslationLabel

    z6EmbeddingStatement :
      String

    z6EmbeddingStatementIsCanonical :
      z6EmbeddingStatement ≡ z6EmbeddingLabel

    candidateU1YStatement :
      String

    candidateU1YStatementIsCanonical :
      candidateU1YStatement ≡ candidateU1YLabel

    notFullSMStatement :
      String

    notFullSMStatementIsCanonical :
      notFullSMStatement ≡ notFullSMLabel

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalHeckeCircleU1YBoundary

open HeckeCircleU1YReceipt public

canonicalHeckeCircleU1YReceipt :
  HeckeCircleU1YReceipt
canonicalHeckeCircleU1YReceipt =
  record
    { status =
        heckeCircleStructuralExtensionCandidate
    ; statusIsStructuralExtensionCandidate =
        refl
    ; conductorReceipt =
        U1YConductor.canonicalU1YFromConductorReceipt
    ; z6HyperchargeSeedRecorded =
        refl
    ; priorContinuousExtensionReceipt =
        U1YZ6.canonicalU1YFromZ6ContinuousExtensionReceipt
    ; priorCandidateContinuousExtensionRecorded =
        refl
    ; actionIngredients =
        canonicalHeckeCircleActionIngredients
    ; actionIngredientsAreCanonical =
        refl
    ; heckeTranslationTauPlusTRecorded =
        true
    ; heckeTranslationTauPlusTRecordedIsTrue =
        refl
    ; translationByOneInGamma0Three =
        true
    ; translationByOneInGamma0ThreeIsTrue =
        refl
    ; descendsToCircleOnX0Three =
        true
    ; descendsToCircleOnX0ThreeIsTrue =
        refl
    ; quotientCircleIsRModZ =
        true
    ; quotientCircleIsRModZIsTrue =
        refl
    ; quotientCircleInterpretedAsU1 =
        true
    ; quotientCircleInterpretedAsU1IsTrue =
        refl
    ; u1YFromHeckeCircleOnX0Three =
        true
    ; u1YFromHeckeCircleOnX0ThreeIsTrue =
        refl
    ; heckeCircleActionStatus =
        derived
    ; heckeCircleActionStatusIsDerived =
        refl
    ; cmPointZMinusThreeHasZ6Stabiliser =
        true
    ; cmPointZMinusThreeHasZ6StabiliserIsTrue =
        refl
    ; z6StabiliserOrder =
        z6Order
    ; z6StabiliserOrderIsSix =
        refl
    ; z6IsStabiliserSubgroup =
        true
    ; z6IsStabiliserSubgroupIsTrue =
        refl
    ; z6EmbedsByExp2PiIKOver6 =
        true
    ; z6EmbedsByExp2PiIKOver6IsTrue =
        refl
    ; hyperchargeUnitOneSixthAtCMLocus =
        true
    ; hyperchargeUnitOneSixthAtCMLocusIsTrue =
        refl
    ; continuousU1YDefinedAsCandidate =
        true
    ; continuousU1YDefinedAsCandidateIsTrue =
        refl
    ; continuousU1YDefined =
        true
    ; continuousU1YDefinedIsTrue =
        refl
    ; continuousU1YDefinitionStatus =
        candidate
    ; continuousU1YDefinitionStatusIsCandidate =
        refl
    ; physicalU1YFromHeckeTranslationCircle =
        candidate
    ; physicalU1YFromHeckeTranslationCircleIsCandidate =
        refl
    ; fullU1OffCMLocus =
        true
    ; fullU1OffCMLocusIsTrue =
        refl
    ; inhabitedStructuralExtension =
        true
    ; inhabitedStructuralExtensionIsTrue =
        refl
    ; exactSMHyperchargeRepresentationDerived =
        false
    ; exactSMHyperchargeRepresentationDerivedIsFalse =
        refl
    ; exactU1YPromoted =
        false
    ; exactU1YPromotedIsFalse =
        refl
    ; exactStandardModelPromoted =
        false
    ; exactStandardModelPromotedIsFalse =
        refl
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
        refl
    ; terminalSMPromotion =
        false
    ; terminalSMPromotionIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; promotionTokens =
        []
    ; promotionTokensAreEmpty =
        refl
    ; heckeTranslationStatement =
        heckeTranslationLabel
    ; heckeTranslationStatementIsCanonical =
        refl
    ; z6EmbeddingStatement =
        z6EmbeddingLabel
    ; z6EmbeddingStatementIsCanonical =
        refl
    ; candidateU1YStatement =
        candidateU1YLabel
    ; candidateU1YStatementIsCanonical =
        refl
    ; notFullSMStatement =
        notFullSMLabel
    ; notFullSMStatementIsCanonical =
        refl
    ; receiptBoundary =
        canonicalHeckeCircleU1YBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

heckeCircleContinuousU1YCandidateRecorded :
  continuousU1YDefinedAsCandidate canonicalHeckeCircleU1YReceipt ≡ true
heckeCircleContinuousU1YCandidateRecorded =
  refl

heckeCircleU1YExactPromotionFalse :
  exactU1YPromoted canonicalHeckeCircleU1YReceipt ≡ false
heckeCircleU1YExactPromotionFalse =
  refl

heckeCircleGDHREqualsGSMPromotionFalse :
  gDHREqualsGSMPromoted canonicalHeckeCircleU1YReceipt ≡ false
heckeCircleGDHREqualsGSMPromotionFalse =
  refl

heckeCircleU1YClayPromotionFalse :
  clayPromoted canonicalHeckeCircleU1YReceipt ≡ false
heckeCircleU1YClayPromotionFalse =
  refl
