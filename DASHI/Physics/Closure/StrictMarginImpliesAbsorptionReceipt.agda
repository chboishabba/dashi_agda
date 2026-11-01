module DASHI.Physics.Closure.StrictMarginImpliesAbsorptionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Shared L0 margin grammar.
--
-- This receipt records the domain-independent core used by the NS theta,
-- YM rho, Gate 3 frame, and dialectical carry lanes.  It deliberately does
-- not prove any lane-specific estimate.  A concrete lane must first
-- inhabit the dynamics bound, actual-ratio, absorber-positivity, and
-- strict-margin fields before it can consume the absorption conclusion.

data L0MarginStatus : Set where
  l0MarginGrammarRecordedFailClosed :
    L0MarginStatus

data L0Lemma : Set where
  l0OneDynamicsBound :
    L0Lemma

  l0TwoSignedMarginEquivalentToRatio :
    L0Lemma

  l0ThreeStrictMarginImpliesAbsorption :
    L0Lemma

  l0FourFailClosedNonPromotion :
    L0Lemma

canonicalL0Lemmas : List L0Lemma
canonicalL0Lemmas =
  l0OneDynamicsBound
  ∷ l0TwoSignedMarginEquivalentToRatio
  ∷ l0ThreeStrictMarginImpliesAbsorption
  ∷ l0FourFailClosedNonPromotion
  ∷ []

data MarginQuantity : Set where
  residual :
    MarginQuantity

  production :
    MarginQuantity

  absorption :
    MarginQuantity

  marginRatio :
    MarginQuantity

  signedMargin :
    MarginQuantity

canonicalMarginQuantities : List MarginQuantity
canonicalMarginQuantities =
  residual
  ∷ production
  ∷ absorption
  ∷ marginRatio
  ∷ signedMargin
  ∷ []

data MarginPremise : Set where
  residualDerivativeBoundedByProductionMinusAbsorption :
    MarginPremise

  productionBoundedByThetaTimesAbsorption :
    MarginPremise

  thetaStrictlyBelowOne :
    MarginPremise

  absorberStrengthPositive :
    MarginPremise

canonicalStrictMarginPremises : List MarginPremise
canonicalStrictMarginPremises =
  residualDerivativeBoundedByProductionMinusAbsorption
  ∷ productionBoundedByThetaTimesAbsorption
  ∷ thetaStrictlyBelowOne
  ∷ absorberStrengthPositive
  ∷ []

data MarginConclusion : Set where
  residualDerivativeStrictlyNegative :
    MarginConclusion

  residualDerivativeBoundedByNegativeMarginAbsorption :
    MarginConclusion

canonicalStrictMarginConclusions : List MarginConclusion
canonicalStrictMarginConclusions =
  residualDerivativeStrictlyNegative
  ∷ residualDerivativeBoundedByNegativeMarginAbsorption
  ∷ []

data RatioSignedEquivalenceCondition : Set where
  absorptionPositiveRequired :
    RatioSignedEquivalenceCondition

  ratioIsActualProductionOverAbsorption :
    RatioSignedEquivalenceCondition

  signedIsActualAbsorptionMinusProduction :
    RatioSignedEquivalenceCondition

canonicalRatioSignedEquivalenceConditions :
  List RatioSignedEquivalenceCondition
canonicalRatioSignedEquivalenceConditions =
  absorptionPositiveRequired
  ∷ ratioIsActualProductionOverAbsorption
  ∷ signedIsActualAbsorptionMinusProduction
  ∷ []

data FailClosedPromotionGate : Set where
  diagnosticIsNotTheorem :
    FailClosedPromotionGate

  toyRatioIsNotAnalyticMargin :
    FailClosedPromotionGate

  finiteFrameIsNotContinuumDensity :
    FailClosedPromotionGate

  observedMarginIsNotProvedMargin :
    FailClosedPromotionGate

  carrierGapIsNotContinuumGap :
    FailClosedPromotionGate

canonicalFailClosedPromotionGates : List FailClosedPromotionGate
canonicalFailClosedPromotionGates =
  diagnosticIsNotTheorem
  ∷ toyRatioIsNotAnalyticMargin
  ∷ finiteFrameIsNotContinuumDensity
  ∷ observedMarginIsNotProvedMargin
  ∷ carrierGapIsNotContinuumGap
  ∷ []

data FailClosedMarginRequirement : Set where
  actualProductionOverActualAbsorption :
    FailClosedMarginRequirement

  actualAbsorptionPositive :
    FailClosedMarginRequirement

  strictMarginProvedNotMerelyObserved :
    FailClosedMarginRequirement

  laneDynamicsBoundDischarged :
    FailClosedMarginRequirement

canonicalFailClosedMarginRequirements :
  List FailClosedMarginRequirement
canonicalFailClosedMarginRequirements =
  actualProductionOverActualAbsorption
  ∷ actualAbsorptionPositive
  ∷ strictMarginProvedNotMerelyObserved
  ∷ laneDynamicsBoundDischarged
  ∷ []

data MarginAbsorptionPromotion : Set where

marginAbsorptionPromotionImpossibleHere :
  MarginAbsorptionPromotion →
  ⊥
marginAbsorptionPromotionImpossibleHere ()

strictMarginFormula : String
strictMarginFormula =
  "R'(t) <= P(t)-A(t), P(t) <= theta*A(t), theta<1, A(t)>0 => R'(t) <= -(1-theta)*A(t) < 0."

ratioSignedFormula : String
ratioSignedFormula =
  "A(t)>0 and ratio=P/A and signed=A-P imply ratio<1 iff signed>0."

failClosedFormula : String
failClosedFormula =
  "No lane may consume absorption unless ratio is actual, absorption is positive, the margin is proved, and the lane dynamics bound is discharged."

record MarginFunctional : Setω where
  field
    State :
      Set

    Scalar :
      Set

    Residual :
      State → Scalar

    Production :
      State → Scalar

    Absorption :
      State → Scalar

    ratio :
      State → Scalar

    signed :
      State → Scalar

    -- Domain-specific propositions.  This core receipt does not choose an
    -- ordered scalar implementation; each analytic lane supplies its own.
    dynamicsBound :
      State → Set

    actualRatio :
      State → Set

    actualSigned :
      State → Set

    absorberPositive :
      State → Set

    ratioBelowOne :
      State → Set

    signedPositive :
      State → Set

    residualAbsorbs :
      State → Set

    ratioSignedEquiv :
      ∀ s →
      absorberPositive s →
      actualRatio s →
      actualSigned s →
      ratioBelowOne s →
      signedPositive s

    strictMarginImpliesAbsorption :
      ∀ s →
      dynamicsBound s →
      actualRatio s →
      absorberPositive s →
      ratioBelowOne s →
      residualAbsorbs s

record StrictMarginImpliesAbsorptionReceipt : Setω where
  field
    status :
      L0MarginStatus

    statusIsFailClosed :
      status ≡ l0MarginGrammarRecordedFailClosed

    lemmas :
      List L0Lemma

    lemmasAreCanonical :
      lemmas ≡ canonicalL0Lemmas

    quantities :
      List MarginQuantity

    quantitiesAreCanonical :
      quantities ≡ canonicalMarginQuantities

    strictMarginPremises :
      List MarginPremise

    strictMarginPremisesAreCanonical :
      strictMarginPremises ≡ canonicalStrictMarginPremises

    strictMarginConclusions :
      List MarginConclusion

    strictMarginConclusionsAreCanonical :
      strictMarginConclusions ≡ canonicalStrictMarginConclusions

    ratioSignedEquivalenceConditions :
      List RatioSignedEquivalenceCondition

    ratioSignedEquivalenceConditionsAreCanonical :
      ratioSignedEquivalenceConditions
      ≡
      canonicalRatioSignedEquivalenceConditions

    failClosedRequirements :
      List FailClosedMarginRequirement

    failClosedRequirementsAreCanonical :
      failClosedRequirements ≡ canonicalFailClosedMarginRequirements

    promotionGates :
      List FailClosedPromotionGate

    promotionGatesAreCanonical :
      promotionGates ≡ canonicalFailClosedPromotionGates

    dynamicsBoundIsLoadBearing :
      Bool

    dynamicsBoundIsLoadBearingIsTrue :
      dynamicsBoundIsLoadBearing ≡ true

    absorberPositivityIsLoadBearing :
      Bool

    absorberPositivityIsLoadBearingIsTrue :
      absorberPositivityIsLoadBearing ≡ true

    ratioMustBeActualNotToy :
      Bool

    ratioMustBeActualNotToyIsTrue :
      ratioMustBeActualNotToy ≡ true

    observedMarginCannotPromote :
      Bool

    observedMarginCannotPromoteIsTrue :
      observedMarginCannotPromote ≡ true

    provesNSRegularity :
      Bool

    provesNSRegularityIsFalse :
      provesNSRegularity ≡ false

    provesYMMassGap :
      Bool

    provesYMMassGapIsFalse :
      provesYMMassGap ≡ false

    provesGate3ContinuumLift :
      Bool

    provesGate3ContinuumLiftIsFalse :
      provesGate3ContinuumLift ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    strictMarginFormulaRecorded :
      String

    strictMarginFormulaRecordedIsCanonical :
      strictMarginFormulaRecorded ≡ strictMarginFormula

    ratioSignedFormulaRecorded :
      String

    ratioSignedFormulaRecordedIsCanonical :
      ratioSignedFormulaRecorded ≡ ratioSignedFormula

    failClosedFormulaRecorded :
      String

    failClosedFormulaRecordedIsCanonical :
      failClosedFormulaRecorded ≡ failClosedFormula

canonicalStrictMarginImpliesAbsorptionReceipt :
  StrictMarginImpliesAbsorptionReceipt
canonicalStrictMarginImpliesAbsorptionReceipt =
  record
    { status =
        l0MarginGrammarRecordedFailClosed
    ; statusIsFailClosed =
        refl
    ; lemmas =
        canonicalL0Lemmas
    ; lemmasAreCanonical =
        refl
    ; quantities =
        canonicalMarginQuantities
    ; quantitiesAreCanonical =
        refl
    ; strictMarginPremises =
        canonicalStrictMarginPremises
    ; strictMarginPremisesAreCanonical =
        refl
    ; strictMarginConclusions =
        canonicalStrictMarginConclusions
    ; strictMarginConclusionsAreCanonical =
        refl
    ; ratioSignedEquivalenceConditions =
        canonicalRatioSignedEquivalenceConditions
    ; ratioSignedEquivalenceConditionsAreCanonical =
        refl
    ; failClosedRequirements =
        canonicalFailClosedMarginRequirements
    ; failClosedRequirementsAreCanonical =
        refl
    ; promotionGates =
        canonicalFailClosedPromotionGates
    ; promotionGatesAreCanonical =
        refl
    ; dynamicsBoundIsLoadBearing =
        true
    ; dynamicsBoundIsLoadBearingIsTrue =
        refl
    ; absorberPositivityIsLoadBearing =
        true
    ; absorberPositivityIsLoadBearingIsTrue =
        refl
    ; ratioMustBeActualNotToy =
        true
    ; ratioMustBeActualNotToyIsTrue =
        refl
    ; observedMarginCannotPromote =
        true
    ; observedMarginCannotPromoteIsTrue =
        refl
    ; provesNSRegularity =
        false
    ; provesNSRegularityIsFalse =
        refl
    ; provesYMMassGap =
        false
    ; provesYMMassGapIsFalse =
        refl
    ; provesGate3ContinuumLift =
        false
    ; provesGate3ContinuumLiftIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; strictMarginFormulaRecorded =
        strictMarginFormula
    ; strictMarginFormulaRecordedIsCanonical =
        refl
    ; ratioSignedFormulaRecorded =
        ratioSignedFormula
    ; ratioSignedFormulaRecordedIsCanonical =
        refl
    ; failClosedFormulaRecorded =
        failClosedFormula
    ; failClosedFormulaRecordedIsCanonical =
        refl
    }

l0DynamicsBoundIsLoadBearing :
  StrictMarginImpliesAbsorptionReceipt.dynamicsBoundIsLoadBearing
    canonicalStrictMarginImpliesAbsorptionReceipt
  ≡
  true
l0DynamicsBoundIsLoadBearing =
  refl

l0ClayPromotionStillFalse :
  StrictMarginImpliesAbsorptionReceipt.clayPromotion
    canonicalStrictMarginImpliesAbsorptionReceipt
  ≡
  false
l0ClayPromotionStillFalse =
  refl
