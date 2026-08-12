module DASHI.Core.ConditionalNormalizationBoundary where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerIndexedRelevanceMeasure as Relevance

------------------------------------------------------------------------
-- Conditional-normalisation boundary.
--
-- Renormalising a selected/responding subset to unit mass is not evidence that
-- the subset carries unit mass relative to the original cohort measure.  This
-- finite countermodel gives the distinction a constructive witness rather than
-- leaving it as a prose warning.
------------------------------------------------------------------------

_+N_ : Nat → Nat → Nat
zero +N n = n
suc m +N n = suc (m +N n)

one : Nat
one = suc zero

two : Nat
two = suc one

data SurveyRegion : Set where
  cohortRegion respondentRegion nonresponseRegion : SurveyRegion

data CohortConsumer : Set where
  cohortConsumer : CohortConsumer

data ConditionalRespondentConsumer : Set where
  respondentConsumer : ConditionalRespondentConsumer

cohortMass : CohortConsumer → SurveyRegion → Nat
cohortMass cohortConsumer cohortRegion = two
cohortMass cohortConsumer respondentRegion = one
cohortMass cohortConsumer nonresponseRegion = one

conditionalRespondentMass :
  ConditionalRespondentConsumer → SurveyRegion → Nat
conditionalRespondentMass respondentConsumer cohortRegion = one
conditionalRespondentMass respondentConsumer respondentRegion = one
conditionalRespondentMass respondentConsumer nonresponseRegion = zero

cohortMeasure :
  Relevance.ConsumerIndexedRelevanceMeasure
    CohortConsumer SurveyRegion Nat
cohortMeasure =
  Relevance.consumerIndexedRelevanceMeasure
    Relevance.consumerRelevanceMass
    cohortRegion
    zero
    two
    _+N_
    cohortMass
    (λ { cohortConsumer → refl })

conditionalRespondentMeasure :
  Relevance.ConsumerIndexedRelevanceMeasure
    ConditionalRespondentConsumer SurveyRegion Nat
conditionalRespondentMeasure =
  Relevance.consumerIndexedRelevanceMeasure
    Relevance.consumerRelevanceMass
    respondentRegion
    zero
    one
    _+N_
    conditionalRespondentMass
    (λ { respondentConsumer → refl })

conditionalRespondentRegionIsUnit :
  Relevance.relevanceMass
    conditionalRespondentMeasure respondentConsumer respondentRegion
  ≡ Relevance.unitMass conditionalRespondentMeasure
conditionalRespondentRegionIsUnit = refl

oneIsNotTwo : one ≡ two → ⊥
oneIsNotTwo ()

respondentRegionIsNotWholeCohortMass :
  Relevance.relevanceMass cohortMeasure cohortConsumer respondentRegion
  ≡ Relevance.unitMass cohortMeasure →
  ⊥
respondentRegionIsNotWholeCohortMass = oneIsNotTwo

record ConditionalNormalizationCounterexample : Set where
  constructor conditionalNormalizationCounterexample
  field
    selectedSubsetRenormalizesToUnit :
      Relevance.relevanceMass
        conditionalRespondentMeasure respondentConsumer respondentRegion
      ≡ Relevance.unitMass conditionalRespondentMeasure
    selectedSubsetDoesNotCarryOriginalUnit :
      Relevance.relevanceMass cohortMeasure cohortConsumer respondentRegion
      ≡ Relevance.unitMass cohortMeasure →
      ⊥

open ConditionalNormalizationCounterexample public

canonicalConditionalNormalizationCounterexample :
  ConditionalNormalizationCounterexample
canonicalConditionalNormalizationCounterexample =
  conditionalNormalizationCounterexample
    conditionalRespondentRegionIsUnit
    respondentRegionIsNotWholeCohortMass
