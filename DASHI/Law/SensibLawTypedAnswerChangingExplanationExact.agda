module DASHI.Law.SensibLawTypedAnswerChangingExplanationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawChangeLocusExact as Locus
import DASHI.Law.SensibLawPabaiComparativeWorldExact as Pabai

------------------------------------------------------------------------
-- M11.2 TYPED MINIMAL ANSWER-CHANGING EXPLANATION
--
-- Minimality says WHICH admitted input atom changes the answer/route.
-- The explanation layer additionally records WHERE the atom entered and the
-- reviewed dependency/reason that connects it to the changed route.
------------------------------------------------------------------------

record AnswerChangeStep : Set where
  constructor answer-change-step
  field
    deltaRef : String
    layer : Locus.ChangeLayer
    coordinateRef : String
    routeRef : String
    explanationRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsClaimTruth : Bool
    createsClaimTruthIsFalse : createsClaimTruth ≡ false

open AnswerChangeStep public

pabaiDefeaterStep : AnswerChangeStep
pabaiDefeaterStep =
  answer-change-step
    "delta:pabai:w0-w1:defeater"
    Locus.applicabilityLayer
    "coordinate:pabai:comparative:defeater"
    "route:pabai:comparative-duty"
    "reviewed core-policy defeater enters applicability and blocks the candidate route"
    true refl
    false refl

pabaiCounterStep : AnswerChangeStep
pabaiCounterStep =
  answer-change-step
    "delta:pabai:w1-w2:counter-defeater"
    Locus.applicabilityLayer
    "coordinate:pabai:comparative:counter-defeater"
    "route:pabai:comparative-duty"
    "reviewed counter-distinction reopens the candidate route for fresh defeater search"
    true refl
    false refl

pabaiDefeaterStillExactMinimalAtom :
  Pabai.applyFromW0 Pabai.corePolicyDefeaterD
  ≡ Pabai.routeStatus Pabai.w1DefeaterAdmitted
pabaiDefeaterStillExactMinimalAtom =
  Pabai.w0ToW1ExactDistinction

pabaiCounterStillExactMinimalAtom :
  Pabai.applyFromW1 Pabai.counterDistinctionC
  ≡ Pabai.routeStatus Pabai.w2CounterCandidate
pabaiCounterStillExactMinimalAtom =
  Pabai.w1ToW2ExactDistinction

data ExplanationPromotesDifferenceToCausation : Set where
data ExplanationPredictsJudicialOutcome : Set where
data MissingTypedLocusMayBeSilentlyFilled : Set where
data ExplanationCreatesClaimTruth : Set where

explanationDoesNotPromoteDifferenceToCausation :
  ExplanationPromotesDifferenceToCausation → ⊥
explanationDoesNotPromoteDifferenceToCausation ()

explanationDoesNotPredictJudicialOutcome :
  ExplanationPredictsJudicialOutcome → ⊥
explanationDoesNotPredictJudicialOutcome ()

missingTypedLocusRemainsUnresolved :
  MissingTypedLocusMayBeSilentlyFilled → ⊥
missingTypedLocusRemainsUnresolved ()

explanationDoesNotCreateTruth :
  ExplanationCreatesClaimTruth → ⊥
explanationDoesNotCreateTruth ()

record TypedAnswerExplanationBoundary : Set where
  constructor typedAnswerExplanationBoundary
  field
    minimalAtomCarriesChangeLayer : Bool
    minimalAtomCarriesChangeLayerIsTrue :
      minimalAtomCarriesChangeLayer ≡ true

    explanationRequiresTypedLocus : Bool
    explanationRequiresTypedLocusIsTrue :
      explanationRequiresTypedLocus ≡ true

    explanationRequiresDependencyReason : Bool
    explanationRequiresDependencyReasonIsTrue :
      explanationRequiresDependencyReason ≡ true

    missingLocusIsSilentlyInferred : Bool
    missingLocusIsSilentlyInferredIsFalse :
      missingLocusIsSilentlyInferred ≡ false

    explanationPredictsOutcome : Bool
    explanationPredictsOutcomeIsFalse :
      explanationPredictsOutcome ≡ false

    explanationCreatesTruth : Bool
    explanationCreatesTruthIsFalse :
      explanationCreatesTruth ≡ false

open TypedAnswerExplanationBoundary public

canonicalTypedAnswerExplanationBoundary : TypedAnswerExplanationBoundary
canonicalTypedAnswerExplanationBoundary =
  typedAnswerExplanationBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
