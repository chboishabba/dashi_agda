module DASHI.Algebra.DisagreementFourViewBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Algebra.TetralemmaBridge using
  ( TetralemmaPosition
  ; affirmation ; negation ; both ; neither
  )

------------------------------------------------------------------------
-- Two distinct fourfold structures occur in disagreement analysis.
--
-- 1. A tetralemma classifies one proposition by support for P and ¬P.
-- 2. A four-view matrix records two agents' first-order views and their
--    second-order models of each other.
--
-- They both have four named positions, but they are not the same object.

record FourViewMatrix (View : Set) : Set where
  constructor fourViews
  field
    aOwn : View
    bOwn : View
    aModelsB : View
    bModelsA : View

open FourViewMatrix public

data Party : Set where
  partyA : Party
  partyB : Party

data ViewOrder : Set where
  firstOrder : ViewOrder
  secondOrder : ViewOrder

viewAt :
  ∀ {View} →
  FourViewMatrix View →
  Party →
  Party →
  View
viewAt views partyA partyA = aOwn views
viewAt views partyA partyB = aModelsB views
viewAt views partyB partyA = bModelsA views
viewAt views partyB partyB = bOwn views

viewOrder : Party → Party → ViewOrder
viewOrder partyA partyA = firstOrder
viewOrder partyB partyB = firstOrder
viewOrder partyA partyB = secondOrder
viewOrder partyB partyA = secondOrder

diagonal-is-first-order :
  ∀ p →
  viewOrder p p ≡ firstOrder
diagonal-is-first-order partyA = refl
diagonal-is-first-order partyB = refl

a-models-b-is-second-order :
  viewOrder partyA partyB ≡ secondOrder
a-models-b-is-second-order = refl

b-models-a-is-second-order :
  viewOrder partyB partyA ≡ secondOrder
b-models-a-is-second-order = refl

------------------------------------------------------------------------
-- Tetralemma classification concerns polarity of one proposition.

record PolarAssessment : Set where
  constructor assess
  field
    supportsP : Bool
    supportsNotP : Bool

open PolarAssessment public

polarPosition : PolarAssessment → TetralemmaPosition
polarPosition (assess true false) = affirmation
polarPosition (assess false true) = negation
polarPosition (assess true true) = both
polarPosition (assess false false) = neither

affirmation-receipt :
  polarPosition (assess true false) ≡ affirmation
affirmation-receipt = refl

negation-receipt :
  polarPosition (assess false true) ≡ negation
negation-receipt = refl

both-receipt :
  polarPosition (assess true true) ≡ both
both-receipt = refl

neither-receipt :
  polarPosition (assess false false) ≡ neither
neither-receipt = refl

------------------------------------------------------------------------
-- Logical appraisal and practical efficacy are independent coordinates.
--
-- Catching a contradiction can change inferential status without changing
-- whether a breakup, refusal, filing, vote, or order remains operative.

data InferentialStatus : Set where
  valid : InferentialStatus
  invalid : InferentialStatus
  underdetermined : InferentialStatus

data OperativeStatus : Set where
  inert : OperativeStatus
  operative : OperativeStatus

record SpeechActState : Set where
  constructor speechAct
  field
    inference : InferentialStatus
    force : OperativeStatus

open SpeechActState public

invalid-yet-operative : SpeechActState
invalid-yet-operative = speechAct invalid operative

invalid-yet-operative-inference :
  inference invalid-yet-operative ≡ invalid
invalid-yet-operative-inference = refl

invalid-yet-operative-force :
  force invalid-yet-operative ≡ operative
invalid-yet-operative-force = refl

valid-yet-inert : SpeechActState
valid-yet-inert = speechAct valid inert

valid-yet-inert-inference :
  inference valid-yet-inert ≡ valid
valid-yet-inert-inference = refl

valid-yet-inert-force :
  force valid-yet-inert ≡ inert
valid-yet-inert-force = refl

record LogicForceIndependence : Set where
  field
    validOperative : SpeechActState
    validInert : SpeechActState
    invalidOperative : SpeechActState
    invalidInert : SpeechActState

logicForceIndependence : LogicForceIndependence
logicForceIndependence =
  record
    { validOperative = speechAct valid operative
    ; validInert = speechAct valid inert
    ; invalidOperative = speechAct invalid operative
    ; invalidInert = speechAct invalid inert
    }

------------------------------------------------------------------------
-- A causal or motivational structure is weaker than a valid argument.
-- Preference, affect, authority, and articulated propositions may all cause
-- action, but only some are candidates for inferential validity.

data GroundKind : Set where
  propositionalGround : GroundKind
  preferenceGround : GroundKind
  affectiveGround : GroundKind
  authorityGround : GroundKind
  unarticulatedGround : GroundKind

data CommitmentDiscipline : Set where
  stableCommitment : CommitmentDiscipline
  revisableCommitment : CommitmentDiscipline
  evasiveRevision : CommitmentDiscipline

record DisagreementState (View : Set) : Set where
  field
    views : FourViewMatrix View
    polarity : PolarAssessment
    speechActState : SpeechActState
    groundKind : GroundKind
    commitmentDiscipline : CommitmentDiscipline

------------------------------------------------------------------------
-- Explicit non-identification boundary.

fourfoldNonIdentificationBoundary : List String
fourfoldNonIdentificationBoundary =
  "The four-view matrix is a 2x2 epistemic object, not a catuskoti"
  ∷ "A tetralemma classifies support for one proposition and its negation"
  ∷ "Objective events, first-order reports, and attributed reports must remain distinct"
  ∷ "Inferential invalidity does not entail practical ineffectiveness"
  ∷ "Causal or motivational structure does not entail propositional consistency"
  ∷ "Bad-faith premise revision may be modelled without pretending that exposure compels agreement"
  ∷ []
