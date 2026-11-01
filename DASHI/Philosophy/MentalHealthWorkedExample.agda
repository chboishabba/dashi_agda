module DASHI.Philosophy.MentalHealthWorkedExample where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Philosophy.ReflexivePowerUp as Reflexive

------------------------------------------------------------------------
-- Evidence-bearing worked example.  Distress is retained as meaningful data
-- while bodily, developmental, relational, material, symbolic, and
-- existential explanations remain live and non-exclusive.

data DistressDimension : Set where
  bodily : DistressDimension
  developmental : DistressDimension
  relational : DistressDimension
  material : DistressDimension
  symbolic : DistressDimension
  existential : DistressDimension

canonicalDistressDimensions : List DistressDimension
canonicalDistressDimensions =
  bodily ∷ developmental ∷ relational ∷ material ∷ symbolic ∷ existential ∷ []

data CandidateSupport : Set where
  bodilyCare : CandidateSupport
  environmentalAdjustment : CandidateSupport
  relationalSupport : CandidateSupport
  materialSupport : CandidateSupport
  interpretiveSupport : CandidateSupport
  clinicalAssessment : CandidateSupport
  collectiveAction : CandidateSupport

record EvidenceLane : Set where
  constructor mkEvidenceLane
  field
    sourceAndProvenance : String
    populationAndContext : String
    competingExplanations : List DistressDimension
    limitsOfGeneralisation : String
    affectedAuthority : String
    nonClaimBoundary : String
    disconfirmationCriterion : String

open EvidenceLane public

record MentalHealthCase : Set where
  constructor mkMentalHealthCase
  field
    experience : String
    implicitFrame : String
    representedFrame : String
    observerPosition : String
    dimensionsConsidered : List DistressDimension
    evidence : EvidenceLane
    candidateSupport : CandidateSupport
    signalTreatedAsMeaningful : Bool
    uniqueCauseInferred : Bool
    automaticDiagnosisInferred : Bool
    automaticSystemicTruthInferred : Bool
    supportRequiresConsentAndReview : Bool

open MentalHealthCase public

canonicalMentalHealthCase : MentalHealthCase
canonicalMentalHealthCase =
  mkMentalHealthCase
    "distress, overload, loss of function, or anguish reported by a situated person"
    "the person alone is defective or failing"
    "experience is interpreted across body, development, relation, material conditions, symbols, and existential meaning"
    "the person participates in interpretation without becoming an infallible outside observer"
    canonicalDistressDimensions
    (mkEvidenceLane
      "candidate evidence must name source, date, method, and provenance"
      "population, environment, history, and task must be declared"
      canonicalDistressDimensions
      "no single case or source generalises universally"
      "clinical, political, and lived-experience authority remain distinct"
      "this formalism neither diagnoses nor proves a social cause"
      "revise the interpretation when contrary bodily, contextual, longitudinal, or intervention evidence appears")
    relationalSupport
    true
    false
    false
    false
    true

canonicalNoAutomaticDiagnosis :
  automaticDiagnosisInferred canonicalMentalHealthCase ≡ false
canonicalNoAutomaticDiagnosis = refl

canonicalNoAutomaticSystemicTruth :
  automaticSystemicTruthInferred canonicalMentalHealthCase ≡ false
canonicalNoAutomaticSystemicTruth = refl

mentalHealthReflexiveKnowledge :
  Reflexive.ReflexiveKnowledge String String String CandidateSupport
mentalHealthReflexiveKnowledge =
  Reflexive.powerUp
    (experience canonicalMentalHealthCase)
    (λ _ → implicitFrame canonicalMentalHealthCase)
    (observerPosition canonicalMentalHealthCase)
    "multi-causal residual remains open"
    (candidateSupport canonicalMentalHealthCase)
    String
