module DASHI.Philosophy.MaterialFeedbackIntervention where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- Politics at second order maps the reproduction circuit and intervenes in
-- feedback, rather than treating the visible utterance as an isolated object.

data ReproductionLayer : Set where
  visibleContent :
    ReproductionLayer

  attention :
    ReproductionLayer

  audienceMetric :
    ReproductionLayer

  funding :
    ReproductionLayer

  institutionalProtection :
    ReproductionLayer

  reproducedContent :
    ReproductionLayer

canonicalReproductionCircuit :
  List ReproductionLayer
canonicalReproductionCircuit =
  visibleContent
  ∷ attention
  ∷ audienceMetric
  ∷ funding
  ∷ institutionalProtection
  ∷ reproducedContent
  ∷ []

record FeedbackIntervention
       (State Action Response : Set) : Set₁ where
  field
    initialState :
      State

    intervention :
      Action

    observedResponse :
      Response

    nextAction :
      Action

    loopMapped :
      Set

    materialSubstrateTargeted :
      Set

    tacticalClosure :
      Set

    generativeStructureChanged :
      Set

open FeedbackIntervention public

record InterventionBoundary : Set where
  constructor mkInterventionBoundary
  field
    targetingSubstrateCanBeMateriallyEffective :
      Bool

    removingOneOutputProvesSystemicClosure :
      Bool

    incentiveGovernanceOwnershipStillMatter :
      Bool

open InterventionBoundary public

canonicalInterventionBoundary :
  InterventionBoundary
canonicalInterventionBoundary =
  mkInterventionBoundary
    true
    false
    true

canonicalOutputRemovalIsNotSystemicClosure :
  removingOneOutputProvesSystemicClosure canonicalInterventionBoundary
  ≡
  false
canonicalOutputRemovalIsNotSystemicClosure =
  refl
