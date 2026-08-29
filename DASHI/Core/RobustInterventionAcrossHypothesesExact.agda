module DASHI.Core.RobustInterventionAcrossHypothesesExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- PURPOSE
--
-- Repo-wide intervention gate inspired by the option-cone / no-action baseline
-- pattern already used in trading and governance, but abstracted away from any
-- economic or environmental semantics.
--
-- A model may be observationally unresolved.  An intervention can nevertheless
-- be safe for a declared decision consumer when it is no worse than the
-- baseline under every still-live hypothesis.  Conversely, information can be
-- valuable because it removes hypotheses that block such a robust action.
--
-- This is a DASHI construction; robustness is not authority or permission.
------------------------------------------------------------------------

record HypothesisInterventionSystem
    (Hypothesis Intervention Outcome : Set) : Set₁ where
  constructor hypothesisInterventionSystem
  field
    baseline : Intervention
    predict : Hypothesis → Intervention → Outcome
    NoWorse : Outcome → Outcome → Set
    StrictlyBetter : Outcome → Outcome → Set

open HypothesisInterventionSystem public

record RobustlyNoWorseThanBaseline
    {Hypothesis Intervention Outcome : Set}
    (system : HypothesisInterventionSystem Hypothesis Intervention Outcome)
    (Declared : Hypothesis → Set)
    (intervention : Intervention) : Set₁ where
  constructor robustlyNoWorseThanBaseline
  field
    noWorse :
      (hypothesis : Hypothesis) →
      Declared hypothesis →
      NoWorse system
        (predict system hypothesis intervention)
        (predict system hypothesis (baseline system))

open RobustlyNoWorseThanBaseline public

record RobustlyDominatesBaseline
    {Hypothesis Intervention Outcome : Set}
    (system : HypothesisInterventionSystem Hypothesis Intervention Outcome)
    (Declared : Hypothesis → Set)
    (intervention : Intervention) : Set₁ where
  constructor robustlyDominatesBaseline
  field
    robustNoWorse : RobustlyNoWorseThanBaseline system Declared intervention
    witnessHypothesis : Hypothesis
    witnessDeclared : Declared witnessHypothesis
    strictlyBetterSomewhere :
      StrictlyBetter system
        (predict system witnessHypothesis intervention)
        (predict system witnessHypothesis (baseline system))

open RobustlyDominatesBaseline public

------------------------------------------------------------------------
-- Refining the live hypothesis set cannot destroy a universal robustness proof.
------------------------------------------------------------------------

DeclaredRefines :
  ∀ {Hypothesis : Set} →
  (Hypothesis → Set) →
  (Hypothesis → Set) → Set
DeclaredRefines stronger weaker =
  ∀ hypothesis → stronger hypothesis → weaker hypothesis

robustnessSurvivesHypothesisRefinement :
  ∀ {Hypothesis Intervention Outcome}
    {system : HypothesisInterventionSystem Hypothesis Intervention Outcome}
    {stronger weaker : Hypothesis → Set}
    {intervention : Intervention} →
  DeclaredRefines stronger weaker →
  RobustlyNoWorseThanBaseline system weaker intervention →
  RobustlyNoWorseThanBaseline system stronger intervention
robustnessSurvivesHypothesisRefinement refines robust =
  robustlyNoWorseThanBaseline λ hypothesis declaredStrong →
    noWorse robust hypothesis (refines hypothesis declaredStrong)

------------------------------------------------------------------------
-- Decision conflict witness: unresolved hypotheses can demand incompatible
-- interventions.  This is non-probabilistic and does not rank the hypotheses.
------------------------------------------------------------------------

record HypothesisActionConflict
    {Hypothesis Intervention Outcome : Set}
    (system : HypothesisInterventionSystem Hypothesis Intervention Outcome)
    (Declared : Hypothesis → Set) : Set where
  constructor hypothesisActionConflict
  field
    left right : Hypothesis
    leftDeclared : Declared left
    rightDeclared : Declared right
    leftRequired rightRequired : Intervention
    differentRequirements : leftRequired ≡ rightRequired → ⊥

open HypothesisActionConflict public

------------------------------------------------------------------------
-- Information-unlocks-action witness.  The before/after hypothesis fibres are
-- explicit; after must refine before.  The action is certified only after the
-- refinement.  No implication that every measurement increases actionability.
------------------------------------------------------------------------

record InformationUnlocksIntervention
    {Hypothesis Intervention Outcome : Set}
    (system : HypothesisInterventionSystem Hypothesis Intervention Outcome)
    (intervention : Intervention) : Set₁ where
  constructor informationUnlocksIntervention
  field
    Before After : Hypothesis → Set
    afterRefinesBefore : DeclaredRefines After Before
    beforeConflict : HypothesisActionConflict system Before
    afterRobust : RobustlyNoWorseThanBaseline system After intervention
    informationReference : String
    interventionConsumerReference : String

open InformationUnlocksIntervention public

record RobustInterventionBoundary : Set where
  constructor robustInterventionBoundary
  field
    unresolvedModelsAlwaysForbidAction : Bool
    unresolvedModelsAlwaysForbidActionIsFalse : unresolvedModelsAlwaysForbidAction ≡ false
    robustAgainstAllLiveHypothesesCanSupportDecisionUse : Bool
    robustAgainstAllLiveHypothesesCanSupportDecisionUseIsTrue :
      robustAgainstAllLiveHypothesesCanSupportDecisionUse ≡ true
    hypothesisRefinementCanPreserveExistingRobustness : Bool
    hypothesisRefinementCanPreserveExistingRobustnessIsTrue :
      hypothesisRefinementCanPreserveExistingRobustness ≡ true
    measurementAlwaysUnlocksAnIntervention : Bool
    measurementAlwaysUnlocksAnInterventionIsFalse :
      measurementAlwaysUnlocksAnIntervention ≡ false
    robustDominanceEqualsAuthorityOrPermission : Bool
    robustDominanceEqualsAuthorityOrPermissionIsFalse :
      robustDominanceEqualsAuthorityOrPermission ≡ false

canonicalRobustInterventionBoundary : RobustInterventionBoundary
canonicalRobustInterventionBoundary =
  robustInterventionBoundary false refl true refl true refl false refl false refl
