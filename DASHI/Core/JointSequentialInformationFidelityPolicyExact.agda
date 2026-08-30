module DASHI.Core.JointSequentialInformationFidelityPolicyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; zero; _+_)

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.RobustInterventionAcrossHypothesesExact as Robust

------------------------------------------------------------------------
-- JOINT SEQUENTIAL INFORMATION / FIDELITY / ACTION POLICY
--
-- Evidence-producing moves refine the live hypothesis fibre.  Fidelity moves
-- change the active model state but do NOT, by themselves, remove hypotheses.
-- To make fidelity semantically consequential rather than decorative, terminal
-- action additionally requires `DecisionAdequate model intervention`: an
-- application-supplied certificate that the current model state is sufficient
-- for the declared intervention consumer.
------------------------------------------------------------------------

private
  variable
    Hypothesis Intervention Outcome ModelState : Set

data EvidenceCapableKind : Choice.InformationMoveKind → Set where
  measurementEvidence : EvidenceCapableKind Choice.takeMeasurement
  perturbationEvidence : EvidenceCapableKind Choice.perturbAndMeasure
  replicationEvidence : EvidenceCapableKind Choice.replicateMeasurement

record EvidenceMove (Hypothesis : Set) : Set₁ where
  constructor evidenceMove
  field
    informationMove : Choice.InformationMove
    evidenceCapable : EvidenceCapableKind (Choice.kind informationMove)
    Observation : Set
    supports : Hypothesis → Observation → Set
    observationReference : String
    calibrationOrRealisationReference : String

open EvidenceMove public

RefineLive :
  ∀ {Hypothesis} →
  (Hypothesis → Set) →
  (move : EvidenceMove Hypothesis) →
  Observation move →
  Hypothesis → Set
RefineLive live move observed hypothesis =
  live hypothesis × supports move hypothesis observed

EvidenceOutcomePossible :
  ∀ {Hypothesis} →
  (Hypothesis → Set) →
  (move : EvidenceMove Hypothesis) →
  Observation move → Set
EvidenceOutcomePossible live move observed =
  Σ Hypothesis λ hypothesis → RefineLive live move observed hypothesis

record FidelityMove (ModelState : Set) (current : ModelState) : Set where
  constructor fidelityMove
  field
    informationMove : Choice.InformationMove
    isFidelityMove : Choice.kind informationMove ≡ Choice.increaseFidelity
    nextModel : ModelState
    transitionReference : String
    retainedCounterexampleOrNeedReference : String

open FidelityMove public

bundleAsEvidenceMove :
  ∀ {Hypothesis} →
  Synthesis.ExperimentBundle Hypothesis →
  EvidenceMove Hypothesis
bundleAsEvidenceMove bundle =
  evidenceMove
    (Synthesis.bundleInformationMove bundle)
    measurementEvidence
    (Synthesis.Observation bundle)
    (λ hypothesis observed → Synthesis.observe bundle hypothesis ≡ observed)
    (Synthesis.bundleReference bundle)
    (Synthesis.calibrationReference bundle)

------------------------------------------------------------------------
-- Joint policy.  Evidence and fidelity update orthogonal coordinates.
------------------------------------------------------------------------

data JointSequentialPolicy
    (system : Robust.HypothesisInterventionSystem
      Hypothesis Intervention Outcome)
    (Authority : Intervention → Set)
    (ModelState : Set)
    (DecisionAdequate : ModelState → Intervention → Set) :
    (Hypothesis → Set) → ModelState → Set₁ where

  actNow :
    ∀ {live model}
      (intervention : Intervention) →
      Robust.RobustlyNoWorseThanBaseline system live intervention →
      DecisionAdequate model intervention →
      Authority intervention →
    JointSequentialPolicy
      system Authority ModelState DecisionAdequate live model

  evidenceThen :
    ∀ {live model}
      (move : EvidenceMove Hypothesis) →
      ((observed : Observation move) →
        EvidenceOutcomePossible live move observed →
        JointSequentialPolicy
          system Authority ModelState DecisionAdequate
          (RefineLive live move observed)
          model) →
    JointSequentialPolicy
      system Authority ModelState DecisionAdequate live model

  fidelityThen :
    ∀ {live model}
      (move : FidelityMove ModelState model) →
      JointSequentialPolicy
        system Authority ModelState DecisionAdequate
        live
        (nextModel move) →
    JointSequentialPolicy
      system Authority ModelState DecisionAdequate live model

------------------------------------------------------------------------
-- A fidelity transition can remove a model-adequacy obstruction without being
-- new empirical evidence.  This is the exact reason such a move can matter in
-- a joint policy.
------------------------------------------------------------------------

record FidelityUnlocksDecision
    {ModelState Intervention : Set}
    (DecisionAdequate : ModelState → Intervention → Set)
    (from : ModelState)
    (intervention : Intervention) : Set₁ where
  constructor fidelityUnlocksDecision
  field
    move : FidelityMove ModelState from
    blockedBefore : DecisionAdequate from intervention → ⊥
    adequateAfter : DecisionAdequate (nextModel move) intervention
    adequacyReference : String

open FidelityUnlocksDecision public

data JointPolicyCostAtMost
    {system : Robust.HypothesisInterventionSystem
      Hypothesis Intervention Outcome}
    {Authority : Intervention → Set}
    {ModelState : Set}
    {DecisionAdequate : ModelState → Intervention → Set}
    {live : Hypothesis → Set}
    {model : ModelState} :
    JointSequentialPolicy
      system Authority ModelState DecisionAdequate live model →
    Nat → Set₁ where

  actCost :
    ∀ {intervention robust adequate authority budget} →
    zero ≤ budget →
    JointPolicyCostAtMost
      (actNow intervention robust adequate authority)
      budget

  evidenceCost :
    ∀ {move continuations budget}
      (branchBudget : Observation move → Nat) →
      ((observed : Observation move) →
        (possible : EvidenceOutcomePossible live move observed) →
        JointPolicyCostAtMost
          (continuations observed possible)
          (branchBudget observed)) →
      ((observed : Observation move) →
        EvidenceOutcomePossible live move observed →
        Choice.cost (informationMove move) + branchBudget observed ≤ budget) →
    JointPolicyCostAtMost (evidenceThen move continuations) budget

  fidelityCost :
    ∀ {move continuation childBudget budget} →
    JointPolicyCostAtMost continuation childBudget →
    Choice.cost (informationMove move) + childBudget ≤ budget →
    JointPolicyCostAtMost (fidelityThen move continuation) budget

record CertifiedJointSequentialPolicy
    (system : Robust.HypothesisInterventionSystem
      Hypothesis Intervention Outcome)
    (Authority : Intervention → Set)
    (ModelState : Set)
    (DecisionAdequate : ModelState → Intervention → Set)
    (live : Hypothesis → Set)
    (model : ModelState) : Set₂ where
  constructor certifiedJointSequentialPolicy
  field
    policy : JointSequentialPolicy
      system Authority ModelState DecisionAdequate live model
    worstCaseCostBound : Nat
    costCertificate : JointPolicyCostAtMost policy worstCaseCostBound
    policyReference : String

open CertifiedJointSequentialPolicy public

record MinimalJointSequentialPolicy
    (system : Robust.HypothesisInterventionSystem
      Hypothesis Intervention Outcome)
    (Authority : Intervention → Set)
    (ModelState : Set)
    (DecisionAdequate : ModelState → Intervention → Set)
    (live : Hypothesis → Set)
    (model : ModelState)
    (Declared : CertifiedJointSequentialPolicy
      system Authority ModelState DecisionAdequate live model → Set) : Set₂ where
  constructor minimalJointSequentialPolicy
  field
    selected : CertifiedJointSequentialPolicy
      system Authority ModelState DecisionAdequate live model
    selectedDeclared : Declared selected
    minimalWorstCaseCost :
      (alternative : CertifiedJointSequentialPolicy
        system Authority ModelState DecisionAdequate live model) →
      Declared alternative →
      worstCaseCostBound selected ≤ worstCaseCostBound alternative
    comparisonReference : String

open MinimalJointSequentialPolicy public

robustActionSurvivesEvidenceMove :
  ∀ {system : Robust.HypothesisInterventionSystem
        Hypothesis Intervention Outcome}
    {live : Hypothesis → Set}
    {intervention : Intervention}
    (robust : Robust.RobustlyNoWorseThanBaseline system live intervention)
    (move : EvidenceMove Hypothesis)
    (observed : Observation move) →
  Robust.RobustlyNoWorseThanBaseline
    system
    (RefineLive live move observed)
    intervention
robustActionSurvivesEvidenceMove robust move observed =
  Robust.robustnessSurvivesHypothesisRefinement
    (λ hypothesis refined → proj₁ refined)
    robust

record JointSequentialPolicyBoundary : Set where
  constructor jointSequentialPolicyBoundary
  field
    fidelityMoveAloneRefinesEmpiricalHypothesisFibre : Bool
    fidelityMoveAloneRefinesEmpiricalHypothesisFibreIsFalse :
      fidelityMoveAloneRefinesEmpiricalHypothesisFibre ≡ false

    evidenceMoveMayRefineLiveHypotheses : Bool
    evidenceMoveMayRefineLiveHypothesesIsTrue :
      evidenceMoveMayRefineLiveHypotheses ≡ true

    fidelityCanRemoveModelAdequacyObstruction : Bool
    fidelityCanRemoveModelAdequacyObstructionIsTrue :
      fidelityCanRemoveModelAdequacyObstruction ≡ true

    measurementAndFidelityMayShareOneSequentialCostObjective : Bool
    measurementAndFidelityMayShareOneSequentialCostObjectiveIsTrue :
      measurementAndFidelityMayShareOneSequentialCostObjective ≡ true

    modelEscalationAutomaticallyCreatesNewWorldEvidence : Bool
    modelEscalationAutomaticallyCreatesNewWorldEvidenceIsFalse :
      modelEscalationAutomaticallyCreatesNewWorldEvidence ≡ false

    robustSupportAndModelAdequacyAutomaticallyCreateAuthority : Bool
    robustSupportAndModelAdequacyAutomaticallyCreateAuthorityIsFalse :
      robustSupportAndModelAdequacyAutomaticallyCreateAuthority ≡ false

canonicalJointSequentialPolicyBoundary : JointSequentialPolicyBoundary
canonicalJointSequentialPolicyBoundary =
  jointSequentialPolicyBoundary
    false refl true refl true refl true refl false refl false refl
