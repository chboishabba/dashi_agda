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
-- This owner fuses the previously separate sequential information tree and
-- adaptive model-fidelity search without collapsing their semantics.
--
-- Evidence-producing moves refine the live hypothesis fibre by a declared
-- observation relation.  Fidelity moves change the active model state but do
-- NOT, by themselves, remove hypotheses.  A terminal action still requires an
-- independent robustness proof and an independent authority witness.
------------------------------------------------------------------------

private
  variable
    Hypothesis Intervention Outcome ModelState : Set

------------------------------------------------------------------------
-- Only move kinds that can actually return evidence inhabit this witness.
------------------------------------------------------------------------

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
  EvidenceMove Hypothesis →
  Observation →
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

------------------------------------------------------------------------
-- Fidelity transitions change the model/representation coordinate only.
------------------------------------------------------------------------

record FidelityMove (ModelState : Set) (current : ModelState) : Set where
  constructor fidelityMove
  field
    informationMove : Choice.InformationMove
    isFidelityMove : Choice.kind informationMove ≡ Choice.increaseFidelity
    nextModel : ModelState
    transitionReference : String
    retainedCounterexampleOrNeedReference : String

open FidelityMove public

------------------------------------------------------------------------
-- Deterministic experiment bundles embed as evidence moves.  This preserves
-- the existing measurement semantics while the relational carrier above also
-- supports set-valued theory predictions.
------------------------------------------------------------------------

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
-- Joint policy.  The two recursive constructors intentionally update different
-- coordinates:
--
--   evidenceThen  : live fibre changes, model state stays fixed
--   fidelityThen  : model state changes, live fibre stays fixed
------------------------------------------------------------------------

data JointSequentialPolicy
    (system : Robust.HypothesisInterventionSystem
      Hypothesis Intervention Outcome)
    (Authority : Intervention → Set)
    (ModelState : Set) :
    (Hypothesis → Set) → ModelState → Set₁ where

  actNow :
    ∀ {live model}
      (intervention : Intervention) →
      Robust.RobustlyNoWorseThanBaseline system live intervention →
      Authority intervention →
    JointSequentialPolicy system Authority ModelState live model

  evidenceThen :
    ∀ {live model}
      (move : EvidenceMove Hypothesis) →
      ((observed : Observation move) →
        EvidenceOutcomePossible live move observed →
        JointSequentialPolicy
          system Authority ModelState
          (RefineLive live move observed)
          model) →
    JointSequentialPolicy system Authority ModelState live model

  fidelityThen :
    ∀ {live model}
      (move : FidelityMove ModelState model) →
      JointSequentialPolicy
        system Authority ModelState
        live
        (nextModel move) →
    JointSequentialPolicy system Authority ModelState live model

------------------------------------------------------------------------
-- Worst-case cumulative resource bound.  Evidence branches are bounded over
-- every realizable outcome; deterministic fidelity transitions have one child.
------------------------------------------------------------------------

data JointPolicyCostAtMost
    {system : Robust.HypothesisInterventionSystem
      Hypothesis Intervention Outcome}
    {Authority : Intervention → Set}
    {ModelState : Set}
    {live : Hypothesis → Set}
    {model : ModelState} :
    JointSequentialPolicy system Authority ModelState live model →
    Nat → Set₁ where

  actCost :
    ∀ {intervention robust authority budget} →
    zero ≤ budget →
    JointPolicyCostAtMost (actNow intervention robust authority) budget

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
    (live : Hypothesis → Set)
    (model : ModelState) : Set₂ where
  constructor certifiedJointSequentialPolicy
  field
    policy : JointSequentialPolicy system Authority ModelState live model
    worstCaseCostBound : Nat
    costCertificate : JointPolicyCostAtMost policy worstCaseCostBound
    policyReference : String

open CertifiedJointSequentialPolicy public

record MinimalJointSequentialPolicy
    (system : Robust.HypothesisInterventionSystem
      Hypothesis Intervention Outcome)
    (Authority : Intervention → Set)
    (ModelState : Set)
    (live : Hypothesis → Set)
    (model : ModelState)
    (Declared : CertifiedJointSequentialPolicy
      system Authority ModelState live model → Set) : Set₂ where
  constructor minimalJointSequentialPolicy
  field
    selected : CertifiedJointSequentialPolicy
      system Authority ModelState live model
    selectedDeclared : Declared selected
    minimalWorstCaseCost :
      (alternative : CertifiedJointSequentialPolicy
        system Authority ModelState live model) →
      Declared alternative →
      worstCaseCostBound selected ≤ worstCaseCostBound alternative
    comparisonReference : String

open MinimalJointSequentialPolicy public

------------------------------------------------------------------------
-- Structural consequences.
------------------------------------------------------------------------

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

    measurementAndFidelityMayShareOneSequentialCostObjective : Bool
    measurementAndFidelityMayShareOneSequentialCostObjectiveIsTrue :
      measurementAndFidelityMayShareOneSequentialCostObjective ≡ true

    modelEscalationAutomaticallyCreatesNewWorldEvidence : Bool
    modelEscalationAutomaticallyCreatesNewWorldEvidenceIsFalse :
      modelEscalationAutomaticallyCreatesNewWorldEvidence ≡ false

    robustSupportAutomaticallyCreatesAuthority : Bool
    robustSupportAutomaticallyCreatesAuthorityIsFalse :
      robustSupportAutomaticallyCreatesAuthority ≡ false

canonicalJointSequentialPolicyBoundary : JointSequentialPolicyBoundary
canonicalJointSequentialPolicyBoundary =
  jointSequentialPolicyBoundary
    false refl true refl true refl false refl false refl
