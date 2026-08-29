module DASHI.Core.JointSequentialInformationFidelityFixtureExact where

open import DASHI.Core.Prelude

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.JointSequentialInformationFidelityPolicyExact as Joint
import DASHI.Core.RobustInterventionAcrossHypothesesExact as Robust

------------------------------------------------------------------------
-- FINITE EXECUTABLE FIXTURE
--
-- One measurement has two realizable outcomes.  Under outcome A, the coarse
-- model is already adequate for the robust authorised action.  Under outcome B,
-- the observation identifies a different robust action but the coarse model is
-- inadequate, so the policy escalates fidelity and then acts.
--
-- This is synthetic theorem data, not an empirical experiment.
------------------------------------------------------------------------

data Hypothesis : Set where
  hA hB : Hypothesis

data Intervention : Set where
  baseline actionA actionB : Intervention

data Utility : Set where
  bad neutral good : Utility

data NoWorse : Utility → Utility → Set where
  neutralNoWorseNeutral : NoWorse neutral neutral
  goodNoWorseNeutral : NoWorse good neutral

predict : Hypothesis → Intervention → Utility
predict hA baseline = neutral
predict hA actionA = good
predict hA actionB = bad
predict hB baseline = neutral
predict hB actionA = bad
predict hB actionB = good

system : Robust.HypothesisInterventionSystem Hypothesis Intervention Utility
system = Robust.hypothesisInterventionSystem
  baseline predict NoWorse NoWorse

Authority : Intervention → Set
Authority _ = ⊤

data ModelState : Set where
  coarse rich : ModelState

DecisionAdequate : ModelState → Intervention → Set
DecisionAdequate coarse baseline = ⊤
DecisionAdequate coarse actionA = ⊤
DecisionAdequate coarse actionB = ⊥
DecisionAdequate rich baseline = ⊤
DecisionAdequate rich actionA = ⊤
DecisionAdequate rich actionB = ⊤

data Measurement : Set where
  observedA observedB : Measurement

measure : Hypothesis → Measurement
measure hA = observedA
measure hB = observedB

measurementBundle : Synthesis.ExperimentBundle Hypothesis
measurementBundle =
  Synthesis.experimentBundle
    Measurement
    measure
    1
    "synthetic A/B discriminator"
    "synthetic exact lookup"

measurementMove : Joint.EvidenceMove Hypothesis
measurementMove = Joint.bundleAsEvidenceMove measurementBundle

live : Hypothesis → Set
live _ = ⊤

robustA :
  Robust.RobustlyNoWorseThanBaseline
    system
    (Joint.RefineLive live measurementMove observedA)
    actionA
robustA = Robust.robustlyNoWorseThanBaseline λ where
  hA (tt , refl) → goodNoWorseNeutral
  hB (tt , ())

robustB :
  Robust.RobustlyNoWorseThanBaseline
    system
    (Joint.RefineLive live measurementMove observedB)
    actionB
robustB = Robust.robustlyNoWorseThanBaseline λ where
  hA (tt , ())
  hB (tt , refl) → goodNoWorseNeutral

coarseToRich : Joint.FidelityMove ModelState coarse
coarseToRich = Joint.fidelityMove
  (Choice.informationMove
    Choice.increaseFidelity
    2
    "synthetic coarse -> rich model escalation"
    "synthetic fidelity cost"
    "actionB requires rich model adequacy")
  refl
  rich
  "synthetic fidelity transition"
  "coarse actionB adequacy obstruction"

fidelityUnlocksActionB :
  Joint.FidelityUnlocksDecision DecisionAdequate coarse actionB
fidelityUnlocksActionB = Joint.fidelityUnlocksDecision
  coarseToRich
  (λ ())
  tt
  "rich model certifies actionB consumer"

------------------------------------------------------------------------
-- Outcome-adaptive joint policy:
--
--   measure
--     observedA -> actA at coarse fidelity
--     observedB -> increase fidelity -> actB
------------------------------------------------------------------------

jointPolicy :
  Joint.JointSequentialPolicy
    system Authority ModelState DecisionAdequate live coarse
jointPolicy =
  Joint.evidenceThen measurementMove λ where
    observedA possible →
      Joint.actNow actionA robustA tt tt
    observedB possible →
      Joint.fidelityThen coarseToRich
        (Joint.actNow actionB robustB tt tt)

record JointSequentialFixtureBoundary : Set where
  constructor jointSequentialFixtureBoundary
  field
    oneFixedFidelityUsedOnEveryOutcomeBranch : Bool
    oneFixedFidelityUsedOnEveryOutcomeBranchIsFalse :
      oneFixedFidelityUsedOnEveryOutcomeBranch ≡ false

    measurementOutcomeCanDetermineWhetherEscalationIsNeeded : Bool
    measurementOutcomeCanDetermineWhetherEscalationIsNeededIsTrue :
      measurementOutcomeCanDetermineWhetherEscalationIsNeeded ≡ true

    fidelityEscalationCanUnlockModelAdequacyWithoutChangingEvidence : Bool
    fidelityEscalationCanUnlockModelAdequacyWithoutChangingEvidenceIsTrue :
      fidelityEscalationCanUnlockModelAdequacyWithoutChangingEvidence ≡ true

    fixtureIsEmpiricalValidation : Bool
    fixtureIsEmpiricalValidationIsFalse :
      fixtureIsEmpiricalValidation ≡ false

canonicalJointSequentialFixtureBoundary : JointSequentialFixtureBoundary
canonicalJointSequentialFixtureBoundary =
  jointSequentialFixtureBoundary false refl true refl true refl false refl
