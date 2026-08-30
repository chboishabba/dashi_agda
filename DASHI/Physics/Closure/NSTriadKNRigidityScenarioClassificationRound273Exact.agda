module DASHI.Physics.Closure.NSTriadKNRigidityScenarioClassificationRound273Exact where

------------------------------------------------------------------------
-- ROUND273 / RIGIDITY SCENARIO CLASSIFICATION AFTER ROUND272
--
-- Once the SAME mixed-defect critical solution owns a maximal lifespan and a
-- frequency scale, the rigidity analysis may split according to its actual
-- dynamics.  The classification is intentionally weaker than the dispersive
-- folklore trichotomy: only cases justified by the parabolic critical element
-- are admitted.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record RigidityScenarioClassification {ℓ : Level}
    (CriticalDynamics : Set ℓ) : Set (lsuc ℓ) where
  field
    dynamics : CriticalDynamics

    FiniteTerminalConcentration : Set ℓ
    GlobalBoundedFrequency : Set ℓ
    GlobalUnboundedFrequency : Set ℓ

    scenariosExhaustMaximalLifespanDynamics : Set ℓ
    finiteTerminalImpliesScaleConcentration : Set ℓ
    globalBoundedFrequencyHasPositiveLowerAndFiniteUpperScale : Set ℓ
    globalUnboundedFrequencyHasEscapingScaleSequence : Set ℓ

open RigidityScenarioClassification public

round273ClassificationRequiresRound272Dynamics : Bool
round273ClassificationRequiresRound272Dynamics = true

round273DispersiveSolitonCascadeLabelsNotAssumedWithoutParabolicProof : Bool
round273DispersiveSolitonCascadeLabelsNotAssumedWithoutParabolicProof = true

round273ScenarioClassificationClosed : Bool
round273ScenarioClassificationClosed = false

round273PackageAClosed : Bool
round273PackageAClosed = false

round273ScenarioClassificationClosedIsFalse : round273ScenarioClassificationClosed ≡ false
round273ScenarioClassificationClosedIsFalse = refl
