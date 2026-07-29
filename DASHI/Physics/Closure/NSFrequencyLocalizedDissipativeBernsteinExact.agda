module DASHI.Physics.Closure.NSFrequencyLocalizedDissipativeBernsteinExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSPeriodicInfinityShellBernstein as FiniteShell
import DASHI.Physics.Closure.NSPeriodicInfinityShellDerivativeBound as FiniteDerivative

------------------------------------------------------------------------
-- Harmonic-analysis provenance.
--
-- Dong Li,
-- "On a Frequency Localized Bernstein Inequality and Some Generalized
-- Poincare-Type Inequalities", arXiv:1212.0183v1 (2012).
-- No DOI is recorded in the uploaded paper.
--
-- Main source targets:
--   Theorem 1.1, equations (1.4)--(1.5): frequency-localized heat-flow decay;
--   Corollary 1.6, equations (1.10)--(1.11): dissipative Bernstein coercivity;
--   Theorem 1.10 and Corollary 1.13: periodic mean-zero heat-flow and
--   generalized Poincare inequalities.
--
-- Relationship to DASHI: this is an adjacent Navier--Stokes/fractional-
-- dissipation authority.  It is not the same theorem as the existing finite
-- cube-shell L-infinity-from-L2 Bernstein count and is not imported into the
-- Yang--Mills Gate-4 proof.
------------------------------------------------------------------------

data BernsteinMechanism : Set where
  finiteFourierCounting : BernsteinMechanism
  dissipativeSemigroupCoercivity : BernsteinMechanism

finiteAndDissipativeBernsteinAreDistinct :
  finiteFourierCounting ≡ dissipativeSemigroupCoercivity → Set
finiteAndDissipativeBernsteinAreDistinct ()

------------------------------------------------------------------------
-- Exact assembly from the right derivative of heat-flow decay.
------------------------------------------------------------------------

record FrequencyLocalizedHeatFlowDerivativeBridge
    (Scale State Bound : Set) : Set₁ where
  field
    FrequencyLocalized : Scale → State → Set
    LessEqual : Bound → Bound → Set

    scaledNormPower : Scale → State → Bound
    negativeHeatNormRightDerivative : Scale → State → Bound
    dissipativeForm : Scale → State → Bound

    heatFlowDecayDerivativeLowerBound :
      ∀ (scale : Scale) (state : State) →
      FrequencyLocalized scale state →
      LessEqual
        (scaledNormPower scale state)
        (negativeHeatNormRightDerivative scale state)

    derivativeIdentifiesDissipation :
      ∀ (scale : Scale) (state : State) →
      FrequencyLocalized scale state →
      negativeHeatNormRightDerivative scale state
      ≡ dissipativeForm scale state

open FrequencyLocalizedHeatFlowDerivativeBridge public

frequencyLocalizedDissipativeBernstein :
  ∀ {Scale State Bound}
    (dataSet : FrequencyLocalizedHeatFlowDerivativeBridge Scale State Bound)
    (scale : Scale) (state : State) →
  FrequencyLocalized dataSet scale state →
  LessEqual dataSet
    (scaledNormPower dataSet scale state)
    (dissipativeForm dataSet scale state)
frequencyLocalizedDissipativeBernstein dataSet scale state supported =
  subst
    (λ upper → LessEqual dataSet
      (scaledNormPower dataSet scale state) upper)
    (derivativeIdentifiesDissipation dataSet scale state supported)
    (heatFlowDecayDerivativeLowerBound dataSet scale state supported)

------------------------------------------------------------------------
-- Periodic mean-zero version.
------------------------------------------------------------------------

record PeriodicMeanZeroHeatFlowBridge
    (State Bound : Set) : Set₁ where
  field
    MeanZero : State → Set
    LessEqual : Bound → Bound → Set

    normPower negativeHeatNormRightDerivative periodicDissipativeForm :
      State → Bound

    periodicHeatFlowDerivativeLowerBound :
      ∀ (state : State) → MeanZero state →
      LessEqual
        (normPower state)
        (negativeHeatNormRightDerivative state)

    periodicDerivativeIdentifiesDissipation :
      ∀ (state : State) → MeanZero state →
      negativeHeatNormRightDerivative state
      ≡ periodicDissipativeForm state

open PeriodicMeanZeroHeatFlowBridge public

periodicGeneralizedPoincare :
  ∀ {State Bound}
    (dataSet : PeriodicMeanZeroHeatFlowBridge State Bound)
    (state : State) →
  MeanZero dataSet state →
  LessEqual dataSet
    (normPower dataSet state)
    (periodicDissipativeForm dataSet state)
periodicGeneralizedPoincare dataSet state meanZero =
  subst
    (λ upper → LessEqual dataSet (normPower dataSet state) upper)
    (periodicDerivativeIdentifiesDissipation dataSet state meanZero)
    (periodicHeatFlowDerivativeLowerBound dataSet state meanZero)

------------------------------------------------------------------------
-- Existing finite Bernstein reuse remains a separate exact lane.
------------------------------------------------------------------------

existingInfinityShellBernsteinReductionLevel : ProofLevel
existingInfinityShellBernsteinReductionLevel =
  FiniteShell.infinityShellBernsteinReductionLevel

existingInfinityShellDerivativeReductionLevel : ProofLevel
existingInfinityShellDerivativeReductionLevel =
  FiniteDerivative.infinityShellDerivativeReductionLevel

dongLiProvenanceMetadataLevel : ProofLevel
dongLiProvenanceMetadataLevel = machineChecked

bernsteinMechanismSeparationLevel : ProofLevel
bernsteinMechanismSeparationLevel = machineChecked

heatFlowToDissipationAssemblyLevel : ProofLevel
heatFlowToDissipationAssemblyLevel = machineChecked

frequencyLocalizedHeatFlowAnalyticInputsLevel : ProofLevel
frequencyLocalizedHeatFlowAnalyticInputsLevel = conditional

periodicMeanZeroHeatFlowAnalyticInputsLevel : ProofLevel
periodicMeanZeroHeatFlowAnalyticInputsLevel = conditional
