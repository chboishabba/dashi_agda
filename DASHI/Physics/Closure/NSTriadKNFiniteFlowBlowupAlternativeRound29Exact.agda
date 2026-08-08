module DASHI.Physics.Closure.NSTriadKNFiniteFlowBlowupAlternativeRound29Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Separate the finite-flow argument into three independent claims:
-- local flow, continuation unless the finite norm escapes, and energy control
-- of that norm. The global conclusion no longer depends on the internals of a
-- particular Picard--Lindelof library theorem.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_)
open import Data.Rational.Base using (ℚ; _≤_)
import Data.Rational.Properties as ℚₚ

record FiniteNormTrajectory
    {timeLevel stateLevel : Level}
    (Time : Set timeLevel)
    (State : Set stateLevel) : Set (lsuc (timeLevel ⊔ stateLevel)) where
  field
    stateAt : Time → State
    normSquared : State → ℚ

open FiniteNormTrajectory public

record UniformNormBound
    {timeLevel stateLevel}
    {Time : Set timeLevel}
    {State : Set stateLevel}
    (trajectory : FiniteNormTrajectory Time State) : Set (timeLevel ⊔ stateLevel) where
  constructor uniform-norm-bound
  field
    bound : ℚ
    boundedAtEveryTime : ∀ time →
      normSquared trajectory (stateAt trajectory time) ≤ bound

open UniformNormBound public

record EscapeWitness
    {timeLevel stateLevel}
    {Time : Set timeLevel}
    {State : Set stateLevel}
    (trajectory : FiniteNormTrajectory Time State) : Set (timeLevel ⊔ stateLevel) where
  constructor escape-witness
  field
    escapesEveryBound :
      (candidate : ℚ) →
      Σ (Time) (λ time →
        ¬ normSquared trajectory (stateAt trajectory time) ≤ candidate)

open EscapeWitness public

uniformBoundContradictsEscape :
  ∀ {timeLevel stateLevel}
    {Time : Set timeLevel}
    {State : Set stateLevel}
    {trajectory : FiniteNormTrajectory Time State} →
  UniformNormBound trajectory → EscapeWitness trajectory → ⊥
uniformBoundContradictsEscape bounded escaping with
  escapesEveryBound escaping (bound bounded)
... | time , notBounded =
  notBounded (boundedAtEveryTime bounded time)

record FiniteBlowupAlternative
    {timeLevel stateLevel}
    {Time : Set timeLevel}
    {State : Set stateLevel}
    (trajectory : FiniteNormTrajectory Time State) :
    Set (lsuc (timeLevel ⊔ stateLevel)) where
  field
    FiniteMaximalTime : Set
    finiteMaximalImpliesEscape :
      FiniteMaximalTime → EscapeWitness trajectory

open FiniteBlowupAlternative public

uniformBoundExcludesFiniteMaximalTime :
  ∀ {timeLevel stateLevel}
    {Time : Set timeLevel}
    {State : Set stateLevel}
    {trajectory : FiniteNormTrajectory Time State}
    (alternative : FiniteBlowupAlternative trajectory) →
  UniformNormBound trajectory →
  FiniteMaximalTime alternative → ⊥
uniformBoundExcludesFiniteMaximalTime alternative bounded finite =
  uniformBoundContradictsEscape bounded
    (finiteMaximalImpliesEscape alternative finite)

record EnergyControl
    {timeLevel stateLevel}
    {Time : Set timeLevel}
    {State : Set stateLevel}
    (trajectory : FiniteNormTrajectory Time State) :
    Set (lsuc (timeLevel ⊔ stateLevel)) where
  field
    energy : State → ℚ
    initialEnergyBound : ℚ
    normControlledByEnergy : ∀ state →
      normSquared trajectory state ≤ energy state
    energyBoundAtEveryTime : ∀ time →
      energy (stateAt trajectory time) ≤ initialEnergyBound

open EnergyControl public

energyConstructsUniformNormBound :
  ∀ {timeLevel stateLevel}
    {Time : Set timeLevel}
    {State : Set stateLevel}
    {trajectory : FiniteNormTrajectory Time State} →
  EnergyControl trajectory → UniformNormBound trajectory
energyConstructsUniformNormBound control =
  uniform-norm-bound
    (initialEnergyBound control)
    (λ time →
      ℚₚ.≤-trans
        (normControlledByEnergy control (stateAt _ time))
        (energyBoundAtEveryTime control time))

energyExcludesFiniteMaximalTime :
  ∀ {timeLevel stateLevel}
    {Time : Set timeLevel}
    {State : Set stateLevel}
    {trajectory : FiniteNormTrajectory Time State}
    (alternative : FiniteBlowupAlternative trajectory) →
  EnergyControl trajectory →
  FiniteMaximalTime alternative → ⊥
energyExcludesFiniteMaximalTime alternative control =
  uniformBoundExcludesFiniteMaximalTime alternative
    (energyConstructsUniformNormBound control)

finiteBlowupAlternativeReducerClosed : Bool
finiteBlowupAlternativeReducerClosed = true

literalFinitePicardLindelofInstantiated : Bool
literalFinitePicardLindelofInstantiated = false

literalPhysicalEnergyIdentityInstantiated : Bool
literalPhysicalEnergyIdentityInstantiated = false

finiteBlowupAlternativeReducerClosedIsTrue :
  finiteBlowupAlternativeReducerClosed ≡ true
finiteBlowupAlternativeReducerClosedIsTrue = refl
