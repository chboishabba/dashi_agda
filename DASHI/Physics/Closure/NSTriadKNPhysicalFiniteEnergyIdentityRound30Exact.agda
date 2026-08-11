module DASHI.Physics.Closure.NSTriadKNPhysicalFiniteEnergyIdentityRound30Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Separate the literal finite energy calculation into its two mathematical
-- inputs: exhaustive triad skew cancellation and diagonal viscous
-- dissipation.  From
--
--   nonlinearPower = 0,
--   viscousPower = - nu * gradientEnergy,
--   dE/dt = nonlinearPower + viscousPower,
--
-- the exact physical identity
--
--   dE/dt + nu * gradientEnergy = 0
--
-- follows by ring normalization.  A time-integration authority then produces
-- the exact energy-plus-accumulated-dissipation identity already consumed by
-- the Round-27/29 continuation lane.  The finite triad cancellation and real
-- fundamental-theorem instances remain explicit same-object producers.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; trans)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteEnergyContinuationRound27Exact as Continuation

record PhysicalFiniteEnergyDerivative
    {timeLevel stateLevel : Level}
    (Time : Set timeLevel)
    (State : Set stateLevel) :
    Set (lsuc (timeLevel ⊔ stateLevel)) where
  field
    stateAt : Time → State
    viscosity : ℚ
    viscosityNonnegative : 0ℚ ≤ viscosity

    energyDerivative nonlinearPower viscousPower : Time → ℚ
    gradientEnergy : State → ℚ
    gradientEnergyNonnegative : ∀ state → 0ℚ ≤ gradientEnergy state

    nonlinearIsLiteralTriadFold : Time → Set
    nonlinearTriadCancellation : ∀ time →
      nonlinearPower time ≡ 0ℚ

    viscousDiagonalExact : ∀ time →
      viscousPower time
      ≡ - (viscosity * gradientEnergy (stateAt time))

    derivativeSplits : ∀ time →
      energyDerivative time
      ≡ nonlinearPower time + viscousPower time

open PhysicalFiniteEnergyDerivative public

physicalFiniteDifferentialEnergyIdentity :
  ∀ {timeLevel stateLevel}
    {Time : Set timeLevel}
    {State : Set stateLevel}
    (dataSet : PhysicalFiniteEnergyDerivative Time State)
    time →
  energyDerivative dataSet time
    + viscosity dataSet * gradientEnergy dataSet (stateAt dataSet time)
  ≡ 0ℚ
physicalFiniteDifferentialEnergyIdentity dataSet time =
  trans
    (cong
      (λ selected → selected
        + viscosity dataSet
          * gradientEnergy dataSet (stateAt dataSet time))
      (derivativeSplits dataSet time))
    (trans
      (cong
        (λ selected →
          selected + viscousPower dataSet time
          + viscosity dataSet
            * gradientEnergy dataSet (stateAt dataSet time))
        (nonlinearTriadCancellation dataSet time))
      (trans
        (cong
          (λ selected →
            0ℚ + selected
            + viscosity dataSet
              * gradientEnergy dataSet (stateAt dataSet time))
          (viscousDiagonalExact dataSet time))
        (ℚRing.solve-∀
          (viscosity dataSet)
          (gradientEnergy dataSet (stateAt dataSet time)))))

record IntegratedPhysicalFiniteEnergy
    {timeLevel stateLevel}
    {Time : Set timeLevel}
    {State : Set stateLevel}
    (derivativeData : PhysicalFiniteEnergyDerivative Time State) :
    Set (lsuc (timeLevel ⊔ stateLevel)) where
  field
    initialTime : Time
    energy : State → ℚ
    accumulatedDissipation : Time → ℚ

    initialDissipationZero :
      accumulatedDissipation initialTime ≡ 0ℚ
    accumulatedDissipationNonnegative : ∀ time →
      0ℚ ≤ accumulatedDissipation time

    -- Exact fundamental-theorem / finite integration producer.
    integrateDifferentialIdentity :
      (∀ time →
        energyDerivative derivativeData time
        + viscosity derivativeData
          * gradientEnergy derivativeData
              (stateAt derivativeData time)
        ≡ 0ℚ) →
      ∀ time →
      energy (stateAt derivativeData time)
        + accumulatedDissipation time
      ≡ energy (stateAt derivativeData initialTime)

open IntegratedPhysicalFiniteEnergy public

physicalFiniteIntegratedEnergyIdentity :
  ∀ {timeLevel stateLevel}
    {Time : Set timeLevel}
    {State : Set stateLevel}
    {derivativeData : PhysicalFiniteEnergyDerivative Time State} →
  (integrated : IntegratedPhysicalFiniteEnergy derivativeData) →
  ∀ time →
  energy integrated (stateAt derivativeData time)
    + accumulatedDissipation integrated time
  ≡ energy integrated (stateAt derivativeData (initialTime integrated))
physicalFiniteIntegratedEnergyIdentity {derivativeData = derivativeData}
    integrated =
  integrateDifferentialIdentity integrated
    (physicalFiniteDifferentialEnergyIdentity derivativeData)

physicalEnergyContinuationTrajectory :
  ∀ {Time State}
    {derivativeData : PhysicalFiniteEnergyDerivative Time State} →
  IntegratedPhysicalFiniteEnergy derivativeData →
  Continuation.FiniteGalerkinEnergyTrajectory
physicalEnergyContinuationTrajectory
    {derivativeData = derivativeData} integrated = record
  { Continuation.FiniteGalerkinEnergyTrajectory.Time = _
  ; Continuation.FiniteGalerkinEnergyTrajectory.State = _
  ; Continuation.FiniteGalerkinEnergyTrajectory.initialTime =
      initialTime integrated
  ; Continuation.FiniteGalerkinEnergyTrajectory.stateAt =
      stateAt derivativeData
  ; Continuation.FiniteGalerkinEnergyTrajectory.energy =
      energy integrated
  ; Continuation.FiniteGalerkinEnergyTrajectory.accumulatedDissipation =
      accumulatedDissipation integrated
  ; Continuation.FiniteGalerkinEnergyTrajectory.initialDissipationZero =
      initialDissipationZero integrated
  ; Continuation.FiniteGalerkinEnergyTrajectory.dissipationNonnegative =
      accumulatedDissipationNonnegative integrated
  ; Continuation.FiniteGalerkinEnergyTrajectory.energyIdentity =
      physicalFiniteIntegratedEnergyIdentity integrated
  }

physicalFiniteDifferentialEnergyIdentityClosed : Bool
physicalFiniteDifferentialEnergyIdentityClosed = true

literalTriadCancellationProducerClosed : Bool
literalTriadCancellationProducerClosed = false

realTimeIntegrationProducerClosed : Bool
realTimeIntegrationProducerClosed = false

physicalFiniteDifferentialEnergyIdentityClosedIsTrue :
  physicalFiniteDifferentialEnergyIdentityClosed ≡ true
physicalFiniteDifferentialEnergyIdentityClosedIsTrue = refl

literalTriadCancellationProducerClosedIsFalse :
  literalTriadCancellationProducerClosed ≡ false
literalTriadCancellationProducerClosedIsFalse = refl

realTimeIntegrationProducerClosedIsFalse :
  realTimeIntegrationProducerClosed ≡ false
realTimeIntegrationProducerClosedIsFalse = refl
