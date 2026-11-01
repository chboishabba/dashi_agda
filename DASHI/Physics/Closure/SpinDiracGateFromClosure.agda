module DASHI.Physics.Closure.SpinDiracGateFromClosure where

open import Agda.Primitive using (Level; _⊔_; lsuc)

open import DASHI.Geometry.CliffordGate using (RingLike)
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Physics.Closure.DynamicalClosure as DC
open import DASHI.Physics.Closure.DynamicalClosureStatus as DCS
open import DASHI.Physics.Closure.DynamicalClosureWitness as DCW
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.PhysicsClosureFull as PCF
open import DASHI.Physics.SpinDiracGateFromMetric
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES

-- Expose the spin/dirac gate type tied to the forced metric from a closure.
-- Stage C prefers the minimum-credible closure boundary so downstream
-- consumers stay attached to the real dynamics package instead of only the
-- metric seam.
SpinDiracGateType :
  (C : PCF.PhysicsClosureFull) →
  ∀ {m ℓψ ℓa ℓg} (Ψ : Set ℓψ)
    (R : RingLike (QF.ScalarField.S QES.ScalarFieldℤ)) →
  Set (lsuc (ℓψ ⊔ ℓa ⊔ ℓg))
SpinDiracGateType C {m} {ℓψ} {ℓa} {ℓg} Ψ R =
  SpinDiracGateFromMetric {ℓa = ℓa} {ℓg = ℓg}
    (QES.AdditiveVecℤ {m})
    QES.ScalarFieldℤ
    (PCF.PhysicsClosureFull.polarizationZ C {m})
    R
    Ψ

requiredDynamics :
  (C : PCF.PhysicsClosureFull) → DC.DynamicalClosure
requiredDynamics C = PCF.PhysicsClosureFull.dynamics C

requiredDynamicsStatus :
  (C : PCF.PhysicsClosureFull) → DCS.DynamicalClosureStatus
requiredDynamicsStatus C = DC.DynamicalClosure.status (requiredDynamics C)

SpinDiracGateTypeFromMinimal :
  (C : MCPC.MinimalCrediblePhysicsClosure) →
  ∀ {m ℓψ ℓa ℓg} (Ψ : Set ℓψ)
    (R : RingLike (QF.ScalarField.S QES.ScalarFieldℤ)) →
  Set (lsuc (ℓψ ⊔ ℓa ⊔ ℓg))
SpinDiracGateTypeFromMinimal C {m} {ℓψ} {ℓa} {ℓg} Ψ R =
  SpinDiracGateType (MCPC.full C) {m} {ℓψ} {ℓa} {ℓg} Ψ R

requiredDynamicsFromMinimal :
  (C : MCPC.MinimalCrediblePhysicsClosure) → DC.DynamicalClosure
requiredDynamicsFromMinimal = MCPC.authoritativeDynamics

requiredDynamicsWitnessFromMinimal :
  (C : MCPC.MinimalCrediblePhysicsClosure) → DCW.DynamicalClosureWitness
requiredDynamicsWitnessFromMinimal = MCPC.authoritativeDynamicsWitness

requiredDynamicsStatusFromMinimal :
  (C : MCPC.MinimalCrediblePhysicsClosure) → DCS.DynamicalClosureStatus
requiredDynamicsStatusFromMinimal C =
  DC.DynamicalClosure.status (requiredDynamicsFromMinimal C)
