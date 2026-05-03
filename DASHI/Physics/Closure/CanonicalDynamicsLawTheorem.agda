module DASHI.Physics.Closure.CanonicalDynamicsLawTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_<_; _≤_; z≤n; s≤s)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import DASHI.Physics.Closure.CanonicalSpinDiracConsumer as CSDC
open import DASHI.Physics.Closure.DynamicalClosure as DC
open import DASHI.Physics.Closure.DynamicalClosureStatus as DCS
open import DASHI.Physics.Closure.DynamicalClosureWitness as DCW
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI
open import DASHI.Physics.Closure.P0BlockadeProofObligations as P0
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.PressureGradientFlowShiftInstance as PGFSI

ShiftConvergenceRateTarget : Set
ShiftConvergenceRateTarget =
  (s : PGFSI.ShiftFlowState) →
  Σ Nat
    (λ n →
      P0.iterate n PGFSI.shiftFlowEvolve s
        ≡
      SPTI.shiftHeldExitPoint
      ×
      n ≤ PGFSI.shiftFlowPotential s)

shiftConvergenceDescent :
  (s : PGFSI.ShiftFlowState) →
  PGFSI.shiftFlowPotential (PGFSI.shiftFlowEvolve s)
    <
  PGFSI.shiftFlowPotential s
  ⊎
  PGFSI.shiftFlowEvolve s ≡ s
shiftConvergenceDescent SPTI.shiftStartPoint =
  inj₁ (s≤s (s≤s z≤n))
shiftConvergenceDescent SPTI.shiftNextPoint =
  inj₁ (s≤s z≤n)
shiftConvergenceDescent SPTI.shiftHeldExitPoint =
  inj₂ refl

shiftConvergenceRateTarget : ShiftConvergenceRateTarget
shiftConvergenceRateTarget SPTI.shiftStartPoint =
  suc (suc zero) , (refl , s≤s (s≤s z≤n))
shiftConvergenceRateTarget SPTI.shiftNextPoint =
  suc zero , (refl , s≤s z≤n)
shiftConvergenceRateTarget SPTI.shiftHeldExitPoint =
  zero , (refl , z≤n)

canonicalShiftConvergenceBound :
  P0.ConvergenceBound {PGFSI.ShiftFlowState}
canonicalShiftConvergenceBound =
  record
    { K = PGFSI.shiftFlowEvolve
    ; mdl = PGFSI.shiftFlowPotential
    ; descent = shiftConvergenceDescent
    ; fixedPoint = SPTI.shiftHeldExitPoint
    ; converges = shiftConvergenceRateTarget
    }

record CanonicalDynamicsLawTheorem : Setω where
  field
    canonicalConsumer :
      CSDC.SpinDiracConsumerFromMinimal MCCSI.minimumCredibleClosureShift
    canonicalDynamics : DC.DynamicalClosure
    canonicalDynamicsStatus : DCS.DynamicalClosureStatus
    canonicalDynamicsWitness : DCW.DynamicalClosureWitness
    propagationLaw :
      DCS.DynamicalClosureStatus.propagation canonicalDynamicsStatus
      ≡ DCS.fiberBackedPropagation
    causalAdmissibilityLaw :
      DCS.DynamicalClosureStatus.causalAdmissibility canonicalDynamicsStatus
      ≡ DCS.seamBackedCausalAdmissibility
    conservedQuantityLaw :
      DCS.DynamicalClosureStatus.monotoneQuantity canonicalDynamicsStatus
      ≡ DCS.mdlLyapunovAndFejer
    continuumLimitLaw :
      DCS.DynamicalClosureStatus.effectiveGeometry canonicalDynamicsStatus
      ≡ DCS.quadraticPolarizationAndOrthogonality
    realizationIndependentProofShape : DCW.DynamicalClosureWitness
    boundedConvergenceRate :
      P0.ConvergenceBound {PGFSI.ShiftFlowState}
    concreteConvergenceRateTarget :
      ShiftConvergenceRateTarget

canonicalDynamicsLawTheorem : CanonicalDynamicsLawTheorem
canonicalDynamicsLawTheorem =
  record
    { canonicalConsumer =
        CSDC.spinDiracConsumerFromMinimal MCCSI.minimumCredibleClosureShift
    ; canonicalDynamics =
        CSDC.SpinDiracConsumerFromMinimal.dynamics
          (CSDC.spinDiracConsumerFromMinimal MCCSI.minimumCredibleClosureShift)
    ; canonicalDynamicsStatus =
        CSDC.SpinDiracConsumerFromMinimal.dynamicsStatus
          (CSDC.spinDiracConsumerFromMinimal MCCSI.minimumCredibleClosureShift)
    ; canonicalDynamicsWitness =
        CSDC.SpinDiracConsumerFromMinimal.dynamicsWitness
          (CSDC.spinDiracConsumerFromMinimal MCCSI.minimumCredibleClosureShift)
    ; propagationLaw = refl
    ; causalAdmissibilityLaw = refl
    ; conservedQuantityLaw = refl
    ; continuumLimitLaw = refl
    ; realizationIndependentProofShape =
        CSDC.SpinDiracConsumerFromMinimal.dynamicsWitness
          (CSDC.spinDiracConsumerFromMinimal MCCSI.minimumCredibleClosureShift)
    ; boundedConvergenceRate = canonicalShiftConvergenceBound
    ; concreteConvergenceRateTarget = shiftConvergenceRateTarget
    }
