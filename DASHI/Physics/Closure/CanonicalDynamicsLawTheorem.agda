module DASHI.Physics.Closure.CanonicalDynamicsLawTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Closure.CanonicalSpinDiracConsumer as CSDC
open import DASHI.Physics.Closure.DynamicalClosure as DC
open import DASHI.Physics.Closure.DynamicalClosureStatus as DCS
open import DASHI.Physics.Closure.DynamicalClosureWitness as DCW
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI

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
    }
