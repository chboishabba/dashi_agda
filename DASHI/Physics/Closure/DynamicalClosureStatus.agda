module DASHI.Physics.Closure.DynamicalClosureStatus where

data PropagationStatus : Set where
  fiberBackedPropagation : PropagationStatus
  strongerPropagationPending : PropagationStatus

data CausalAdmissibilityStatus : Set where
  seamBackedCausalAdmissibility : CausalAdmissibilityStatus
  strongerCausalAdmissibilityPending : CausalAdmissibilityStatus

data MonotoneQuantityStatus : Set where
  mdlLyapunovAndFejer : MonotoneQuantityStatus
  strongerConservedQuantityPending : MonotoneQuantityStatus

data EffectiveGeometryStatus : Set where
  quadraticPolarizationAndOrthogonality : EffectiveGeometryStatus
  strongerGeometryPending : EffectiveGeometryStatus

record DynamicalClosureStatus : Set where
  field
    propagation : PropagationStatus
    causalAdmissibility : CausalAdmissibilityStatus
    monotoneQuantity : MonotoneQuantityStatus
    effectiveGeometry : EffectiveGeometryStatus

