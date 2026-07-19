module DASHI.Algebra.Quantum.CCRFromAdmissibleFlow where

open import Data.Nat using (_≤_)
open import DASHI.Execution.DeltaConeMDLContract
open import DASHI.Algebra.Quantum.CCRFromProjection

-- Governance boundary: delta-cone/MDL dynamics do not by themselves prove
-- canonical commutation.  CCR emergence additionally requires the concrete
-- projection-Weyl laws.  This record makes that dependency explicit.
record AdmissibleFlowCCRBridge
  {X : Set}
  (G : ExecutionGeometry X)
  (D : CCRData) : Set₁ where
  field
    flow-admissible : ExecutionAdmissible G
    projection-weyl : ProjectionWeylAxioms D

open AdmissibleFlowCCRBridge public

ccr-from-admissible-flow :
  ∀ {X} {G : ExecutionGeometry X} {D : CCRData} →
  AdmissibleFlowCCRBridge G D →
  CCR D
ccr-from-admissible-flow B = stone-vn (projection-weyl B)

-- The execution consequences remain available alongside CCR; neither side is
-- silently discarded by the bridge.
flow-mdl-descent :
  ∀ {X} {G : ExecutionGeometry X} {D : CCRData} →
  (B : AdmissibleFlowCCRBridge G D) →
  ∀ x → mdl G (step G x) ≤ mdl G x
flow-mdl-descent B = execution-descends-mdl (flow-admissible B)
