module DASHI.Physics.Closure.ConstraintClosureFromCanonicalPathTheorem where

open import Agda.Primitive using (Setω)
open import DASHI.Physics.Constraints.Closure using (ClosureLaw)
open import DASHI.Physics.Constraints.ConcreteInstance as CI
open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ConstraintClosureFromCanonicalPackage as CCFP
open import DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem as CQSB
open import DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem as QTCB
open import DASHI.Physics.Closure.ParametricGaugeConstraintTheorem as PGCT

record CanonicalPathWitness : Setω where
  field
    contractionQuadraticToSignature :
      CQSB.ContractionQuadraticToSignatureBridgeTheorem
    quadraticToClifford :
      QTCB.QuadraticToCliffordBridgeTheorem

canonicalPathWitness : CanonicalPathWitness
canonicalPathWitness =
  record
    { contractionQuadraticToSignature =
        CQSB.canonicalContractionQuadraticToSignatureBridgeTheorem
    ; quadraticToClifford =
        QTCB.canonicalQuadraticToCliffordBridgeTheorem
    }

-- Path-tied transport theorem with a lightweight witness:
-- canonical contraction=>quadratic=>signature and quadratic=>Clifford are fixed,
-- then transported canonical constraint package induces the concrete closure law.
closureFromCanonicalQuadraticSignatureDynamics :
  CanonicalPathWitness →
  (P : CCGP.CanonicalConstraintGaugePackage) →
  CCFP.ConstraintClosureTransport P →
  ClosureLaw CI.CS CI.L
closureFromCanonicalQuadraticSignatureDynamics _ P T =
  CCFP.transportedClosureLaw P T

canonicalPathInducedConstraintClosure :
  ClosureLaw CI.CS CI.L
canonicalPathInducedConstraintClosure =
  closureFromCanonicalQuadraticSignatureDynamics
    canonicalPathWitness
    PGCT.canonicalConstraintGaugePackage
    CCFP.canonicalConstraintClosureTransport
