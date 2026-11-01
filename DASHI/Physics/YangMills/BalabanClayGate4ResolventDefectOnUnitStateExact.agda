module DASHI.Physics.YangMills.BalabanClayGate4ResolventDefectOnUnitStateExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4ResolventDefectPipelineExact as Resolvent

------------------------------------------------------------------------
-- Uniform vector defect from the operator resolvent estimate.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics (1995 reprint).
-- DOI: 10.1007/978-3-642-66282-9.
--
-- Once the second resolvent identity controls the operator difference, the
-- defect on a unit fluctuation is automatic.  This module isolates that step so
-- the gauge and constraint channels can share the same theorem literally.
------------------------------------------------------------------------

record ResolventDefectOnUnitState
    (Operator Vector Bound : Set) : Set₁ where
  field
    resolvent : Resolvent.ResolventIdentityData Operator Bound

    apply : Operator → Vector → Vector
    vectorNorm : Vector → Bound

    UnitState : Vector → Set
    one : Bound

    actionNormBound : ∀ operator vector →
      Resolvent.LessEqual (Resolvent.algebra resolvent)
        (vectorNorm (apply operator vector))
        (Resolvent.multiply (Resolvent.algebra resolvent)
          (Resolvent.operatorNorm (Resolvent.algebra resolvent) operator)
          (vectorNorm vector))

    unitNormBelowOne : ∀ vector → UnitState vector →
      Resolvent.LessEqual (Resolvent.algebra resolvent)
        (vectorNorm vector) one

    multiplyRightIdentity : ∀ value →
      Resolvent.multiply (Resolvent.algebra resolvent) value one
      ≡ value

open ResolventDefectOnUnitState public

resolventVectorDefect :
  ∀ {Operator Vector Bound} →
  ResolventDefectOnUnitState Operator Vector Bound →
  Vector → Bound
resolventVectorDefect dataSet vector =
  vectorNorm dataSet
    (apply dataSet (Resolvent.difference (resolvent dataSet)) vector)

resolventVectorDefectUniform :
  ∀ {Operator Vector Bound}
    (dataSet : ResolventDefectOnUnitState Operator Vector Bound)
    vector → UnitState dataSet vector →
  Resolvent.LessEqual (Resolvent.algebra (resolvent dataSet))
    (resolventVectorDefect dataSet vector)
    (Resolvent.differenceBudget (resolvent dataSet))
resolventVectorDefectUniform dataSet vector unit =
  subst
    (λ upper →
      Resolvent.LessEqual (Resolvent.algebra (resolvent dataSet))
        (resolventVectorDefect dataSet vector) upper)
    (multiplyRightIdentity dataSet
      (Resolvent.differenceBudget (resolvent dataSet)))
    (Resolvent.transitive (Resolvent.algebra (resolvent dataSet))
      (actionNormBound dataSet
        (Resolvent.difference (resolvent dataSet)) vector)
      (Resolvent.multiplyMonotone
        (Resolvent.algebra (resolvent dataSet))
        (Resolvent.resolventDifferenceNormBelowBudget
          (resolvent dataSet))
        (unitNormBelowOne dataSet vector unit)))

resolventOperatorToUnitDefectLevel : ProofLevel
resolventOperatorToUnitDefectLevel = machineChecked

physicalResolventActionNormInputsLevel : ProofLevel
physicalResolventActionNormInputsLevel = conditional

physicalUnitStateNormConventionInputsLevel : ProofLevel
physicalUnitStateNormConventionInputsLevel = conditional
