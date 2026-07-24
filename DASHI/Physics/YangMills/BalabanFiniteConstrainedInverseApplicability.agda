module DASHI.Physics.YangMills.BalabanFiniteConstrainedInverseApplicability where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteOneStepCore as Core
import DASHI.Physics.YangMills.BalabanFiniteCoerciveGreen as Green

------------------------------------------------------------------------
-- Exact applicability package for finite constrained Hessian inversion.
--
-- The point of this record is to prevent a generic coercive-inverse theorem
-- from being applied to the wrong carrier, inner product, Hessian, or selected
-- gauge/block constraint space.
------------------------------------------------------------------------

record FiniteConstrainedCarrier (Vector : Set) : Set₁ where
  field
    vectors : List Vector
    Constraint : Vector → Set
    constrainedEnumerationComplete : ∀ vector → Constraint vector → Set

open FiniteConstrainedCarrier public

record FiniteConstrainedInverseApplicability
    (Vector Scalar Bound : Set) : Set₁ where
  field
    carrier : FiniteConstrainedCarrier Vector
    operatorData : Green.CoerciveFiniteOperator Vector Scalar Bound

    selectedOperatorPreservesConstraint : ∀ vector →
      Constraint carrier vector →
      Constraint carrier (Green.operator operatorData vector)

    selectedOperatorSelfAdjoint : ∀ left right →
      Constraint carrier left →
      Constraint carrier right →
      Green.inner operatorData left (Green.operator operatorData right) ≡
      Green.inner operatorData (Green.operator operatorData left) right

    coercivityIsOnSelectedConstraint : ∀ vector →
      Constraint carrier vector → Green.Coercive operatorData

    inverseAuthority : Green.FiniteCoerciveInverseAuthority operatorData

    selectedInversePreservesConstraint : ∀ vector →
      Constraint carrier vector →
      Constraint carrier (Green.inverse inverseAuthority vector)

open FiniteConstrainedInverseApplicability public

selectedFiniteInverseCertificate :
  ∀ {Vector Scalar Bound}
    (dataSet : FiniteConstrainedInverseApplicability Vector Scalar Bound) →
  Core.FiniteInverseCertificate Vector
selectedFiniteInverseCertificate dataSet =
  Green.toFiniteInverseCertificate (inverseAuthority dataSet)

selectedFiniteGreenOperatorBound :
  ∀ {Vector Scalar Bound}
    (dataSet : FiniteConstrainedInverseApplicability Vector Scalar Bound) →
  Green.GreenOperatorBound Vector Bound
selectedFiniteGreenOperatorBound dataSet =
  Green.toGreenOperatorBound (inverseAuthority dataSet)

selectedInverseLeftOnConstraint :
  ∀ {Vector Scalar Bound}
    (dataSet : FiniteConstrainedInverseApplicability Vector Scalar Bound) →
  ∀ vector → Constraint (carrier dataSet) vector →
  Green.inverse (inverseAuthority dataSet)
    (Green.operator (operatorData dataSet) vector) ≡ vector
selectedInverseLeftOnConstraint dataSet vector constraint =
  Green.inverseLeft (inverseAuthority dataSet) vector

selectedInverseRightOnConstraint :
  ∀ {Vector Scalar Bound}
    (dataSet : FiniteConstrainedInverseApplicability Vector Scalar Bound) →
  ∀ vector → Constraint (carrier dataSet) vector →
  Green.operator (operatorData dataSet)
    (Green.inverse (inverseAuthority dataSet) vector) ≡ vector
selectedInverseRightOnConstraint dataSet vector constraint =
  Green.inverseRight (inverseAuthority dataSet) vector

selectedInverseNormBoundOnConstraint :
  ∀ {Vector Scalar Bound}
    (dataSet : FiniteConstrainedInverseApplicability Vector Scalar Bound) →
  ∀ vector → Constraint (carrier dataSet) vector →
  Green.LessEqual (operatorData dataSet)
    (Green.vectorNorm (operatorData dataSet)
      (Green.inverse (inverseAuthority dataSet) vector))
    (Green.multiplyBound (inverseAuthority dataSet)
      (Green.reciprocalCoercivity (inverseAuthority dataSet))
      (Green.vectorNorm (operatorData dataSet) vector))
selectedInverseNormBoundOnConstraint dataSet vector constraint =
  Green.inverseNormBound (inverseAuthority dataSet) vector

finiteConstrainedInverseApplicabilityAssemblyLevel : ProofLevel
finiteConstrainedInverseApplicabilityAssemblyLevel = machineChecked

finiteConstrainedCoerciveInverseAuthorityLevel : ProofLevel
finiteConstrainedCoerciveInverseAuthorityLevel = standardImported
