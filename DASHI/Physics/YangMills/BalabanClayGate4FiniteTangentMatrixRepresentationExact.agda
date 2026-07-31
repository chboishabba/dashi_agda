module DASHI.Physics.YangMills.BalabanClayGate4FiniteTangentMatrixRepresentationExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Relation.Binary.PropositionalEquality using
  (cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Finite constrained tangent coordinates and matrix representation.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- At fixed lattice volume the gauge-fixed constrained tangent fibre is finite.
-- Once a complete independent basis is supplied, every restricted Hessian has
-- a finite matrix.  The proofs below derive matrix splitting and norm transport
-- from proof-bearing operator representations; no determinant theorem is used
-- at this layer.
------------------------------------------------------------------------

record FiniteTangentBasis
    (Index Vector Scalar : Set) : Set₁ where
  field
    indices : List Index
    basisVector : Index → Vector
    coordinates : Vector → Index → Scalar
    linearCombination : List Index → (Index → Scalar) → Vector

    BasisIndexComplete : Index → Set
    basisIndexComplete : ∀ index → BasisIndexComplete index

    basisComplete : ∀ vector →
      vector ≡ linearCombination indices (coordinates vector)

    LinearlyIndependent : (Index → Vector) → Set
    basisIndependent : LinearlyIndependent basisVector

open FiniteTangentBasis public

record RestrictedHessianMatrixRepresentation
    (Operator Matrix Vector : Set) : Set₁ where
  field
    referenceOperator physicalOperator remainderOperator : Operator
    referenceMatrix physicalMatrix remainderMatrix : Matrix

    apply : Operator → Vector → Vector
    matrixAction : Matrix → Vector → Vector

    addOperator : Operator → Operator → Operator
    addMatrix : Matrix → Matrix → Matrix

    physicalOperatorSplit :
      physicalOperator ≡ addOperator referenceOperator remainderOperator

    referenceMatrixMeaning :
      matrixAction referenceMatrix ≡ apply referenceOperator
    physicalMatrixMeaning :
      matrixAction physicalMatrix ≡ apply physicalOperator
    remainderMatrixMeaning :
      matrixAction remainderMatrix ≡ apply remainderOperator

    matrixActionAdd : ∀ left right →
      matrixAction (addMatrix left right)
      ≡ addOperatorAction
          (matrixAction left) (matrixAction right)

    addOperatorAction :
      (Vector → Vector) → (Vector → Vector) → Vector → Vector

    addOperatorMeaning : ∀ left right →
      apply (addOperator left right)
      ≡ addOperatorAction (apply left) (apply right)

    matrixActionInjective : ∀ {left right} →
      matrixAction left ≡ matrixAction right → left ≡ right

open RestrictedHessianMatrixRepresentation public

physicalMatrixSplitsExactly :
  ∀ {Operator Matrix Vector}
    (meaning : RestrictedHessianMatrixRepresentation
      Operator Matrix Vector) →
  physicalMatrix meaning
  ≡ addMatrix meaning (referenceMatrix meaning) (remainderMatrix meaning)
physicalMatrixSplitsExactly meaning =
  matrixActionInjective meaning
    (trans
      (physicalMatrixMeaning meaning)
      (trans
        (subst
          (λ operator → apply meaning (physicalOperator meaning) ≡
            apply meaning operator)
          (physicalOperatorSplit meaning)
          (Agda.Builtin.Equality.refl))
        (trans
          (addOperatorMeaning meaning
            (referenceOperator meaning) (remainderOperator meaning))
          (trans
            (cong₂ (addOperatorAction meaning)
              (sym (referenceMatrixMeaning meaning))
              (sym (remainderMatrixMeaning meaning)))
            (sym (matrixActionAdd meaning
              (referenceMatrix meaning) (remainderMatrix meaning)))))))

record MatrixOperatorNormTransport
    (Operator Matrix Bound : Set) : Set₁ where
  field
    selectedOperator : Operator
    selectedMatrix : Matrix

    operatorNorm : Operator → Bound
    matrixNorm : Matrix → Bound

    OperatorLessEqual MatrixLessEqual : Bound → Bound → Set

    matrixRepresentsOperator : Set
    matrixRepresentationEvidence : matrixRepresentsOperator

    matrixNormMeaning :
      matrixNorm selectedMatrix ≡ operatorNorm selectedOperator

    orderMeaning : ∀ left right →
      MatrixLessEqual left right ≡ OperatorLessEqual left right

open MatrixOperatorNormTransport public

matrixNormBoundFromOperatorNormBound :
  ∀ {Operator Matrix Bound}
    (meaning : MatrixOperatorNormTransport Operator Matrix Bound)
    epsilon →
  OperatorLessEqual meaning
    (operatorNorm meaning (selectedOperator meaning)) epsilon →
  MatrixLessEqual meaning
    (matrixNorm meaning (selectedMatrix meaning)) epsilon
matrixNormBoundFromOperatorNormBound meaning epsilon operatorBound =
  subst
    (λ lower → MatrixLessEqual meaning lower epsilon)
    (sym (matrixNormMeaning meaning))
    (subst
      (λ proposition → proposition)
      (sym (orderMeaning meaning
        (operatorNorm meaning (selectedOperator meaning)) epsilon))
      operatorBound)

record HermitianMatrixMeaning
    (Operator Matrix : Set) : Set₁ where
  field
    selectedOperator : Operator
    selectedMatrix : Matrix
    OperatorSelfAdjoint : Operator → Set
    MatrixHermitian : Matrix → Set
    selectedOperatorSelfAdjoint : OperatorSelfAdjoint selectedOperator
    selfAdjointRepresentationImpliesHermitian :
      OperatorSelfAdjoint selectedOperator → MatrixHermitian selectedMatrix

open HermitianMatrixMeaning public

selectedMatrixHermitian :
  ∀ {Operator Matrix}
    (meaning : HermitianMatrixMeaning Operator Matrix) →
  MatrixHermitian meaning (selectedMatrix meaning)
selectedMatrixHermitian meaning =
  selfAdjointRepresentationImpliesHermitian meaning
    (selectedOperatorSelfAdjoint meaning)

finiteTangentBasisCarrierLevel : ProofLevel
finiteTangentBasisCarrierLevel = machineChecked

restrictedHessianMatrixSplitLevel : ProofLevel
restrictedHessianMatrixSplitLevel = machineChecked

matrixOperatorNormTransportLevel : ProofLevel
matrixOperatorNormTransportLevel = machineChecked

selfAdjointMatrixHermitianTransportLevel : ProofLevel
selfAdjointMatrixHermitianTransportLevel = machineChecked

physicalGaugeFixedTangentBasisInputsLevel : ProofLevel
physicalGaugeFixedTangentBasisInputsLevel = conditional

physicalRestrictedMatrixRepresentationInputsLevel : ProofLevel
physicalRestrictedMatrixRepresentationInputsLevel = conditional

physicalMatrixActionInjectivityInputsLevel : ProofLevel
physicalMatrixActionInjectivityInputsLevel = conditional

physicalMatrixOperatorNormIdentificationInputsLevel : ProofLevel
physicalMatrixOperatorNormIdentificationInputsLevel = conditional
