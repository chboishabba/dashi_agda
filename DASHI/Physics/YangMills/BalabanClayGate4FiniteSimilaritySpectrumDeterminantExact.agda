module DASHI.Physics.YangMills.BalabanClayGate4FiniteSimilaritySpectrumDeterminantExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4FiniteDeterminantFactorizationExact as Determinant

------------------------------------------------------------------------
-- Exact similarity transport for spectrum and determinant.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- A change from one finite basis to another sends A to S^{-1} A S.  The
-- determinant is unchanged by multiplicativity, and every eigenpair is carried
-- to an eigenpair with the same eigenvalue.  These are proved below from the
-- explicit matrix inverse and action laws, so the tree-gauge and Bałaban-slice
-- matrices may be related without postulating basis invariance separately.
------------------------------------------------------------------------

record CommutativeMultiplicativeScalar (Scalar : Set) : Set₁ where
  field
    one : Scalar
    multiply : Scalar → Scalar → Scalar
    associative : ∀ left middle right →
      multiply (multiply left middle) right
      ≡ multiply left (multiply middle right)
    commutative : ∀ left right → multiply left right ≡ multiply right left
    identityLeft : ∀ value → multiply one value ≡ value
    identityRight : ∀ value → multiply value one ≡ value

open CommutativeMultiplicativeScalar public

record FiniteSimilarityDeterminantData
    (Matrix Scalar : Set) : Set₁ where
  field
    matrixAlgebra : Determinant.DeterminantMatrixAlgebra Matrix Scalar
    scalarAlgebra : CommutativeMultiplicativeScalar Scalar

    scalarMultiplicationExact :
      Determinant.multiplyScalar matrixAlgebra ≡ multiply scalarAlgebra

    determinantIdentity :
      Determinant.determinant matrixAlgebra
        (Determinant.identityMatrix matrixAlgebra)
      ≡ one scalarAlgebra

    change inverseChange operator : Matrix
    inverseChangeLeft :
      Determinant.multiplyMatrix matrixAlgebra inverseChange change
      ≡ Determinant.identityMatrix matrixAlgebra

open FiniteSimilarityDeterminantData public

similarityMatrix :
  ∀ {Matrix Scalar} →
  FiniteSimilarityDeterminantData Matrix Scalar → Matrix
similarityMatrix dataSet =
  Determinant.multiplyMatrix (matrixAlgebra dataSet)
    (inverseChange dataSet)
    (Determinant.multiplyMatrix (matrixAlgebra dataSet)
      (operator dataSet) (change dataSet))

determinantProductInSelectedScalar :
  ∀ {Matrix Scalar}
    (dataSet : FiniteSimilarityDeterminantData Matrix Scalar)
    left right →
  Determinant.determinant (matrixAlgebra dataSet)
    (Determinant.multiplyMatrix (matrixAlgebra dataSet) left right)
  ≡ multiply (scalarAlgebra dataSet)
      (Determinant.determinant (matrixAlgebra dataSet) left)
      (Determinant.determinant (matrixAlgebra dataSet) right)
determinantProductInSelectedScalar dataSet left right =
  trans
    (Determinant.determinantMultiplicative
      (matrixAlgebra dataSet) left right)
    (cong
      (λ multiplication → multiplication
        (Determinant.determinant (matrixAlgebra dataSet) left)
        (Determinant.determinant (matrixAlgebra dataSet) right))
      (scalarMultiplicationExact dataSet))

determinantInverseTimesChangeIsOne :
  ∀ {Matrix Scalar}
    (dataSet : FiniteSimilarityDeterminantData Matrix Scalar) →
  multiply (scalarAlgebra dataSet)
    (Determinant.determinant (matrixAlgebra dataSet)
      (inverseChange dataSet))
    (Determinant.determinant (matrixAlgebra dataSet)
      (change dataSet))
  ≡ one (scalarAlgebra dataSet)
determinantInverseTimesChangeIsOne dataSet =
  trans
    (sym
      (determinantProductInSelectedScalar dataSet
        (inverseChange dataSet) (change dataSet)))
    (trans
      (cong (Determinant.determinant (matrixAlgebra dataSet))
        (inverseChangeLeft dataSet))
      (determinantIdentity dataSet))

determinantSimilarityInvariant :
  ∀ {Matrix Scalar}
    (dataSet : FiniteSimilarityDeterminantData Matrix Scalar) →
  Determinant.determinant (matrixAlgebra dataSet)
    (similarityMatrix dataSet)
  ≡ Determinant.determinant (matrixAlgebra dataSet)
      (operator dataSet)
determinantSimilarityInvariant dataSet =
  trans
    (determinantProductInSelectedScalar dataSet
      (inverseChange dataSet)
      (Determinant.multiplyMatrix (matrixAlgebra dataSet)
        (operator dataSet) (change dataSet)))
    (trans
      (cong
        (multiply (scalarAlgebra dataSet)
          (Determinant.determinant (matrixAlgebra dataSet)
            (inverseChange dataSet)))
        (determinantProductInSelectedScalar dataSet
          (operator dataSet) (change dataSet)))
      (trans
        (sym
          (associative (scalarAlgebra dataSet)
            (Determinant.determinant (matrixAlgebra dataSet)
              (inverseChange dataSet))
            (Determinant.determinant (matrixAlgebra dataSet)
              (operator dataSet))
            (Determinant.determinant (matrixAlgebra dataSet)
              (change dataSet))))
        (trans
          (cong
            (λ firstProduct → multiply (scalarAlgebra dataSet)
              firstProduct
              (Determinant.determinant (matrixAlgebra dataSet)
                (change dataSet)))
            (commutative (scalarAlgebra dataSet)
              (Determinant.determinant (matrixAlgebra dataSet)
                (inverseChange dataSet))
              (Determinant.determinant (matrixAlgebra dataSet)
                (operator dataSet))))
          (trans
            (associative (scalarAlgebra dataSet)
              (Determinant.determinant (matrixAlgebra dataSet)
                (operator dataSet))
              (Determinant.determinant (matrixAlgebra dataSet)
                (inverseChange dataSet))
              (Determinant.determinant (matrixAlgebra dataSet)
                (change dataSet)))
            (trans
              (cong
                (multiply (scalarAlgebra dataSet)
                  (Determinant.determinant (matrixAlgebra dataSet)
                    (operator dataSet)))
                (determinantInverseTimesChangeIsOne dataSet))
              (identityRight (scalarAlgebra dataSet)
                (Determinant.determinant (matrixAlgebra dataSet)
                  (operator dataSet))))))))

record FiniteSimilaritySpectrumData
    (Matrix Vector Scalar : Set) : Set₁ where
  field
    identityMatrix : Matrix
    multiplyMatrix : Matrix → Matrix → Matrix
    applyMatrix : Matrix → Vector → Vector
    scaleVector : Scalar → Vector → Vector

    multiplyAssociative : ∀ left middle right →
      multiplyMatrix (multiplyMatrix left middle) right
      ≡ multiplyMatrix left (multiplyMatrix middle right)
    actionMultiplication : ∀ left right vector →
      applyMatrix (multiplyMatrix left right) vector
      ≡ applyMatrix left (applyMatrix right vector)
    actionIdentity : ∀ vector → applyMatrix identityMatrix vector ≡ vector
    actionScale : ∀ matrix scalar vector →
      applyMatrix matrix (scaleVector scalar vector)
      ≡ scaleVector scalar (applyMatrix matrix vector)

    change inverseChange operator : Matrix
    changeInverseRight :
      multiplyMatrix change inverseChange ≡ identityMatrix

open FiniteSimilaritySpectrumData public

similarityOperator :
  ∀ {Matrix Vector Scalar} →
  FiniteSimilaritySpectrumData Matrix Vector Scalar → Matrix
similarityOperator dataSet =
  multiplyMatrix dataSet
    (inverseChange dataSet)
    (multiplyMatrix dataSet (operator dataSet) (change dataSet))

record Eigenpair
    {Matrix Vector Scalar : Set}
    (dataSet : FiniteSimilaritySpectrumData Matrix Vector Scalar)
    (matrix : Matrix) : Set where
  field
    vector : Vector
    eigenvalue : Scalar
    eigenEquation :
      applyMatrix dataSet matrix vector
      ≡ scaleVector dataSet eigenvalue vector

open Eigenpair public

changeAfterInverseReturnsVector :
  ∀ {Matrix Vector Scalar}
    (dataSet : FiniteSimilaritySpectrumData Matrix Vector Scalar)
    vectorValue →
  applyMatrix dataSet (change dataSet)
    (applyMatrix dataSet (inverseChange dataSet) vectorValue)
  ≡ vectorValue
changeAfterInverseReturnsVector dataSet vectorValue =
  trans
    (sym
      (actionMultiplication dataSet
        (change dataSet) (inverseChange dataSet) vectorValue))
    (trans
      (cong (λ matrix → applyMatrix dataSet matrix vectorValue)
        (changeInverseRight dataSet))
      (actionIdentity dataSet vectorValue))

transportEigenpairThroughSimilarity :
  ∀ {Matrix Vector Scalar}
    (dataSet : FiniteSimilaritySpectrumData Matrix Vector Scalar) →
  Eigenpair dataSet (operator dataSet) →
  Eigenpair dataSet (similarityOperator dataSet)
transportEigenpairThroughSimilarity dataSet source = record
  { Eigenpair.vector =
      applyMatrix dataSet (inverseChange dataSet) (vector source)
  ; Eigenpair.eigenvalue = eigenvalue source
  ; Eigenpair.eigenEquation =
      trans
        (actionMultiplication dataSet
          (inverseChange dataSet)
          (multiplyMatrix dataSet (operator dataSet) (change dataSet))
          (applyMatrix dataSet (inverseChange dataSet) (vector source)))
        (trans
          (cong (applyMatrix dataSet (inverseChange dataSet))
            (trans
              (actionMultiplication dataSet
                (operator dataSet) (change dataSet)
                (applyMatrix dataSet (inverseChange dataSet)
                  (vector source)))
              (cong (applyMatrix dataSet (operator dataSet))
                (changeAfterInverseReturnsVector dataSet (vector source)))))
          (trans
            (cong (applyMatrix dataSet (inverseChange dataSet))
              (eigenEquation source))
            (actionScale dataSet (inverseChange dataSet)
              (eigenvalue source) (vector source))))
  }

finiteSimilarityDeterminantInvariantLevel : ProofLevel
finiteSimilarityDeterminantInvariantLevel = machineChecked

finiteSimilarityEigenpairTransportLevel : ProofLevel
finiteSimilarityEigenpairTransportLevel = machineChecked

physicalTreeToBalabanChangeOfBasisInputsLevel : ProofLevel
physicalTreeToBalabanChangeOfBasisInputsLevel = conditional
