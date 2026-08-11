module DASHI.Physics.YangMills.BalabanFiniteRationalInjectiveInverseExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- STANDARD FINITE-DIMENSIONAL INPUT
--
-- For an endomorphism of a finite-dimensional vector space over a field,
-- injective <=> surjective <=> invertible.  Applied over Q to a finite square
-- matrix, the inverse is again rational (equivalently by Gaussian elimination,
-- or adj(A)/det(A) once det(A) != 0).
--
-- This module does not disguise that standard theorem as new Yang--Mills
-- analysis.  It isolates it as the one imported finite-linear-algebra authority
-- between the machine-checked strict-contraction injectivity proof and the
-- repository's already-existing rational inverse certificate consumer.
-- Everything specific to the selected physical matrix is proved elsewhere.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix

PointwiseInjective :
  ∀ {Index : Set} →
  Matrix.FiniteRationalCoordinates Index → Matrix.RationalMatrix Index → Set
PointwiseInjective carrier matrix =
  ∀ left right →
  (∀ row →
    Matrix.applyMatrix carrier matrix left row
    ≡ Matrix.applyMatrix carrier matrix right row) →
  ∀ row → left row ≡ right row

record FiniteRationalInjectiveInverseAuthority : Set₁ where
  field
    finiteSquareInjectiveImpliesRationalInverse :
      ∀ {Index : Set}
        (carrier : Matrix.FiniteRationalCoordinates Index)
        (matrix : Matrix.RationalMatrix Index) →
      PointwiseInjective carrier matrix →
      Matrix.RationalMatrixInverseCertificate carrier matrix

open FiniteRationalInjectiveInverseAuthority public

------------------------------------------------------------------------
-- Once an inverse certificate exists, its action is unique pointwise.  This is
-- proved here rather than imported.
------------------------------------------------------------------------

inverseActionUnique :
  ∀ {Index : Set}
    {carrier : Matrix.FiniteRationalCoordinates Index}
    {matrix : Matrix.RationalMatrix Index}
    (first second : Matrix.RationalMatrixInverseCertificate carrier matrix) →
  ∀ source row →
  Matrix.applyMatrix carrier (Matrix.inverseMatrix first) source row
  ≡ Matrix.applyMatrix carrier (Matrix.inverseMatrix second) source row
inverseActionUnique {carrier = carrier} {matrix = matrix}
    first second source row =
  let
    secondSource =
      Matrix.applyMatrix carrier (Matrix.inverseMatrix second) source
  in
  trans
    (cong
      (λ value →
        Matrix.applyMatrix carrier (Matrix.inverseMatrix first) value row)
      (sym (Matrix.matrixInverseRightExact second source row)))
    (trans
      (Matrix.matrixInverseLeftExact first secondSource row)
      refl)
  where
    open import Relation.Binary.PropositionalEquality using (cong; trans)

finiteRationalInjectiveInverseAuthorityLevel : ProofLevel
finiteRationalInjectiveInverseAuthorityLevel = standardImported

finiteRationalInverseUniquenessLevel : ProofLevel
finiteRationalInverseUniquenessLevel = machineChecked
