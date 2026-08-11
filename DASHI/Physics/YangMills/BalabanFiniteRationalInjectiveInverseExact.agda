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
-- analysis.  It isolates exactly one imported finite-linear-algebra authority
-- between the machine-checked strict-contraction injectivity proof and the
-- repository's existing rational inverse-certificate consumer.  Everything
-- specific to the selected physical matrix is proved in the selected module.
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

finiteRationalInjectiveInverseAuthorityLevel : ProofLevel
finiteRationalInjectiveInverseAuthorityLevel = standardImported
