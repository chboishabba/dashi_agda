module DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Roger A. Horn; Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Put the differentiated Federbush equation into the conditioning-normalized
-- form required by the physical equation-(0.11) solve.  For a finite contour
-- family J and component matrices
--
--       K_j = J_j T_j,
--
-- define
--
--       Abar = w sum_j K_j,
--       w |J| = 1.
--
-- If every reference K_j is the identity, Abar is exactly the identity.  More
-- generally, if K_j = I + R_j then
--
--       Abar = I + w sum_j R_j
--
-- entry by entry.  Thus the remaining physical inversion theorem is a genuine
-- near-identity estimate on a 3 x 3 su(2) Jacobian, not a determinant problem
-- carrying the artificial contour-count factor.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (natAsRational; sumRational; sumRationalCong; sumRationalScale)
open import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact using
  (sumRationalConstant)
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using
  (sumRationalAdd; sumRationalSubtract)
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanPhysicalSU2RationalMatrixCoordinatesExact as Coordinates

Lie3Vector : Set
Lie3Vector = Physical.LieCoordinate3 → ℚ

Lie3Matrix : Set
Lie3Matrix = Physical.LieCoordinate3 → Physical.LieCoordinate3 → ℚ

identity3 : Lie3Matrix
identity3 row column =
  Coordinates.kroneckerDelta Coordinates.lieCoordinateDecidableEquality row column

matrixAdd : Lie3Matrix → Lie3Matrix → Lie3Matrix
matrixAdd left right row column = left row column + right row column

matrixSubtract : Lie3Matrix → Lie3Matrix → Lie3Matrix
matrixSubtract left right row column = left row column - right row column

matrixScale : ℚ → Lie3Matrix → Lie3Matrix
matrixScale coefficient matrix row column = coefficient * matrix row column

sumMatrices : ∀ {Index : Set} → List Index → (Index → Lie3Matrix) → Lie3Matrix
sumMatrices indices matrix row column =
  sumRational indices (λ index → matrix index row column)

normalizedFederbushJacobian :
  ∀ {Index : Set} → ℚ → List Index → (Index → Lie3Matrix) → Lie3Matrix
normalizedFederbushJacobian weight indices component =
  matrixScale weight (sumMatrices indices component)

normalizedFederbushResidual :
  ∀ {Index : Set} → ℚ → List Index → (Index → Lie3Matrix) → Lie3Matrix
normalizedFederbushResidual weight indices residual =
  matrixScale weight (sumMatrices indices residual)

referenceIdentitySumExact :
  ∀ {Index : Set} (indices : List Index) row column →
  sumRational indices (λ _ → identity3 row column)
  ≡ natAsRational (length indices) * identity3 row column
referenceIdentitySumExact indices row column =
  sumRationalConstant indices (identity3 row column)

normalizedReferenceJacobianIsIdentity :
  ∀ {Index : Set} weight (indices : List Index) →
  weight * natAsRational (length indices) ≡ 1ℚ →
  ∀ row column →
  normalizedFederbushJacobian weight indices (λ _ → identity3) row column
  ≡ identity3 row column
normalizedReferenceJacobianIsIdentity weight indices normalized row column =
  trans
    (cong (weight *_)
      (referenceIdentitySumExact indices row column))
    (normalizeEntry normalized (identity3 row column))
  where
  normalizeEntry : ∀ {w count} → w * count ≡ 1ℚ → ∀ value →
    w * (count * value) ≡ value
  normalizeEntry {w} {count} equality value
    rewrite equality = ℚRing.solve-∀ value

componentAsIdentityPlusResidual :
  ∀ {Index : Set}
    (component residual : Index → Lie3Matrix) → Set
componentAsIdentityPlusResidual component residual =
  ∀ index row column →
    component index row column
    ≡ identity3 row column + residual index row column

sumIdentityPlusResidualExact :
  ∀ {Index : Set} (indices : List Index)
    (component residual : Index → Lie3Matrix) →
  componentAsIdentityPlusResidual component residual →
  ∀ row column →
  sumMatrices indices component row column
  ≡ sumRational indices (λ _ → identity3 row column)
    + sumMatrices indices residual row column
sumIdentityPlusResidualExact indices component residual decomposition row column =
  trans
    (sumRationalCong indices
      (λ index → component index row column)
      (λ index → identity3 row column + residual index row column)
      (λ index → decomposition index row column))
    (sumRationalAdd indices
      (λ _ → identity3 row column)
      (λ index → residual index row column))

normalizedJacobianIsIdentityPlusResidual :
  ∀ {Index : Set} weight (indices : List Index)
    (component residual : Index → Lie3Matrix) →
  weight * natAsRational (length indices) ≡ 1ℚ →
  componentAsIdentityPlusResidual component residual →
  ∀ row column →
  normalizedFederbushJacobian weight indices component row column
  ≡ identity3 row column
    + normalizedFederbushResidual weight indices residual row column
normalizedJacobianIsIdentityPlusResidual
    weight indices component residual normalized decomposition row column =
  trans
    (cong (weight *_)
      (sumIdentityPlusResidualExact
        indices component residual decomposition row column))
    (trans
      (ℚRing.solve-∀
        weight
        (sumRational indices (λ _ → identity3 row column))
        (sumMatrices indices residual row column))
      (cong
        (λ identityPart →
          identityPart
          + weight * sumMatrices indices residual row column)
        (normalizedReferenceJacobianIsIdentity
          weight indices normalized row column)))

matrixApply : Lie3Matrix → Lie3Vector → Lie3Vector
matrixApply matrix vector row =
  sumRational Physical.lieCoordinates3
    (λ column → matrix row column * vector column)

identity3ActsExactly : ∀ vector row →
  matrixApply identity3 vector row ≡ vector row
identity3ActsExactly vector row =
  Coordinates.deltaSumIdentity
    Coordinates.lieCoordinateDecidableEquality
    Coordinates.lieCoordinatesDuplicateFree
    row
    (Coordinates.complete Coordinates.lieCoordinateFinite row)
    vector

normalizedReferenceJacobianActsExactly :
  ∀ {Index : Set} weight (indices : List Index) →
  weight * natAsRational (length indices) ≡ 1ℚ →
  ∀ vector row →
  matrixApply
    (normalizedFederbushJacobian weight indices (λ _ → identity3))
    vector row
  ≡ vector row
normalizedReferenceJacobianActsExactly weight indices normalized vector row =
  trans
    (sumRationalCong Physical.lieCoordinates3 _ _
      (λ column →
        cong (_* vector column)
          (normalizedReferenceJacobianIsIdentity
            weight indices normalized row column)))
    (identity3ActsExactly vector row)

cmp109FederbushNormalizedReferenceJacobianLevel : ProofLevel
cmp109FederbushNormalizedReferenceJacobianLevel = machineChecked

cmp109FederbushIdentityPlusResidualLevel : ProofLevel
cmp109FederbushIdentityPlusResidualLevel = machineChecked
