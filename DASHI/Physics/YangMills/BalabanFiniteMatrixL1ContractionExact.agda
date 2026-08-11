module DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Issai Schur, classical matrix norm test (1911). No DOI applies to the
-- original result.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Prove directly on a proof-bearing finite carrier that a uniform absolute
-- column-mass bound q controls the induced l1 action:
--
--   sup_j sum_i |K(i,j)| <= q
--       => ||K v||_1 <= q ||v||_1.
--
-- The proof is finite triangle inequality + Fubini + nonnegative
-- multiplication.  No spectral theorem, norm-completion assumption, or
-- floating estimate enters.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteColumnMassExact as ColumnMass

SquareKernel : Set → Set
SquareKernel Index = Index → Index → ℚ

Vector : Set → Set
Vector Index = Index → ℚ

vectorL1 : ∀ {Index : Set} → List Index → Vector Index → ℚ
vectorL1 indices vector =
  Sums.sumRational indices (λ index → ∣ vector index ∣)

applyKernel : ∀ {Index : Set} →
  List Index → SquareKernel Index → Vector Index → Vector Index
applyKernel indices kernel vector row =
  Sums.sumRational indices (λ column → kernel row column * vector column)

applyEntryAbsoluteUpper : ∀ {Index : Set}
  (indices : List Index) kernel vector row →
  ∣ applyKernel indices kernel vector row ∣
  ≤ Sums.sumRational indices
      (λ column → ∣ kernel row column ∣ * ∣ vector column ∣)
applyEntryAbsoluteUpper indices kernel vector row =
  subst
    (λ upper → ∣ applyKernel indices kernel vector row ∣ ≤ upper)
    (Schur.sumAbsoluteProductsExact
      indices (kernel row) vector)
    (Schur.sumAbsoluteTriangle
      indices (λ column → kernel row column * vector column))

applyL1FubiniUpper : ∀ {Index : Set}
  (indices : List Index) kernel vector →
  vectorL1 indices (applyKernel indices kernel vector)
  ≤ Sums.sumRational indices
      (λ column →
        ∣ vector column ∣
          * ColumnMass.squareColumnMass indices kernel column)
applyL1FubiniUpper indices kernel vector =
  let
    triangle = Schur.sumPointwiseBelow indices _ _
      (applyEntryAbsoluteUpper indices kernel vector)

    swap :
      Sums.sumRational indices
        (λ row →
          Sums.sumRational indices
            (λ column → ∣ kernel row column ∣ * ∣ vector column ∣))
      ≡ Sums.sumRational indices
        (λ column →
          Sums.sumRational indices
            (λ row → ∣ kernel row column ∣ * ∣ vector column ∣))
    swap = Fubini.sumSwap indices indices
      (λ row column → ∣ kernel row column ∣ * ∣ vector column ∣)

    factor :
      Sums.sumRational indices
        (λ column →
          Sums.sumRational indices
            (λ row → ∣ kernel row column ∣ * ∣ vector column ∣))
      ≡ Sums.sumRational indices
        (λ column →
          ∣ vector column ∣
            * ColumnMass.squareColumnMass indices kernel column)
    factor = Sums.sumRationalCong indices _ _
      (λ column →
        trans
          (Sums.sumRationalCong indices _ _
            (λ row → ℚP.*-comm
              ∣ kernel row column ∣ ∣ vector column ∣))
          (Sums.sumRationalScale ∣ vector column ∣ indices
            (λ row → ∣ kernel row column ∣)))
  in
  subst
    (λ upper → vectorL1 indices (applyKernel indices kernel vector) ≤ upper)
    (trans swap factor)
    triangle

applyKernelL1Bound : ∀ {Index : Set}
  (indices : List Index) kernel vector q →
  0ℚ ≤ q →
  (∀ column → ColumnMass.squareColumnMass indices kernel column ≤ q) →
  vectorL1 indices (applyKernel indices kernel vector)
  ≤ q * vectorL1 indices vector
applyKernelL1Bound indices kernel vector q qNonnegative columnBound =
  let
    fubini = applyL1FubiniUpper indices kernel vector

    pointwise : ∀ column →
      ∣ vector column ∣
        * ColumnMass.squareColumnMass indices kernel column
      ≤ ∣ vector column ∣ * q
    pointwise column =
      Norm.scaleNonnegative ∣ vector column ∣
        (ℚP.0≤∣p∣ (vector column))
        (columnBound column)

    summed = Schur.sumPointwiseBelow indices _ _ pointwise

    factor :
      Sums.sumRational indices
        (λ column → ∣ vector column ∣ * q)
      ≡ q * vectorL1 indices vector
    factor =
      trans
        (Sums.sumRationalCong indices _ _
          (λ column → ℚP.*-comm ∣ vector column ∣ q))
        (Sums.sumRationalScale q indices
          (λ column → ∣ vector column ∣))
  in
  ℚP.≤-trans fubini
    (subst
      (λ upper →
        Sums.sumRational indices
          (λ column →
            ∣ vector column ∣
              * ColumnMass.squareColumnMass indices kernel column)
        ≤ upper)
      factor summed)

finiteMatrixL1ContractionLevel : ProofLevel
finiteMatrixL1ContractionLevel = machineChecked
