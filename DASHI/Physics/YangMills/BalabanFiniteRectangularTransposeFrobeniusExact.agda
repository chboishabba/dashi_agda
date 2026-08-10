module DASHI.Physics.YangMills.BalabanFiniteRectangularTransposeFrobeniusExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn; Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Augustin-Louis Cauchy, finite-sum inequality (1821), and
-- Hermann Amandus Schwarz, integral inequality (1888).
-- No DOI applies to these classical results.
--
-- DASHI CONTRIBUTION
--
-- Prove the finite rectangular estimate needed to turn a *forward* physical
-- gauge-defect estimate into an estimate for the transpose/adjoint defect.
-- If every column e_j of a literal rectangular rational matrix E satisfies
--
--      sum_i E_ij^2 <= B,
--
-- then, for every row vector lambda,
--
--      ||E^T lambda||^2
--        <= (# columns) B ||lambda||^2.
--
-- The proof is the literal finite Cauchy--Schwarz inequality column by column,
-- followed by a finite ordered sum.  There is no appeal to equality of
-- abstract operator norms, singular values, or a spectral theorem.  The
-- deliberately crude Frobenius factor is useful here because the selected
-- radius rho=1/8192 leaves ample exact rational slack.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length; map)
open import Data.Product.Base using (_,_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

------------------------------------------------------------------------
-- Literal finite rectangular algebra.
------------------------------------------------------------------------

record RectangularColumnBound {Row Column : Set} : Set₁ where
  field
    rows : List Row
    columns : List Column
    matrix : Row → Column → ℚ
    columnBound : ℚ
    columnBoundNonnegative : 0ℚ ≤ columnBound

    columnBounded : ∀ column →
      Sums.sumRational rows
        (λ row → matrix row column * matrix row column)
      ≤ columnBound
open RectangularColumnBound public

rowVectorNormSq :
  ∀ {Row Column} →
  RectangularColumnBound {Row} {Column} →
  (Row → ℚ) → ℚ
rowVectorNormSq dataSet vector =
  Sums.sumRational (rows dataSet)
    (λ row → vector row * vector row)

transposeApply :
  ∀ {Row Column} →
  RectangularColumnBound {Row} {Column} →
  (Row → ℚ) → Column → ℚ
transposeApply dataSet vector column =
  Sums.sumRational (rows dataSet)
    (λ row → matrix dataSet row column * vector row)

transposeNormSq :
  ∀ {Row Column} →
  RectangularColumnBound {Row} {Column} →
  (Row → ℚ) → ℚ
transposeNormSq dataSet vector =
  Sums.sumRational (columns dataSet)
    (λ column →
      transposeApply dataSet vector column
      * transposeApply dataSet vector column)

columnPairs :
  ∀ {Row Column}
    (dataSet : RectangularColumnBound {Row} {Column}) →
  (Row → ℚ) → Column → List FiniteL2.Pair
columnPairs dataSet vector column =
  map
    (λ row → matrix dataSet row column , vector row)
    (rows dataSet)

pairDotMapExact :
  ∀ {Index : Set} (indices : List Index)
    (left right : Index → ℚ) →
  FiniteL2.pairDot
    (map (λ index → left index , right index) indices)
  ≡ Sums.sumRational indices
      (λ index → left index * right index)
pairDotMapExact [] left right = refl
pairDotMapExact (index ∷ indices) left right
  rewrite pairDotMapExact indices left right = refl

leftNormMapExact :
  ∀ {Index : Set} (indices : List Index)
    (left right : Index → ℚ) →
  FiniteL2.leftNormSquared
    (map (λ index → left index , right index) indices)
  ≡ Sums.sumRational indices
      (λ index → left index * left index)
leftNormMapExact [] left right = refl
leftNormMapExact (index ∷ indices) left right
  rewrite leftNormMapExact indices left right = refl

rightNormMapExact :
  ∀ {Index : Set} (indices : List Index)
    (left right : Index → ℚ) →
  FiniteL2.rightNormSquared
    (map (λ index → left index , right index) indices)
  ≡ Sums.sumRational indices
      (λ index → right index * right index)
rightNormMapExact [] left right = refl
rightNormMapExact (index ∷ indices) left right
  rewrite rightNormMapExact indices left right = refl

transposeEntryCauchySquared :
  ∀ {Row Column}
    (dataSet : RectangularColumnBound {Row} {Column})
    vector column →
  transposeApply dataSet vector column
    * transposeApply dataSet vector column
  ≤ Sums.sumRational (rows dataSet)
      (λ row → matrix dataSet row column * matrix dataSet row column)
      * rowVectorNormSq dataSet vector
transposeEntryCauchySquared dataSet vector column =
  let
    pairs = columnPairs dataSet vector column
    raw = FiniteL2.finiteCauchySchwarzSquared pairs
  in
  subst
    (λ dotValue →
      dotValue * dotValue
      ≤ Sums.sumRational (rows dataSet)
          (λ row → matrix dataSet row column * matrix dataSet row column)
        * rowVectorNormSq dataSet vector)
    (pairDotMapExact
      (rows dataSet) (λ row → matrix dataSet row column) vector)
    (subst
      (λ leftNorm →
        FiniteL2.pairDot pairs * FiniteL2.pairDot pairs
        ≤ leftNorm * rowVectorNormSq dataSet vector)
      (leftNormMapExact
        (rows dataSet) (λ row → matrix dataSet row column) vector)
      (subst
        (λ rightNorm →
          FiniteL2.pairDot pairs * FiniteL2.pairDot pairs
          ≤ FiniteL2.leftNormSquared pairs * rightNorm)
        (rightNormMapExact
          (rows dataSet) (λ row → matrix dataSet row column) vector)
        raw))

rowVectorNormSqNonnegative :
  ∀ {Row Column}
    (dataSet : RectangularColumnBound {Row} {Column}) vector →
  0ℚ ≤ rowVectorNormSq dataSet vector
rowVectorNormSqNonnegative dataSet vector =
  Schur.sumNonnegative
    (rows dataSet)
    (λ row → vector row * vector row)
    (λ row → FiniteL2.squareNonnegative (vector row))

transposeEntryBelowUniformColumnBound :
  ∀ {Row Column}
    (dataSet : RectangularColumnBound {Row} {Column}) vector column →
  transposeApply dataSet vector column
    * transposeApply dataSet vector column
  ≤ columnBound dataSet * rowVectorNormSq dataSet vector
transposeEntryBelowUniformColumnBound dataSet vector column =
  let
    cauchy = transposeEntryCauchySquared dataSet vector column
    scaledColumn :
      Sums.sumRational (rows dataSet)
          (λ row → matrix dataSet row column * matrix dataSet row column)
        * rowVectorNormSq dataSet vector
      ≤ columnBound dataSet * rowVectorNormSq dataSet vector
    scaledColumn =
      Norm.scaleNonnegative
        (rowVectorNormSq dataSet vector)
        (rowVectorNormSqNonnegative dataSet vector)
        (columnBounded dataSet column)
  in
  ℚP.≤-trans cauchy scaledColumn

sumConstantAsLength :
  ∀ {Index : Set} (indices : List Index) constant →
  Sums.sumRational indices (λ _ → constant)
  ≡ Sums.natAsRational (length indices) * constant
sumConstantAsLength [] constant = ℚRing.solve-∀ constant
sumConstantAsLength (_ ∷ indices) constant
  rewrite sumConstantAsLength indices constant =
  ℚRing.solve-∀ constant (Sums.natAsRational (length indices))

transposeFrobeniusBound :
  ∀ {Row Column}
    (dataSet : RectangularColumnBound {Row} {Column}) vector →
  transposeNormSq dataSet vector
  ≤ Sums.natAsRational (length (columns dataSet))
      * columnBound dataSet * rowVectorNormSq dataSet vector
transposeFrobeniusBound dataSet vector =
  let
    constant = columnBound dataSet * rowVectorNormSq dataSet vector

    pointwise :
      transposeNormSq dataSet vector
      ≤ Sums.sumRational (columns dataSet) (λ _ → constant)
    pointwise =
      Schur.sumPointwiseBelow
        (columns dataSet)
        (λ column →
          transposeApply dataSet vector column
          * transposeApply dataSet vector column)
        (λ _ → constant)
        (transposeEntryBelowUniformColumnBound dataSet vector)

    folded :
      Sums.sumRational (columns dataSet) (λ _ → constant)
      ≡ Sums.natAsRational (length (columns dataSet)) * constant
    folded = sumConstantAsLength (columns dataSet) constant
  in
  subst
    (λ upper → transposeNormSq dataSet vector ≤ upper)
    (trans folded
      (ℚRing.solve-∀
        (Sums.natAsRational (length (columns dataSet)))
        (columnBound dataSet)
        (rowVectorNormSq dataSet vector)))
    pointwise

finiteRectangularTransposeFrobeniusLevel : ProofLevel
finiteRectangularTransposeFrobeniusLevel = machineChecked
