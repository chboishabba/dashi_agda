module DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteMassExact where

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
-- Finite absolute-mass calculus for rectangular matrices.  If A and B have
-- the same column carrier, then
--
--   (A B^T)(i,j) = sum_k A(i,k) B(j,k).
--
-- The literal triangle inequality plus finite Fubini gives
--
--   rowMass(A B^T,i)
--     <= rowMass(A,i) * sup_k columnMass(B,k).
--
-- This is the l-infinity/absolute-row companion to the repository's existing
-- square-root-free Schur-squared theorem.  It is used by the selected gauge
-- Green lane because L_0 and D_A are rectangular 768 x 3072 matrices whereas
-- their Gram perturbation E_A is square on the 768-row multiplier carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur

RectMatrix : Set → Set → Set
RectMatrix Row Column = Row → Column → ℚ

absoluteRectRowMass :
  ∀ {Row Column : Set} →
  List Column → RectMatrix Row Column → Row → ℚ
absoluteRectRowMass columns matrix row =
  Sums.sumRational columns (λ column → ∣ matrix row column ∣)

absoluteRectColumnMass :
  ∀ {Row Column : Set} →
  List Row → RectMatrix Row Column → Column → ℚ
absoluteRectColumnMass rows matrix column =
  Sums.sumRational rows (λ row → ∣ matrix row column ∣)

transposeProduct :
  ∀ {Row Column : Set} →
  List Column →
  RectMatrix Row Column → RectMatrix Row Column →
  Row → Row → ℚ
transposeProduct columns left right row outputRow =
  Sums.sumRational columns
    (λ column → left row column * right outputRow column)

squareRowMass :
  ∀ {Row : Set} →
  List Row → (Row → Row → ℚ) → Row → ℚ
squareRowMass rows matrix row =
  Sums.sumRational rows (λ outputRow → ∣ matrix row outputRow ∣)

sumAddExact :
  ∀ {Index : Set} (indices : List Index) left right →
  Sums.sumRational indices (λ index → left index + right index)
  ≡ Sums.sumRational indices left + Sums.sumRational indices right
sumAddExact [] left right = ℚRing.solve []
sumAddExact (index ∷ indices) left right
  rewrite sumAddExact indices left right =
  ℚRing.solve-∀
    (left index) (right index)
    (Sums.sumRational indices left)
    (Sums.sumRational indices right)

transposeProductEntryAbsoluteBound :
  ∀ {Row Column : Set}
    (columns : List Column)
    (left right : RectMatrix Row Column)
    row outputRow →
  ∣ transposeProduct columns left right row outputRow ∣
  ≤ Sums.sumRational columns
      (λ column → ∣ left row column ∣ * ∣ right outputRow column ∣)
transposeProductEntryAbsoluteBound columns left right row outputRow =
  subst
    (λ upper → ∣ transposeProduct columns left right row outputRow ∣ ≤ upper)
    (Schur.sumAbsoluteProductsExact
      columns (left row) (right outputRow))
    (Schur.sumAbsoluteTriangle
      columns (λ column → left row column * right outputRow column))

transposeProductRowMassFubiniUpper :
  ∀ {Row Column : Set}
    (rows : List Row) (columns : List Column)
    (left right : RectMatrix Row Column) row →
  squareRowMass rows (transposeProduct columns left right) row
  ≤ Sums.sumRational columns
      (λ column →
        ∣ left row column ∣ * absoluteRectColumnMass rows right column)
transposeProductRowMassFubiniUpper rows columns left right row =
  let
    first :
      Sums.sumRational rows
        (λ outputRow →
          ∣ transposeProduct columns left right row outputRow ∣)
      ≤ Sums.sumRational rows
        (λ outputRow →
          Sums.sumRational columns
            (λ column →
              ∣ left row column ∣ * ∣ right outputRow column ∣))
    first =
      Schur.sumPointwiseBelow rows _ _
        (transposeProductEntryAbsoluteBound columns left right row)

    swapped :
      Sums.sumRational rows
        (λ outputRow →
          Sums.sumRational columns
            (λ column →
              ∣ left row column ∣ * ∣ right outputRow column ∣))
      ≡ Sums.sumRational columns
        (λ column →
          Sums.sumRational rows
            (λ outputRow →
              ∣ left row column ∣ * ∣ right outputRow column ∣))
    swapped =
      Fubini.sumSwap rows columns
        (λ outputRow column →
          ∣ left row column ∣ * ∣ right outputRow column ∣)

    factored :
      Sums.sumRational columns
        (λ column →
          Sums.sumRational rows
            (λ outputRow →
              ∣ left row column ∣ * ∣ right outputRow column ∣))
      ≡ Sums.sumRational columns
        (λ column →
          ∣ left row column ∣ * absoluteRectColumnMass rows right column)
    factored =
      Sums.sumRationalCong columns _ _
        (λ column →
          Sums.sumRationalScale
            ∣ left row column ∣ rows
            (λ outputRow → ∣ right outputRow column ∣))
  in
  subst
    (λ upper →
      squareRowMass rows (transposeProduct columns left right) row ≤ upper)
    (trans swapped factored)
    first

transposeProductRowMassBound :
  ∀ {Row Column : Set}
    (rows : List Row) (columns : List Column)
    (left right : RectMatrix Row Column)
    (columnBound : ℚ) row →
  0ℚ ≤ columnBound →
  (∀ column → absoluteRectColumnMass rows right column ≤ columnBound) →
  squareRowMass rows (transposeProduct columns left right) row
  ≤ absoluteRectRowMass columns left row * columnBound
transposeProductRowMassBound
    rows columns left right columnBound row
    columnBoundNonnegative rightColumnBound =
  let
    pointwise : ∀ column →
      ∣ left row column ∣ * absoluteRectColumnMass rows right column
      ≤ ∣ left row column ∣ * columnBound
    pointwise column =
      Norm.scaleNonnegative
        ∣ left row column ∣
        (ℚP.0≤∣p∣ (left row column))
        (rightColumnBound column)

    bounded :
      Sums.sumRational columns
        (λ column →
          ∣ left row column ∣ * absoluteRectColumnMass rows right column)
      ≤ Sums.sumRational columns
        (λ column → ∣ left row column ∣ * columnBound)
    bounded = Schur.sumPointwiseBelow columns _ _ pointwise

    factored :
      Sums.sumRational columns
        (λ column → ∣ left row column ∣ * columnBound)
      ≡ absoluteRectRowMass columns left row * columnBound
    factored =
      trans
        (Sums.sumRationalCong columns _ _
          (λ column → ℚP.*-comm ∣ left row column ∣ columnBound))
        (trans
          (Sums.sumRationalScale columnBound columns
            (λ column → ∣ left row column ∣))
          (ℚP.*-comm columnBound
            (absoluteRectRowMass columns left row)))
  in
  ℚP.≤-trans
    (transposeProductRowMassFubiniUpper rows columns left right row)
    (subst
      (λ upper →
        Sums.sumRational columns
          (λ column →
            ∣ left row column ∣ * absoluteRectColumnMass rows right column)
        ≤ upper)
      factored bounded)

squareRowMassAdd :
  ∀ {Row : Set} (rows : List Row)
    (left right : Row → Row → ℚ) row →
  squareRowMass rows (λ i j → left i j + right i j) row
  ≤ squareRowMass rows left row + squareRowMass rows right row
squareRowMassAdd rows left right row =
  let
    pointwise : ∀ outputRow →
      ∣ left row outputRow + right row outputRow ∣
      ≤ ∣ left row outputRow ∣ + ∣ right row outputRow ∣
    pointwise outputRow =
      ℚP.∣p+q∣≤∣p∣+∣q∣
        (left row outputRow) (right row outputRow)

    bounded = Schur.sumPointwiseBelow rows _ _ pointwise
  in
  subst
    (λ upper →
      squareRowMass rows (λ i j → left i j + right i j) row ≤ upper)
    (sumAddExact rows
      (λ outputRow → ∣ left row outputRow ∣)
      (λ outputRow → ∣ right row outputRow ∣))
    bounded

squareRowMassAdd3 :
  ∀ {Row : Set} (rows : List Row)
    (first second third : Row → Row → ℚ) row →
  squareRowMass rows
    (λ i j → first i j + second i j + third i j) row
  ≤ squareRowMass rows first row
    + squareRowMass rows second row
    + squareRowMass rows third row
squareRowMassAdd3 rows first second third row =
  let
    firstTwo = λ i j → first i j + second i j
    firstStep = squareRowMassAdd rows firstTwo third row
    secondStep = squareRowMassAdd rows first second row
    lifted = ℚP.+-monoˡ-≤
      (squareRowMass rows third row) secondStep
  in
  ℚP.≤-trans firstStep
    (subst
      (λ upper →
        squareRowMass rows firstTwo row + squareRowMass rows third row ≤ upper)
      (ℚRing.solve-∀
        (squareRowMass rows first row)
        (squareRowMass rows second row)
        (squareRowMass rows third row))
      lifted)

finiteRectangularAbsoluteMassLevel : ProofLevel
finiteRectangularAbsoluteMassLevel = machineChecked
