module DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteColumnMassExact where

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
-- Column-mass companion to BalabanFiniteRectangularAbsoluteMassExact.
-- For the rectangular transpose product
--
--   (A B^T)(i,j) = sum_k A(i,k) B(j,k),
--
-- commutativity of rational multiplication gives
--
--   (A B^T)(i,j) = (B A^T)(j,i).
--
-- Therefore
--
--   columnMass(A B^T,j)
--     <= rowMass(B,j) * sup_k columnMass(A,k).
--
-- Together with the row theorem this gives exact l1 and l-infinity control
-- without square roots.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteMassExact as Mass

squareColumnMass :
  ∀ {Row : Set} → List Row → (Row → Row → ℚ) → Row → ℚ
squareColumnMass rows matrix column =
  Sums.sumRational rows (λ row → ∣ matrix row column ∣)

transposeProductSwapExact :
  ∀ {Row Column : Set}
    (columns : List Column)
    (left right : Mass.RectMatrix Row Column)
    row outputRow →
  Mass.transposeProduct columns left right row outputRow
  ≡ Mass.transposeProduct columns right left outputRow row
transposeProductSwapExact columns left right row outputRow =
  Sums.sumRationalCong columns _ _
    (λ column → ℚP.*-comm (left row column) (right outputRow column))

transposeProductColumnMassAsSwappedRow :
  ∀ {Row Column : Set}
    (rows : List Row)
    (columns : List Column)
    (left right : Mass.RectMatrix Row Column)
    outputRow →
  squareColumnMass rows (Mass.transposeProduct columns left right) outputRow
  ≡ Mass.squareRowMass rows
      (Mass.transposeProduct columns right left) outputRow
transposeProductColumnMassAsSwappedRow rows columns left right outputRow =
  Sums.sumRationalCong rows _ _
    (λ row → cong ∣_∣
      (transposeProductSwapExact columns left right row outputRow))

transposeProductColumnMassBound :
  ∀ {Row Column : Set}
    (rows : List Row)
    (columns : List Column)
    (left right : Mass.RectMatrix Row Column)
    (leftColumnBound : ℚ) outputRow →
  0ℚ ≤ leftColumnBound →
  (∀ column → Mass.absoluteRectColumnMass rows left column ≤ leftColumnBound) →
  squareColumnMass rows (Mass.transposeProduct columns left right) outputRow
  ≤ Mass.absoluteRectRowMass columns right outputRow * leftColumnBound
transposeProductColumnMassBound
    rows columns left right leftColumnBound outputRow
    boundNonnegative leftColumnBounded =
  subst
    (λ lower →
      lower ≤ Mass.absoluteRectRowMass columns right outputRow * leftColumnBound)
    (sym (transposeProductColumnMassAsSwappedRow
      rows columns left right outputRow))
    (Mass.transposeProductRowMassBound
      rows columns right left leftColumnBound outputRow
      boundNonnegative leftColumnBounded)

squareColumnMassAdd :
  ∀ {Row : Set} (rows : List Row)
    (left right : Row → Row → ℚ) column →
  squareColumnMass rows (λ i j → left i j + right i j) column
  ≤ squareColumnMass rows left column + squareColumnMass rows right column
squareColumnMassAdd rows left right column =
  let
    pointwise = Schur.sumPointwiseBelow rows _ _
      (λ row → ℚP.∣p+q∣≤∣p∣+∣q∣
        (left row column) (right row column))
  in
  subst
    (λ upper →
      squareColumnMass rows (λ i j → left i j + right i j) column ≤ upper)
    (Mass.sumAddExact rows
      (λ row → ∣ left row column ∣)
      (λ row → ∣ right row column ∣))
    pointwise

squareColumnMassAdd3 :
  ∀ {Row : Set} (rows : List Row)
    (first second third : Row → Row → ℚ) column →
  squareColumnMass rows
    (λ i j → first i j + second i j + third i j) column
  ≤ squareColumnMass rows first column
    + squareColumnMass rows second column
    + squareColumnMass rows third column
squareColumnMassAdd3 rows first second third column =
  let
    firstTwo = λ i j → first i j + second i j
    firstStep = squareColumnMassAdd rows firstTwo third column
    secondStep = squareColumnMassAdd rows first second column
    lifted = ℚP.+-monoˡ-≤ (squareColumnMass rows third column) secondStep
  in
  ℚP.≤-trans firstStep
    (subst
      (λ upper →
        squareColumnMass rows firstTwo column
          + squareColumnMass rows third column ≤ upper)
      (ℚRing.solve-∀
        (squareColumnMass rows first column)
        (squareColumnMass rows second column)
        (squareColumnMass rows third column))
      lifted)

finiteRectangularAbsoluteColumnMassLevel : ProofLevel
finiteRectangularAbsoluteColumnMassLevel = machineChecked
