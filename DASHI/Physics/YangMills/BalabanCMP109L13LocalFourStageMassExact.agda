module DASHI.Physics.YangMills.BalabanCMP109L13LocalFourStageMassExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tosio Kato, "Perturbation Theory for Linear Operators".
-- DOI: 10.1007/978-3-642-66282-9.
--
-- DASHI CONTRIBUTION
--
-- The same four product-rule leaves used by the existing operator-norm
-- telescope are now converted into the local absolute-mass quantity consumed
-- by the source-faithful L=13 normalized Schur theorem.  For a two-background
-- local kernel we allocate
--
--     outer      1/8,
--     logarithm  1/8,
--     transport  1/4,
--     path       1/2
--
-- of the local mass radius 1/4096.  Entrywise triangle inequality followed by
-- finite summation proves that the sum of the four stage matrices has row and
-- column mass at most 1/4096.  No dense coordinate count occurs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using
  (ℚ; _+_; _*_; _≤_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanCMP109L13NormalizedDerivativeSchurBudgetExact as L13

Matrix : Set → Set → Set
Matrix Row Column = Row → Column → ℚ

addMatrix : ∀ {Row Column} → Matrix Row Column → Matrix Row Column → Matrix Row Column
addMatrix left right row column = left row column + right row column

fourStageMatrix :
  ∀ {Row Column} →
  Matrix Row Column → Matrix Row Column → Matrix Row Column → Matrix Row Column →
  Matrix Row Column
fourStageMatrix outer logarithm transport path =
  addMatrix outer (addMatrix logarithm (addMatrix transport path))

oneEighth oneQuarter oneHalf : ℚ
oneEighth = + 1 / 8
oneQuarter = + 1 / 4
oneHalf = + 1 / 2

outerMass logarithmMass transportMass pathMass : ℚ
outerMass = oneEighth * L13.localTwoBackgroundMass
logarithmMass = oneEighth * L13.localTwoBackgroundMass
transportMass = oneQuarter * L13.localTwoBackgroundMass
pathMass = oneHalf * L13.localTwoBackgroundMass

allocatedMassExact :
  outerMass + (logarithmMass + (transportMass + pathMass))
  ≡ L13.localTwoBackgroundMass
allocatedMassExact = ℚRing.solve []

rowMassAddUpper :
  ∀ {Row Column}
    (columns : List Column)
    (left right : Matrix Row Column) row leftBound rightBound →
  RectSchur.rectAbsoluteRowMass columns left row ≤ leftBound →
  RectSchur.rectAbsoluteRowMass columns right row ≤ rightBound →
  RectSchur.rectAbsoluteRowMass columns (addMatrix left right) row
  ≤ leftBound + rightBound
rowMassAddUpper columns left right row leftBound rightBound leftUpper rightUpper =
  let
    pointwise : ∀ column →
      ∣ addMatrix left right row column ∣
      ≤ ∣ left row column ∣ + ∣ right row column ∣
    pointwise column = ℚP.∣p+q∣≤∣p∣+∣q∣
      (left row column) (right row column)

    summed = Schur.sumPointwiseBelow columns
      (λ column → ∣ addMatrix left right row column ∣)
      (λ column → ∣ left row column ∣ + ∣ right row column ∣)
      pointwise

    split :
      Sums.sumRational columns
        (λ column → ∣ left row column ∣ + ∣ right row column ∣)
      ≡ RectSchur.rectAbsoluteRowMass columns left row
        + RectSchur.rectAbsoluteRowMass columns right row
    split = Fubini.sumRationalAdd columns
      (λ column → ∣ left row column ∣)
      (λ column → ∣ right row column ∣)
  in
  ℚP.≤-trans
    (subst
      (λ upper →
        RectSchur.rectAbsoluteRowMass columns (addMatrix left right) row
        ≤ upper)
      split summed)
    (ℚP.+-mono-≤ leftUpper rightUpper)

columnMassAddUpper :
  ∀ {Row Column}
    (rows : List Row)
    (left right : Matrix Row Column) column leftBound rightBound →
  RectSchur.rectAbsoluteColumnMass rows left column ≤ leftBound →
  RectSchur.rectAbsoluteColumnMass rows right column ≤ rightBound →
  RectSchur.rectAbsoluteColumnMass rows (addMatrix left right) column
  ≤ leftBound + rightBound
columnMassAddUpper rows left right column leftBound rightBound leftUpper rightUpper =
  let
    pointwise : ∀ row →
      ∣ addMatrix left right row column ∣
      ≤ ∣ left row column ∣ + ∣ right row column ∣
    pointwise row = ℚP.∣p+q∣≤∣p∣+∣q∣
      (left row column) (right row column)

    summed = Schur.sumPointwiseBelow rows
      (λ row → ∣ addMatrix left right row column ∣)
      (λ row → ∣ left row column ∣ + ∣ right row column ∣)
      pointwise

    split :
      Sums.sumRational rows
        (λ row → ∣ left row column ∣ + ∣ right row column ∣)
      ≡ RectSchur.rectAbsoluteColumnMass rows left column
        + RectSchur.rectAbsoluteColumnMass rows right column
    split = Fubini.sumRationalAdd rows
      (λ row → ∣ left row column ∣)
      (λ row → ∣ right row column ∣)
  in
  ℚP.≤-trans
    (subst
      (λ upper →
        RectSchur.rectAbsoluteColumnMass rows (addMatrix left right) column
        ≤ upper)
      split summed)
    (ℚP.+-mono-≤ leftUpper rightUpper)

record LocalFourStageMassBudget {Row Column : Set}
    (rows : List Row) (columns : List Column)
    (outer logarithm transport path : Matrix Row Column) : Set₁ where
  field
    outerRows : ∀ row →
      RectSchur.rectAbsoluteRowMass columns outer row ≤ outerMass
    logarithmRows : ∀ row →
      RectSchur.rectAbsoluteRowMass columns logarithm row ≤ logarithmMass
    transportRows : ∀ row →
      RectSchur.rectAbsoluteRowMass columns transport row ≤ transportMass
    pathRows : ∀ row →
      RectSchur.rectAbsoluteRowMass columns path row ≤ pathMass

    outerColumns : ∀ column →
      RectSchur.rectAbsoluteColumnMass rows outer column ≤ outerMass
    logarithmColumns : ∀ column →
      RectSchur.rectAbsoluteColumnMass rows logarithm column ≤ logarithmMass
    transportColumns : ∀ column →
      RectSchur.rectAbsoluteColumnMass rows transport column ≤ transportMass
    pathColumns : ∀ column →
      RectSchur.rectAbsoluteColumnMass rows path column ≤ pathMass

open LocalFourStageMassBudget public

localFourStageRowMass :
  ∀ {Row Column rows columns outer logarithm transport path}
    (budget : LocalFourStageMassBudget
      {Row} {Column} rows columns outer logarithm transport path)
    row →
  RectSchur.rectAbsoluteRowMass columns
    (fourStageMatrix outer logarithm transport path) row
  ≤ L13.localTwoBackgroundMass
localFourStageRowMass
    {columns = columns} {outer = outer} {logarithm = logarithm}
    {transport = transport} {path = path} budget row =
  subst
    (λ upper →
      RectSchur.rectAbsoluteRowMass columns
        (fourStageMatrix outer logarithm transport path) row ≤ upper)
    allocatedMassExact
    (rowMassAddUpper columns outer
      (addMatrix logarithm (addMatrix transport path)) row
      outerMass (logarithmMass + (transportMass + pathMass))
      (outerRows budget row)
      (rowMassAddUpper columns logarithm (addMatrix transport path) row
        logarithmMass (transportMass + pathMass)
        (logarithmRows budget row)
        (rowMassAddUpper columns transport path row
          transportMass pathMass
          (transportRows budget row) (pathRows budget row))))

localFourStageColumnMass :
  ∀ {Row Column rows columns outer logarithm transport path}
    (budget : LocalFourStageMassBudget
      {Row} {Column} rows columns outer logarithm transport path)
    column →
  RectSchur.rectAbsoluteColumnMass rows
    (fourStageMatrix outer logarithm transport path) column
  ≤ L13.localTwoBackgroundMass
localFourStageColumnMass
    {rows = rows} {outer = outer} {logarithm = logarithm}
    {transport = transport} {path = path} budget column =
  subst
    (λ upper →
      RectSchur.rectAbsoluteColumnMass rows
        (fourStageMatrix outer logarithm transport path) column ≤ upper)
    allocatedMassExact
    (columnMassAddUpper rows outer
      (addMatrix logarithm (addMatrix transport path)) column
      outerMass (logarithmMass + (transportMass + pathMass))
      (outerColumns budget column)
      (columnMassAddUpper rows logarithm (addMatrix transport path) column
        logarithmMass (transportMass + pathMass)
        (logarithmColumns budget column)
        (columnMassAddUpper rows transport path column
          transportMass pathMass
          (transportColumns budget column) (pathColumns budget column))))

cmp109L13LocalFourStageMassAllocationLevel : ProofLevel
cmp109L13LocalFourStageMassAllocationLevel = machineChecked

cmp109L13LocalFourStageRowColumnMassLevel : ProofLevel
cmp109L13LocalFourStageRowColumnMassLevel = machineChecked

-- Physical work is now stage-local.  The existing length-24 contour theorem
-- and per-step transport/path budgets are intended to discharge the last two
-- fields; outer exponential and principal-log Frechet mass are the remaining
-- analytic leaves.
physicalCMP109L13OuterLogLocalMassLevel : ProofLevel
physicalCMP109L13OuterLogLocalMassLevel = conditional
