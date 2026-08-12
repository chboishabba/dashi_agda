module DASHI.Physics.YangMills.BalabanSelectedBlockAverageReferenceEntryBudgetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Convert the existing CMP109-style pointwise reference estimate into the
-- exact nonlinear Gate-I squared L2 budget on the literal selected carriers.
--
-- Let E_U = DQ_U-DQ_ref and E_A = DQ_A-DQ_ref.  If every literal matrix entry
-- obeys
--
--     |E_U(row,column)| <= rho,
--     |E_A(row,column)| <= rho,
--     rho = 1/8192,
--
-- then the two-background derivative difference has entry bound 2 rho.  The
-- selected block-average derivative is a 12 x 3072 rectangular map.  Therefore
-- its absolute masses obey
--
--     rowMass <= 3072*(2 rho) = 3/4,
--     columnMass <= 12*(2 rho) = 3/1024.
--
-- The square-root-free rectangular Schur theorem consequently gives
--
--     ||(DQ_U-DQ_A)h||^2 <= (9/4096)||h||^2.
--
-- This already fits strictly inside the 3711/262144 block-average allowance
-- left by the gauge sector, with exact slack
--
--     3711/262144 - 9/4096 = 3135/262144 > 0.
--
-- Thus the remaining CMP109 same-object task is only to identify the actual
-- selected nonlinear derivative entries with the already-prepared physical
-- reference-entry primitive at radius rho.  No sharper operator estimate is
-- required for the Newton threshold.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; _/_; ∣_∣; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanFourDimensionalHaloOverlapExact as Count
import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact as Fibre
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge
import DASHI.Physics.YangMills.BalabanSelectedBackgroundBlockAverageConstraintMatrixExact as Average
import DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact as Calibration
import DASHI.Physics.YangMills.BalabanSelectedGaugeDerivativeTwoBackgroundVariationExact as GaugeVariation

Row : Set
Row = Average.SelectedBlockAverageRow4

Column : Set
Column = Physical.PhysicalSU2Coordinate4

Matrix : Set
Matrix = Row → Column → ℚ

Vector : Set
Vector = Column → ℚ

rows : List Row
rows = Average.selectedBlockAverageRows4

columns : List Column
columns = Physical.physicalSU2Coordinates4

selectedAverageRowCountExact : length rows ≡ 12
selectedAverageRowCountExact
  rewrite Count.lengthCartesian Physical.lieCoordinates3 Gauge.axes4 = refl

selectedStateColumnCountExact : length columns ≡ 3072
selectedStateColumnCountExact = Calibration.physicalCoordinateCount

rho : ℚ
rho = + 1 / 8192

twoRho : ℚ
twoRho = + 1 / 4096

rowMassBound : ℚ
rowMassBound = + 3 / 4

columnMassBound : ℚ
columnMassBound = + 3 / 1024

blockAverageSchurSquaredCoefficient : ℚ
blockAverageSchurSquaredCoefficient = + 9 / 4096

blockAverageBudgetSlack : ℚ
blockAverageBudgetSlack = + 3135 / 262144

blockAverageCoefficientPlusSlackExact :
  blockAverageSchurSquaredCoefficient + blockAverageBudgetSlack
  ≡ GaugeVariation.blockAverageDerivativeRemainingSquaredBudget
blockAverageCoefficientPlusSlackExact = ℚRing.solve []

blockAverageBudgetSlackNonnegative : 0ℚ ≤ blockAverageBudgetSlack
blockAverageBudgetSlackNonnegative =
  ℚP.nonNegative⁻¹ blockAverageBudgetSlack

absoluteDifferenceBelowTwoRho : ∀ left right →
  ∣ left ∣ ≤ rho →
  ∣ right ∣ ≤ rho →
  ∣ left - right ∣ ≤ twoRho
absoluteDifferenceBelowTwoRho left right leftBound rightBound =
  let
    rewriteDifference : left - right ≡ left + (- right)
    rewriteDifference = ℚRing.solve []

    triangle :
      ∣ left + (- right) ∣ ≤ ∣ left ∣ + ∣ - right ∣
    triangle = ℚP.∣p+q∣≤∣p∣+∣q∣ left (- right)

    removeNeg : ∣ left ∣ + ∣ - right ∣ ≡ ∣ left ∣ + ∣ right ∣
    removeNeg = cong (∣ left ∣ +_) (ℚP.∣-p∣≡∣p∣ right)

    boundedSum : ∣ left ∣ + ∣ right ∣ ≤ rho + rho
    boundedSum = ℚP.+-mono-≤ leftBound rightBound

    toTwoRho : rho + rho ≡ twoRho
    toTwoRho = ℚRing.solve []
  in
  subst
    (λ lower → lower ≤ twoRho)
    (sym (cong ∣_∣ rewriteDifference))
    (ℚP.≤-trans triangle
      (subst
        (λ lower → lower ≤ twoRho)
        (sym removeNeg)
        (subst
          (λ upper → ∣ left ∣ + ∣ right ∣ ≤ upper)
          toTwoRho boundedSum)))

twoBackgroundMatrix : Matrix → Matrix → Matrix
twoBackgroundMatrix leftReferenceDifference rightReferenceDifference row column =
  leftReferenceDifference row column - rightReferenceDifference row column

pointwiseTwoBackgroundEntryBound :
  ∀ leftReferenceDifference rightReferenceDifference →
  (∀ row column → ∣ leftReferenceDifference row column ∣ ≤ rho) →
  (∀ row column → ∣ rightReferenceDifference row column ∣ ≤ rho) →
  ∀ row column →
  ∣ twoBackgroundMatrix leftReferenceDifference rightReferenceDifference row column ∣
  ≤ twoRho
pointwiseTwoBackgroundEntryBound left right leftBound rightBound row column =
  absoluteDifferenceBelowTwoRho
    (left row column) (right row column)
    (leftBound row column) (rightBound row column)

rowMassFromPointwiseTwoRho :
  ∀ matrix →
  (∀ row column → ∣ matrix row column ∣ ≤ twoRho) →
  ∀ row → RectSchur.rectAbsoluteRowMass columns matrix row ≤ rowMassBound
rowMassFromPointwiseTwoRho matrix pointwise row =
  let
    summed = Schur.sumPointwiseBelow columns
      (λ column → ∣ matrix row column ∣)
      (λ _ → twoRho)
      (pointwise row)

    constantExact = Fibre.sumRationalConstant columns twoRho

    countScale :
      Fibre.natAsRational (length columns) * twoRho ≡ rowMassBound
    countScale rewrite selectedStateColumnCountExact = ℚRing.solve []
  in
  subst
    (λ upper → RectSchur.rectAbsoluteRowMass columns matrix row ≤ upper)
    (trans constantExact countScale)
    summed

columnMassFromPointwiseTwoRho :
  ∀ matrix →
  (∀ row column → ∣ matrix row column ∣ ≤ twoRho) →
  ∀ column →
  RectSchur.rectAbsoluteColumnMass rows matrix column ≤ columnMassBound
columnMassFromPointwiseTwoRho matrix pointwise column =
  let
    summed = Schur.sumPointwiseBelow rows
      (λ row → ∣ matrix row column ∣)
      (λ _ → twoRho)
      (λ row → pointwise row column)

    constantExact = Fibre.sumRationalConstant rows twoRho

    countScale :
      Fibre.natAsRational (length rows) * twoRho ≡ columnMassBound
    countScale rewrite selectedAverageRowCountExact = ℚRing.solve []
  in
  subst
    (λ upper → RectSchur.rectAbsoluteColumnMass rows matrix column ≤ upper)
    (trans constantExact countScale)
    summed

selectedBlockAverageTwoBackgroundVariationSchur :
  ∀ leftReferenceDifference rightReferenceDifference vector →
  (∀ row column → ∣ leftReferenceDifference row column ∣ ≤ rho) →
  (∀ row column → ∣ rightReferenceDifference row column ∣ ≤ rho) →
  RectSchur.rectVectorNormSq rows
    (RectSchur.rectApply columns
      (twoBackgroundMatrix leftReferenceDifference rightReferenceDifference)
      vector)
  ≤ blockAverageSchurSquaredCoefficient
      * RectSchur.rectVectorNormSq columns vector
selectedBlockAverageTwoBackgroundVariationSchur left right vector leftBound rightBound =
  let
    matrix = twoBackgroundMatrix left right
    pointwise = pointwiseTwoBackgroundEntryBound left right leftBound rightBound
    schur = RectSchur.finiteRectangularSchurSquared
      rows columns matrix vector rowMassBound columnMassBound
      (ℚP.nonNegative⁻¹ rowMassBound)
      (ℚP.nonNegative⁻¹ columnMassBound)
      (rowMassFromPointwiseTwoRho matrix pointwise)
      (columnMassFromPointwiseTwoRho matrix pointwise)

    coefficientExact : rowMassBound * columnMassBound
      ≡ blockAverageSchurSquaredCoefficient
    coefficientExact = ℚRing.solve []
  in
  subst
    (λ coefficient →
      RectSchur.rectVectorNormSq rows
        (RectSchur.rectApply columns matrix vector)
      ≤ coefficient * RectSchur.rectVectorNormSq columns vector)
    coefficientExact schur

selectedBlockAverageTwoBackgroundFitsIFTBudget :
  ∀ leftReferenceDifference rightReferenceDifference vector →
  (∀ row column → ∣ leftReferenceDifference row column ∣ ≤ rho) →
  (∀ row column → ∣ rightReferenceDifference row column ∣ ≤ rho) →
  RectSchur.rectVectorNormSq rows
    (RectSchur.rectApply columns
      (twoBackgroundMatrix leftReferenceDifference rightReferenceDifference)
      vector)
  ≤ GaugeVariation.blockAverageDerivativeRemainingSquaredBudget
      * RectSchur.rectVectorNormSq columns vector
selectedBlockAverageTwoBackgroundFitsIFTBudget left right vector leftBound rightBound =
  let
    base = selectedBlockAverageTwoBackgroundVariationSchur
      left right vector leftBound rightBound
    norm = RectSchur.rectVectorNormSq columns vector
    normNonnegative =
      Schur.sumNonnegative columns _
        (λ column → FiniteL2.squareNonnegative (vector column))

    coefficientBelow :
      blockAverageSchurSquaredCoefficient
      ≤ GaugeVariation.blockAverageDerivativeRemainingSquaredBudget
    coefficientBelow =
      subst
        (λ upper → blockAverageSchurSquaredCoefficient ≤ upper)
        blockAverageCoefficientPlusSlackExact
        (subst
          (λ lower → lower
            ≤ blockAverageSchurSquaredCoefficient + blockAverageBudgetSlack)
          (sym (ℚP.+-identityʳ blockAverageSchurSquaredCoefficient))
          (ℚP.+-mono-≤ ℚP.≤-refl blockAverageBudgetSlackNonnegative))

    instance
      normNN : NonNegative norm
      normNN = ℚ.nonNegative normNonnegative
  in
  ℚP.≤-trans base
    (ℚP.*-monoʳ-≤-nonNeg norm coefficientBelow)

selectedBlockAverageReferenceEntryToSchurLevel : ProofLevel
selectedBlockAverageReferenceEntryToSchurLevel = machineChecked

selectedBlockAverageTwoBackgroundIFTBudgetLevel : ProofLevel
selectedBlockAverageTwoBackgroundIFTBudgetLevel = machineChecked

physicalCMP109SelectedReferenceEntryIdentificationLevel : ProofLevel
physicalCMP109SelectedReferenceEntryIdentificationLevel = conditional
