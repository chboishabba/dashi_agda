module DASHI.Physics.Closure.NSTriadKNFixedOutputPairDifferenceDebtExact where

------------------------------------------------------------------------
-- FIXED-OUTPUT GRAM DEBT = TOTAL MASS MINUS COMPLETE-GRAPH DIFFERENCE MASS
--
-- Cross-lane donor:
--   DASHI.Physics.YangMills.BalabanFiniteRationalCauchyExact
-- proves for every finite rational list xs
--
--   |xs| * sumSquares xs - square (sum xs)
--     = pairDifferenceEnergy xs.
--
-- The rational Complex3 norm is literally the sum of six rational coordinate
-- squares.  Applying the scalar identity coordinatewise therefore gives
--
--   ||sum_i B_i||^2 + PairDiffMass(B) = n * sum_i ||B_i||^2.
--
-- R207 already proves on one literal physical output fibre
--
--   ||sum_i B_i||^2 = cellMass + fixedOutputBetweenPartnerDebt.
--
-- Combining the two exact identities yields
--
--   fixedOutputBetweenPartnerDebt + PairDiffMass
--     = (n - 1) * cellMass.
--
-- This owner is finite algebra only.  It introduces no PDE estimate, no new
-- residual/payment socket, no positivity assumption, no shell count and no
-- cutoff/spacetime claim.  The next analytic problem is LOWER control of the
-- literal pair-difference mass, not another upper Cauchy estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Physics.YangMills.BalabanFiniteRationalCauchyExact as YM
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as YMSums

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNComparableFixedOutputCarrierRound207Exact as R207

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- 1. Six scalar coordinates of the rational Complex3 carrier.
------------------------------------------------------------------------

xReal xImag yReal yImag zReal zImag : C3.Complex3 F → ℚ
xReal v = C3.real (C3.x v)
xImag v = C3.imaginary (C3.x v)
yReal v = C3.real (C3.y v)
yImag v = C3.imaginary (C3.y v)
zReal v = C3.real (C3.z v)
zImag v = C3.imaginary (C3.z v)

coordinateList : (C3.Complex3 F → ℚ) → List (C3.Complex3 F) → List ℚ
coordinateList coordinate [] = []
coordinateList coordinate (v ∷ vs) = coordinate v ∷ coordinateList coordinate vs

coordinateSum : (C3.Complex3 F → ℚ) → List (C3.Complex3 F) → ℚ
coordinateSum coordinate cells =
  YMSums.sumRational (coordinateList coordinate cells) (λ value → value)

------------------------------------------------------------------------
-- 2. Complete-graph pair-difference mass on Complex3.
------------------------------------------------------------------------

pairDifferenceMass3 : List (C3.Complex3 F) → ℚ
pairDifferenceMass3 cells =
  YM.pairDifferenceEnergy (coordinateList xReal cells)
  + YM.pairDifferenceEnergy (coordinateList xImag cells)
  + YM.pairDifferenceEnergy (coordinateList yReal cells)
  + YM.pairDifferenceEnergy (coordinateList yImag cells)
  + YM.pairDifferenceEnergy (coordinateList zReal cells)
  + YM.pairDifferenceEnergy (coordinateList zImag cells)

coordinateSquareMass3 : List (C3.Complex3 F) → ℚ
coordinateSquareMass3 cells =
  YM.sumSquares (coordinateList xReal cells)
  + YM.sumSquares (coordinateList xImag cells)
  + YM.sumSquares (coordinateList yReal cells)
  + YM.sumSquares (coordinateList yImag cells)
  + YM.sumSquares (coordinateList zReal cells)
  + YM.sumSquares (coordinateList zImag cells)

coordinateSumSquare3 : List (C3.Complex3 F) → ℚ
coordinateSumSquare3 cells =
  coordinateSum xReal cells * coordinateSum xReal cells
  + coordinateSum xImag cells * coordinateSum xImag cells
  + coordinateSum yReal cells * coordinateSum yReal cells
  + coordinateSum yImag cells * coordinateSum yImag cells
  + coordinateSum zReal cells * coordinateSum zReal cells
  + coordinateSum zImag cells * coordinateSum zImag cells

------------------------------------------------------------------------
-- 3. Coordinate bookkeeping for the literal NS list folds.
------------------------------------------------------------------------

sumCellsXReal : ∀ cells →
  xReal (R180.sumCells cells) ≡ coordinateSum xReal cells
sumCellsXReal [] = refl
sumCellsXReal (v ∷ vs) rewrite sumCellsXReal vs = refl

sumCellsXImag : ∀ cells →
  xImag (R180.sumCells cells) ≡ coordinateSum xImag cells
sumCellsXImag [] = refl
sumCellsXImag (v ∷ vs) rewrite sumCellsXImag vs = refl

sumCellsYReal : ∀ cells →
  yReal (R180.sumCells cells) ≡ coordinateSum yReal cells
sumCellsYReal [] = refl
sumCellsYReal (v ∷ vs) rewrite sumCellsYReal vs = refl

sumCellsYImag : ∀ cells →
  yImag (R180.sumCells cells) ≡ coordinateSum yImag cells
sumCellsYImag [] = refl
sumCellsYImag (v ∷ vs) rewrite sumCellsYImag vs = refl

sumCellsZReal : ∀ cells →
  zReal (R180.sumCells cells) ≡ coordinateSum zReal cells
sumCellsZReal [] = refl
sumCellsZReal (v ∷ vs) rewrite sumCellsZReal vs = refl

sumCellsZImag : ∀ cells →
  zImag (R180.sumCells cells) ≡ coordinateSum zImag cells
sumCellsZImag [] = refl
sumCellsZImag (v ∷ vs) rewrite sumCellsZImag vs = refl

sumCellsNormIsCoordinateSumSquares : ∀ cells →
  L2.complex3NormSquared (R180.sumCells cells)
  ≡ coordinateSumSquare3 cells
sumCellsNormIsCoordinateSumSquares cells
  rewrite sumCellsXReal cells
        | sumCellsXImag cells
        | sumCellsYReal cells
        | sumCellsYImag cells
        | sumCellsZReal cells
        | sumCellsZImag cells =
  solve
    ( coordinateSum xReal cells
    ∷ coordinateSum xImag cells
    ∷ coordinateSum yReal cells
    ∷ coordinateSum yImag cells
    ∷ coordinateSum zReal cells
    ∷ coordinateSum zImag cells
    ∷ [])

cellMassSumIsCoordinateSquareMass : ∀ cells →
  R180.cellMassSum cells ≡ coordinateSquareMass3 cells
cellMassSumIsCoordinateSquareMass [] = refl
cellMassSumIsCoordinateSquareMass
    (C3.complex3
      (C3.complex xr xi)
      (C3.complex yr yi)
      (C3.complex zr zi) ∷ rest)
  rewrite cellMassSumIsCoordinateSquareMass rest =
  solve
    ( xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi
    ∷ YM.sumSquares (coordinateList xReal rest)
    ∷ YM.sumSquares (coordinateList xImag rest)
    ∷ YM.sumSquares (coordinateList yReal rest)
    ∷ YM.sumSquares (coordinateList yImag rest)
    ∷ YM.sumSquares (coordinateList zReal rest)
    ∷ YM.sumSquares (coordinateList zImag rest)
    ∷ [])

------------------------------------------------------------------------
-- 4. Coordinatewise lift of the YM complete-graph identity.
------------------------------------------------------------------------

pairDifferenceMass3ClosedForm : ∀ cells →
  pairDifferenceMass3 cells
  ≡ YMSums.natAsRational (length cells) * R180.cellMassSum cells
      - L2.complex3NormSquared (R180.sumCells cells)
pairDifferenceMass3ClosedForm cells
  rewrite sym (YM.pairDifferenceIdentity (coordinateList xReal cells))
        | sym (YM.pairDifferenceIdentity (coordinateList xImag cells))
        | sym (YM.pairDifferenceIdentity (coordinateList yReal cells))
        | sym (YM.pairDifferenceIdentity (coordinateList yImag cells))
        | sym (YM.pairDifferenceIdentity (coordinateList zReal cells))
        | sym (YM.pairDifferenceIdentity (coordinateList zImag cells))
        | cellMassSumIsCoordinateSquareMass cells
        | sumCellsNormIsCoordinateSumSquares cells =
  solve
    ( YMSums.natAsRational (length cells)
    ∷ YM.sumSquares (coordinateList xReal cells)
    ∷ YM.sumSquares (coordinateList xImag cells)
    ∷ YM.sumSquares (coordinateList yReal cells)
    ∷ YM.sumSquares (coordinateList yImag cells)
    ∷ YM.sumSquares (coordinateList zReal cells)
    ∷ YM.sumSquares (coordinateList zImag cells)
    ∷ coordinateSum xReal cells
    ∷ coordinateSum xImag cells
    ∷ coordinateSum yReal cells
    ∷ coordinateSum yImag cells
    ∷ coordinateSum zReal cells
    ∷ coordinateSum zImag cells
    ∷ [])

finiteComplex3PairDifferenceIdentity : ∀ cells →
  L2.complex3NormSquared (R180.sumCells cells)
    + pairDifferenceMass3 cells
  ≡ YMSums.natAsRational (length cells) * R180.cellMassSum cells
finiteComplex3PairDifferenceIdentity cells
  rewrite pairDifferenceMass3ClosedForm cells =
  solve
    ( L2.complex3NormSquared (R180.sumCells cells)
    ∷ YMSums.natAsRational (length cells)
    ∷ R180.cellMassSum cells
    ∷ [])

------------------------------------------------------------------------
-- 5. Literal R207 fixed-output specialization.
------------------------------------------------------------------------

fixedOutputPairDifferenceMass :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode} →
  List (R207.FixedOutputLocalizedComparablePartner system output) → ℚ
fixedOutputPairDifferenceMass entries =
  pairDifferenceMass3 (R207.fixedOutputPartnerCells entries)

fixedOutputDebtPlusPairDifference :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode}
    (entries : List (R207.FixedOutputLocalizedComparablePartner system output)) →
  R207.fixedOutputBetweenPartnerDebt entries
    + fixedOutputPairDifferenceMass entries
  ≡ (YMSums.natAsRational (length (R207.fixedOutputPartnerCells entries)) - 1ℚ)
      * R180.cellMassSum (R207.fixedOutputPartnerCells entries)
fixedOutputDebtPlusPairDifference entries
  rewrite pairDifferenceMass3ClosedForm (R207.fixedOutputPartnerCells entries)
        | R207.fixedOutputCompressedGramLedger entries =
  solve
    ( YMSums.natAsRational (length (R207.fixedOutputPartnerCells entries))
    ∷ R180.cellMassSum (R207.fixedOutputPartnerCells entries)
    ∷ R207.fixedOutputBetweenPartnerDebt entries
    ∷ [])

fixedOutputDebtClosedForm :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode}
    (entries : List (R207.FixedOutputLocalizedComparablePartner system output)) →
  R207.fixedOutputBetweenPartnerDebt entries
  ≡ (YMSums.natAsRational (length (R207.fixedOutputPartnerCells entries)) - 1ℚ)
      * R180.cellMassSum (R207.fixedOutputPartnerCells entries)
      - fixedOutputPairDifferenceMass entries
fixedOutputDebtClosedForm entries
  rewrite fixedOutputDebtPlusPairDifference entries =
  solve
    ( R207.fixedOutputBetweenPartnerDebt entries
    ∷ fixedOutputPairDifferenceMass entries
    ∷ YMSums.natAsRational (length (R207.fixedOutputPartnerCells entries))
    ∷ R180.cellMassSum (R207.fixedOutputPartnerCells entries)
    ∷ [])

------------------------------------------------------------------------
-- Status: finite algebra closed; physical lower pair-difference payment open.
------------------------------------------------------------------------

fixedOutputPairDifferenceAlgebraClosed : Bool
fixedOutputPairDifferenceAlgebraClosed = true

fixedOutputPairDifferenceUsesBalabanIdentity : Bool
fixedOutputPairDifferenceUsesBalabanIdentity = true

fixedOutputPairDifferencePhysicalLowerBoundClosed : Bool
fixedOutputPairDifferencePhysicalLowerBoundClosed = false

fixedOutputPairDifferenceClayPromotion : Bool
fixedOutputPairDifferenceClayPromotion = false

fixedOutputPairDifferenceAlgebraClosedIsTrue :
  fixedOutputPairDifferenceAlgebraClosed ≡ true
fixedOutputPairDifferenceAlgebraClosedIsTrue = refl

fixedOutputPairDifferencePhysicalLowerBoundClosedIsFalse :
  fixedOutputPairDifferencePhysicalLowerBoundClosed ≡ false
fixedOutputPairDifferencePhysicalLowerBoundClosedIsFalse = refl

fixedOutputPairDifferenceClayPromotionIsFalse :
  fixedOutputPairDifferenceClayPromotion ≡ false
fixedOutputPairDifferenceClayPromotionIsFalse = refl
