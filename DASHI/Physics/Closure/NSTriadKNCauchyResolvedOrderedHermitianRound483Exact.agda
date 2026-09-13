module DASHI.Physics.Closure.NSTriadKNCauchyResolvedOrderedHermitianRound483Exact where

------------------------------------------------------------------------
-- ROUND483 / ORDERED FULL CAUCHY SUM = R446 HERMITIAN FORM
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNRationalCauchySchurComplementRound443Exact as R443
import DASHI.Physics.Closure.NSTriadKNRationalComplex3CauchyPSDRound446Exact as R446
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact as R287
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedGramOperatorRound477Exact as R477
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedPositiveCellCarrierRound482Exact as R482

PositiveCell : Set
PositiveCell = R446.PositiveRateComplex3Cell

pairTerm : PositiveCell → PositiveCell → ℚ
pairTerm left right =
  R446.cauchyKernel left right
    * R179.realHermitianCross (R446.value left) (R446.value right)

pairTermSymmetric :
  (left right : PositiveCell) → pairTerm left right ≡ pairTerm right left
pairTermSymmetric left right =
  cong₂ _*_
    (R443.cauchyEntrySymmetric (R446.rate left) (R446.rate right))
    (R287.realHermitianCrossSymmetric (R446.value left) (R446.value right))

columnSum : List PositiveCell → PositiveCell → ℚ
columnSum [] head = 0ℚ
columnSum (cell ∷ rest) head = pairTerm cell head + columnSum rest head

columnSumIsHermitianRowBySymmetry :
  (head : PositiveCell) →
  (rest : List PositiveCell) →
  columnSum rest head ≡ R446.hermitianRow head rest
columnSumIsHermitianRowBySymmetry head [] = refl
columnSumIsHermitianRowBySymmetry head (cell ∷ rest) =
  cong₂ _+_
    (pairTermSymmetric cell head)
    (columnSumIsHermitianRowBySymmetry head rest)

hermitianRowPrepend :
  (rowHead prepend : PositiveCell) →
  (rest : List PositiveCell) →
  R446.hermitianRow rowHead (prepend ∷ rest)
  ≡ pairTerm rowHead prepend + R446.hermitianRow rowHead rest
hermitianRowPrepend rowHead prepend rest = refl

orderedRowsSplitPrependedColumn :
  (prepend : PositiveCell) →
  (rest items : List PositiveCell) →
  R482.orderedHermitianRows (prepend ∷ rest) items
  ≡ columnSum items prepend + R482.orderedHermitianRows rest items
orderedRowsSplitPrependedColumn prepend rest [] = refl
orderedRowsSplitPrependedColumn prepend rest (cell ∷ items) =
  let
    rowSplit = hermitianRowPrepend cell prepend rest
    tailSplit = orderedRowsSplitPrependedColumn prepend rest items
    a = pairTerm cell prepend
    b = R446.hermitianRow cell rest
    c = columnSum items prepend
    d = R482.orderedHermitianRows rest items
  in
  trans
    (cong₂ _+_ rowSplit tailSplit)
    (solve (a ∷ b ∷ c ∷ d ∷ []))

orderedTailRowsSplit :
  (head : PositiveCell) →
  (rest : List PositiveCell) →
  R482.orderedHermitianRows (head ∷ rest) rest
  ≡ R446.hermitianRow head rest + R482.orderedHermitianRows rest rest
orderedTailRowsSplit head rest =
  trans
    (orderedRowsSplitPrependedColumn head rest rest)
    (cong₂ _+_ (columnSumIsHermitianRowBySymmetry head rest) refl)

orderedFullRowsEqualHermitianCauchyForm :
  (cells : List PositiveCell) →
  R482.orderedHermitianRows cells cells ≡ R446.hermitianCauchyForm cells
orderedFullRowsEqualHermitianCauchyForm [] = refl
orderedFullRowsEqualHermitianCauchyForm (head ∷ rest)
  rewrite orderedTailRowsSplit head rest
        | orderedFullRowsEqualHermitianCauchyForm rest =
  solve
    ( R446.cauchyKernel head head
    ∷ R179.realHermitianCross (R446.value head) (R446.value head)
    ∷ R446.hermitianRow head rest
    ∷ R446.hermitianCauchyForm rest
    ∷ [])

resolvedQuadraticAtSelectedCoefficientIsR446HermitianCauchyForm :
  (cells : List PositiveCell) →
  R477.resolvedQuadratic
    (R482.positiveCellResolvedFamily cells)
    R482.selectedCoefficient
  ≡ R446.hermitianCauchyForm cells
resolvedQuadraticAtSelectedCoefficientIsR446HermitianCauchyForm cells =
  trans
    (R482.resolvedQuadraticAtSelectedCoefficientIsOrderedHermitianRows cells)
    (orderedFullRowsEqualHermitianCauchyForm cells)

round483FiniteSymmetryBookkeepingClosed : Bool
round483FiniteSymmetryBookkeepingClosed = true

round483OrderedFullRowsMatchR446HermitianCauchyForm : Bool
round483OrderedFullRowsMatchR446HermitianCauchyForm = true

round483SelectedR477QuadraticMatchesR446HermitianCauchyForm : Bool
round483SelectedR477QuadraticMatchesR446HermitianCauchyForm = true

round483IntroducesAnalyticEstimate : Bool
round483IntroducesAnalyticEstimate = false

round483R480SnapshotWeldClosed : Bool
round483R480SnapshotWeldClosed = false

round483ClayPromotion : Bool
round483ClayPromotion = false

round483IntroducesAnalyticEstimateIsFalse :
  round483IntroducesAnalyticEstimate ≡ false
round483IntroducesAnalyticEstimateIsFalse = refl

round483R480SnapshotWeldClosedIsFalse :
  round483R480SnapshotWeldClosed ≡ false
round483R480SnapshotWeldClosedIsFalse = refl
