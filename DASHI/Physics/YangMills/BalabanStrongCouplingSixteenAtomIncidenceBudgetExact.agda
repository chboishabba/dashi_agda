module DASHI.Physics.YangMills.BalabanStrongCouplingSixteenAtomIncidenceBudgetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
-- arXiv:2204.12737.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks".
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Balaban,
-- "Propagators for Lattice Gauge Theories in a Background Field".
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Derive the source coefficient 8(d-1), rather than recording it as a free
-- constant.  The literal ordered four-link Hessian carrier already contains
-- exactly four diagonal second-derivative placements and twelve ordered cross
-- placements.  Give a diagonal placement at slot i the local budget n_i and an
-- ordered cross placement (i,j) the square-root-free Young budget
--
--                    (n_i+n_j)/2.
--
-- Summing the actual sixteen-constructor enumeration gives exactly
--
--                  4 (n_0+n_1+n_2+n_3).
--
-- Every oriented edge lies in 2(d-1) plaquettes.  Hence the global coefficient
-- is produced by literal placement and incidence counting:
--
--                  4 * 2(d-1) = 8(d-1).
--
-- In d=4 this is 24, split as 6 from the diagonal channel and 18 from the
-- ordered-cross channel.  The remaining analytic obligation is the concrete
-- quaternion scalar estimate showing that each named atom is below its stated
-- local Young budget; the combinatorial coefficient itself is now closed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.YangMills.BalabanP33WilsonPlaquetteSecondVariationPlacementsExact as Placement

sumRational : List ℚ → ℚ
sumRational [] = 0ℚ
sumRational (value ∷ values) = value + sumRational values

diagonalPlacements4 : List Placement.PlaquetteSecondVariationPlacement4
diagonalPlacements4 =
  Placement.secondAt0 ∷ Placement.secondAt1 ∷
  Placement.secondAt2 ∷ Placement.secondAt3 ∷ []

orderedCrossPlacements4 : List Placement.PlaquetteSecondVariationPlacement4
orderedCrossPlacements4 =
  Placement.firstFirst Placement.ordered01 ∷
  Placement.firstFirst Placement.ordered10 ∷
  Placement.firstFirst Placement.ordered02 ∷
  Placement.firstFirst Placement.ordered20 ∷
  Placement.firstFirst Placement.ordered03 ∷
  Placement.firstFirst Placement.ordered30 ∷
  Placement.firstFirst Placement.ordered12 ∷
  Placement.firstFirst Placement.ordered21 ∷
  Placement.firstFirst Placement.ordered13 ∷
  Placement.firstFirst Placement.ordered31 ∷
  Placement.firstFirst Placement.ordered23 ∷
  Placement.firstFirst Placement.ordered32 ∷ []

placementYoungBudget :
  Placement.PlaquetteSecondVariationPlacement4 →
  ℚ → ℚ → ℚ → ℚ → ℚ
placementYoungBudget Placement.secondAt0 n0 n1 n2 n3 = n0
placementYoungBudget Placement.secondAt1 n0 n1 n2 n3 = n1
placementYoungBudget Placement.secondAt2 n0 n1 n2 n3 = n2
placementYoungBudget Placement.secondAt3 n0 n1 n2 n3 = n3
placementYoungBudget
    (Placement.firstFirst Placement.ordered01) n0 n1 n2 n3 =
  (+ 1 / 2) * (n0 + n1)
placementYoungBudget
    (Placement.firstFirst Placement.ordered10) n0 n1 n2 n3 =
  (+ 1 / 2) * (n1 + n0)
placementYoungBudget
    (Placement.firstFirst Placement.ordered02) n0 n1 n2 n3 =
  (+ 1 / 2) * (n0 + n2)
placementYoungBudget
    (Placement.firstFirst Placement.ordered20) n0 n1 n2 n3 =
  (+ 1 / 2) * (n2 + n0)
placementYoungBudget
    (Placement.firstFirst Placement.ordered03) n0 n1 n2 n3 =
  (+ 1 / 2) * (n0 + n3)
placementYoungBudget
    (Placement.firstFirst Placement.ordered30) n0 n1 n2 n3 =
  (+ 1 / 2) * (n3 + n0)
placementYoungBudget
    (Placement.firstFirst Placement.ordered12) n0 n1 n2 n3 =
  (+ 1 / 2) * (n1 + n2)
placementYoungBudget
    (Placement.firstFirst Placement.ordered21) n0 n1 n2 n3 =
  (+ 1 / 2) * (n2 + n1)
placementYoungBudget
    (Placement.firstFirst Placement.ordered13) n0 n1 n2 n3 =
  (+ 1 / 2) * (n1 + n3)
placementYoungBudget
    (Placement.firstFirst Placement.ordered31) n0 n1 n2 n3 =
  (+ 1 / 2) * (n3 + n1)
placementYoungBudget
    (Placement.firstFirst Placement.ordered23) n0 n1 n2 n3 =
  (+ 1 / 2) * (n2 + n3)
placementYoungBudget
    (Placement.firstFirst Placement.ordered32) n0 n1 n2 n3 =
  (+ 1 / 2) * (n3 + n2)

diagonalPlacementBudget : ℚ → ℚ → ℚ → ℚ → ℚ
diagonalPlacementBudget n0 n1 n2 n3 =
  sumRational
    (map (λ placement → placementYoungBudget placement n0 n1 n2 n3)
      diagonalPlacements4)

orderedCrossPlacementBudget : ℚ → ℚ → ℚ → ℚ → ℚ
orderedCrossPlacementBudget n0 n1 n2 n3 =
  sumRational
    (map (λ placement → placementYoungBudget placement n0 n1 n2 n3)
      orderedCrossPlacements4)

allPlacementBudget : ℚ → ℚ → ℚ → ℚ → ℚ
allPlacementBudget n0 n1 n2 n3 =
  sumRational
    (map (λ placement → placementYoungBudget placement n0 n1 n2 n3)
      Placement.plaquetteSecondVariationPlacements4)

localInsertionCharge : ℚ → ℚ → ℚ → ℚ → ℚ
localInsertionCharge n0 n1 n2 n3 = n0 + n1 + n2 + n3

diagonalPlacementBudgetExact :
  ∀ n0 n1 n2 n3 →
  diagonalPlacementBudget n0 n1 n2 n3
  ≡ localInsertionCharge n0 n1 n2 n3
diagonalPlacementBudgetExact n0 n1 n2 n3 =
  solve (n0 ∷ n1 ∷ n2 ∷ n3 ∷ [])

orderedCrossPlacementBudgetExact :
  ∀ n0 n1 n2 n3 →
  orderedCrossPlacementBudget n0 n1 n2 n3
  ≡ (+ 3 / 1) * localInsertionCharge n0 n1 n2 n3
orderedCrossPlacementBudgetExact n0 n1 n2 n3 =
  solve (n0 ∷ n1 ∷ n2 ∷ n3 ∷ [])

sixteenPlacementBudgetExact :
  ∀ n0 n1 n2 n3 →
  allPlacementBudget n0 n1 n2 n3
  ≡ (+ 4 / 1) * localInsertionCharge n0 n1 n2 n3
sixteenPlacementBudgetExact n0 n1 n2 n3 =
  solve (n0 ∷ n1 ∷ n2 ∷ n3 ∷ [])

plaquettesPerOrientedEdge : ℚ → ℚ
plaquettesPerOrientedEdge dMinusOne = (+ 2 / 1) * dMinusOne

globalDiagonalIncidenceCoefficient : ℚ → ℚ
globalDiagonalIncidenceCoefficient dMinusOne =
  plaquettesPerOrientedEdge dMinusOne

globalCrossIncidenceCoefficient : ℚ → ℚ
globalCrossIncidenceCoefficient dMinusOne =
  (+ 3 / 1) * plaquettesPerOrientedEdge dMinusOne

globalSixteenAtomIncidenceCoefficient : ℚ → ℚ
globalSixteenAtomIncidenceCoefficient dMinusOne =
  (+ 4 / 1) * plaquettesPerOrientedEdge dMinusOne

globalDiagonalCoefficientExact :
  ∀ dMinusOne →
  globalDiagonalIncidenceCoefficient dMinusOne
  ≡ (+ 2 / 1) * dMinusOne
globalDiagonalCoefficientExact dMinusOne = solve (dMinusOne ∷ [])

globalCrossCoefficientExact :
  ∀ dMinusOne →
  globalCrossIncidenceCoefficient dMinusOne
  ≡ (+ 6 / 1) * dMinusOne
globalCrossCoefficientExact dMinusOne = solve (dMinusOne ∷ [])

globalSixteenAtomCoefficientExact :
  ∀ dMinusOne →
  globalSixteenAtomIncidenceCoefficient dMinusOne
  ≡ (+ 8 / 1) * dMinusOne
globalSixteenAtomCoefficientExact dMinusOne = solve (dMinusOne ∷ [])

fourDimensionalDMinusOne : ℚ
fourDimensionalDMinusOne = + 3 / 1

fourDimensionalDiagonalCoefficientExact :
  globalDiagonalIncidenceCoefficient fourDimensionalDMinusOne
  ≡ + 6 / 1
fourDimensionalDiagonalCoefficientExact = solve []

fourDimensionalCrossCoefficientExact :
  globalCrossIncidenceCoefficient fourDimensionalDMinusOne
  ≡ + 18 / 1
fourDimensionalCrossCoefficientExact = solve []

fourDimensionalTotalCoefficientExact :
  globalSixteenAtomIncidenceCoefficient fourDimensionalDMinusOne
  ≡ + 24 / 1
fourDimensionalTotalCoefficientExact = solve []

fourDimensionalDiagonalPlusCrossExact :
  globalDiagonalIncidenceCoefficient fourDimensionalDMinusOne
    + globalCrossIncidenceCoefficient fourDimensionalDMinusOne
  ≡ globalSixteenAtomIncidenceCoefficient fourDimensionalDMinusOne
fourDimensionalDiagonalPlusCrossExact = solve []
