module DASHI.Physics.YangMills.BalabanP33WilsonPairDeepBudgetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- DASHI CONTRIBUTION
--
-- Determine the only budget-compatible split of the exact four-factor subset
-- expansion at the configured radius.  Write epsilon = 2 rho, so a selected
-- factor defect has norm scale epsilon.  Per named placement there are
--
--   six pair terms:          6 epsilon^2,
--   four triple + quartic:   4 epsilon^3 + epsilon^4.
--
-- The sixteen placement Young budgets sum to four times the local diagonal
-- charge.  Hence the cubic--quartic channel costs
--
--   4 (4 epsilon^3 + epsilon^4)
--     = 16 epsilon^3 + 4 epsilon^4
--     = 128 rho^3 + 64 rho^4,
--
-- which lies strictly below rho/144.  By contrast charging all pair terms to
-- the same channel costs 24 epsilon^2 = 96 rho^2, strictly above rho/144.
-- The quadratic terms must therefore be retained in the correlated channel.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeSignedLowerExact as Signed
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson

rho epsilon : ℚ
rho = Signed.rho
epsilon = (+ 2 / 1) * rho

pairPlacementCoefficient : ℚ
pairPlacementCoefficient = (+ 6 / 1) * (epsilon * epsilon)

deepPlacementCoefficient : ℚ
deepPlacementCoefficient =
  (+ 4 / 1) * (epsilon * epsilon * epsilon)
  + epsilon * epsilon * epsilon * epsilon

allPlacementPairCoefficient : ℚ
allPlacementPairCoefficient = (+ 4 / 1) * pairPlacementCoefficient

allPlacementDeepCoefficient : ℚ
allPlacementDeepCoefficient = (+ 4 / 1) * deepPlacementCoefficient

pairCoefficientExact :
  allPlacementPairCoefficient ≡ + 3 / 2097152
pairCoefficientExact = ℚRing.solve []

deepCoefficientExact :
  allPlacementDeepCoefficient ≡ + 16385 / 70368744177664
deepCoefficientExact = ℚRing.solve []

diagonalTargetCoefficient : ℚ
diagonalTargetCoefficient = Wilson.rhoOverOneFortyFour

correlatedTargetPerDiagonalCharge : ℚ
correlatedTargetPerDiagonalCharge = (+ 3 / 1) * Wilson.rhoOverThirtySix

deepSlack : ℚ
deepSlack =
  + 536723447 / 633318697598976

deepSlackPositive : 0ℚ < deepSlack
deepSlackPositive = ℚP.positive⁻¹ deepSlack

deepCoefficientPlusSlackIsDiagonalTarget :
  allPlacementDeepCoefficient + deepSlack
  ≡ diagonalTargetCoefficient
deepCoefficientPlusSlackIsDiagonalTarget = ℚRing.solve []

deepCoefficientBelowDiagonalTarget :
  allPlacementDeepCoefficient ≤ diagonalTargetCoefficient
deepCoefficientBelowDiagonalTarget =
  subst
    (λ upper → allPlacementDeepCoefficient ≤ upper)
    deepCoefficientPlusSlackIsDiagonalTarget
    (subst
      (λ lower → lower ≤ allPlacementDeepCoefficient + deepSlack)
      (ℚP.+-identityʳ allPlacementDeepCoefficient)
      (ℚP.+-mono-≤ ℚP.≤-refl
        (ℚP.<⇒≤ deepSlackPositive)))

pairExcessOverDiagonalTarget : ℚ
pairExcessOverDiagonalTarget =
  + 11 / 18874368

pairExcessPositive : 0ℚ < pairExcessOverDiagonalTarget
pairExcessPositive = ℚP.positive⁻¹ pairExcessOverDiagonalTarget

diagonalTargetPlusPairExcessIsPairCoefficient :
  diagonalTargetCoefficient + pairExcessOverDiagonalTarget
  ≡ allPlacementPairCoefficient
diagonalTargetPlusPairExcessIsPairCoefficient = ℚRing.solve []

pairCoefficientPerCrossCharge : ℚ
pairCoefficientPerCrossCharge =
  (+ 1 / 3) * allPlacementPairCoefficient

pairPerCrossExact :
  pairCoefficientPerCrossCharge ≡ rho * (+ 1 / 256)
pairPerCrossExact = ℚRing.solve []

remainingCorrelatedCoefficient : ℚ
remainingCorrelatedCoefficient =
  Wilson.rhoOverThirtySix - pairCoefficientPerCrossCharge

remainingCorrelatedCoefficientExact :
  remainingCorrelatedCoefficient ≡ + 55 / 18874368
remainingCorrelatedCoefficientExact = ℚRing.solve []

remainingCorrelatedCoefficientPositive :
  0ℚ < remainingCorrelatedCoefficient
remainingCorrelatedCoefficientPositive =
  ℚP.positive⁻¹ remainingCorrelatedCoefficient
