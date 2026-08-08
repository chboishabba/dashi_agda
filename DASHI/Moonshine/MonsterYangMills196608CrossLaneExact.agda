module DASHI.Moonshine.MonsterYangMills196608CrossLaneExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks",
-- Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Balaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Igor B. Frenkel, James Lepowsky and Arne Meurman,
-- "Vertex Operator Algebras and the Monster",
-- Pure and Applied Mathematics 134, Academic Press, 1988.
-- ISBN: 978-0-12-267065-7.  No DOI asserted here.
--
-- DASHI CONTRIBUTION
--
-- This module makes the cross-lane overlap refer to the actual repository
-- objects rather than to two independently retyped numerals.
--
-- Yang--Mills owns
--
--   rho = 1/8192,
--   epsilon_W = rho * 13/24 = 13/196608.
--
-- The Leech weight-two coordinate chart owns
--
--   196608 = 196560 + 24 + 24,
--   196884 = 196608 + C(24,2).
--
-- Hence the same integer is simultaneously the reduced denominator of the
-- sharp Wilson budget and a natural basis-coordinate subtotal of the Leech
-- lattice VOA weight-two space.  This is a real shared arithmetic object,
-- not merely hexadecimal proximity.  No dynamical or representation-
-- theoretic selection mechanism between the two theories is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Physics.YangMills.BalabanP33WilsonSharpDuhamelBudgetExact as Wilson
import DASHI.Moonshine.LeechWeightTwo196608BridgeExact as Leech

commonDenominator : Nat
commonDenominator = 196608

commonDenominatorIsTwentyFourTimesRadiusDenominator :
  commonDenominator ≡ 24 * 8192
commonDenominatorIsTwentyFourTimesRadiusDenominator = refl

commonDenominatorIsThreeTimesTwoPowerSixteen :
  commonDenominator ≡ 3 * 65536
commonDenominatorIsThreeTimesTwoPowerSixteen = refl

leechSubtotalIsCommonDenominator :
  Leech.leechCoordinateSubtotal ≡ commonDenominator
leechSubtotalIsCommonDenominator = refl

sharpWilsonBudgetUsesCommonDenominator :
  Wilson.sharpSixteenAtomBudget ≡ + 13 / 196608
sharpWilsonBudgetUsesCommonDenominator = ℚRing.solve []

radiusTimesTwentyFourUsesCommonDenominator :
  Wilson.rho * (+ 1 / 24) ≡ + 1 / 196608
radiusTimesTwentyFourUsesCommonDenominator = ℚRing.solve []

moonshineCompletionOverCommonDenominator :
  commonDenominator + Leech.offDiagonalQuadraticCount
  ≡ Leech.leechWeightTwoDimension
moonshineCompletionOverCommonDenominator = refl

monsterCompletionOverCommonDenominator :
  commonDenominator + Leech.offDiagonalAfterConformalAdjustment
  ≡ Leech.monsterNontrivialDegree
monsterCompletionOverCommonDenominator = refl

record CrossLaneSelectionBoundary : Set where
  constructor crossLaneSelectionBoundary
  field
    actualRepositoryObjectsShareDenominator : Bool
    actualRepositoryObjectsShareDenominatorIsTrue :
      actualRepositoryObjectsShareDenominator ≡ true
    leechCoordinateCountDerivesWilsonEstimate : Bool
    leechCoordinateCountDerivesWilsonEstimateIsFalse :
      leechCoordinateCountDerivesWilsonEstimate ≡ false
    wilsonEstimateConstructsMonsterModule : Bool
    wilsonEstimateConstructsMonsterModuleIsFalse :
      wilsonEstimateConstructsMonsterModule ≡ false
    commonOriginTheoremStillRequired : Bool
    commonOriginTheoremStillRequiredIsTrue :
      commonOriginTheoremStillRequired ≡ true

canonicalCrossLaneSelectionBoundary : CrossLaneSelectionBoundary
canonicalCrossLaneSelectionBoundary =
  crossLaneSelectionBoundary true refl false refl false refl true refl
