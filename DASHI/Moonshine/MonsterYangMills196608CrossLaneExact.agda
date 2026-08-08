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
-- The conformal line lies in the diagonal 24-dimensional quadratic sector,
-- so the correct geometric quotient is
--
--   196883 = (196608 - 1) + 276
--          = 196607 + 276.
--
-- The numerically equivalent 196608 + 275 identity is retained only as
-- arithmetic and is not interpreted as a canonical 275-dimensional sector.
-- The same integer 196608 is thus both the reduced denominator of the sharp
-- Wilson budget and a natural basis-coordinate subtotal of the Leech
-- lattice-VOA weight-two space.  No common dynamical selection theorem is
-- asserted.
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

monsterGeometricCompletionAfterConformalQuotient :
  Leech.coordinateSubtotalAfterConformalQuotient
  + Leech.offDiagonalQuadraticCount
  ≡ Leech.monsterNontrivialDegree
monsterGeometricCompletionAfterConformalQuotient = refl

monsterNumericalCompletionOverCommonDenominator :
  commonDenominator + Leech.numericalResidualBeyond196608
  ≡ Leech.monsterNontrivialDegree
monsterNumericalCompletionOverCommonDenominator = refl

record CrossLaneSelectionBoundary : Set where
  constructor crossLaneSelectionBoundary
  field
    actualRepositoryObjectsShareDenominator : Bool
    actualRepositoryObjectsShareDenominatorIsTrue :
      actualRepositoryObjectsShareDenominator ≡ true
    conformalQuotientPlacedInDiagonalSector : Bool
    conformalQuotientPlacedInDiagonalSectorIsTrue :
      conformalQuotientPlacedInDiagonalSector ≡ true
    numerical275PromotedToCanonicalSector : Bool
    numerical275PromotedToCanonicalSectorIsFalse :
      numerical275PromotedToCanonicalSector ≡ false
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
  crossLaneSelectionBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
