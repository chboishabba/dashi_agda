module DASHI.Mathematics.Topology.AlexanderHornedC3F7FullActorMaschkeExact where

------------------------------------------------------------------------
-- FULL FINITE ACTOR, NOT MERELY THE C3 RESTRICTION
--
-- A5^3 rtimes C3 has 3*60^3 = 648000 elements.
-- 2I^3 rtimes C3 has 3*120^3 = 5184000 elements.
-- Both are 3 mod 7; in particular characteristic 7 does
-- NOT divide either group order. Therefore Maschke's
-- classical theorem applies to EVERY linear representation
-- of BOTH full groups over F7.
--
-- In contrast, F5 is nonmodular for C3 but MODULAR for
-- each entire A5/2I actor. F2 would erase the central
-- spin sign even on the C3 restriction.
--
-- PREVIOUS OWNERS:
--   AlexanderHornedSpinVOAFactorFunctorExact
--      generic mode-preserving factor pullback 360->180;
--   AlexanderHornedC3MaschkeReynoldsExact
--      true three-point rational C3 projector;
--   NormalizedFibreAveragingExact
--      genuine finite averaging projector;
--   IbrahimMonster3BWholeCharacterIsotypicBypassExact
--      actual mathlib Maschke source provenance.
--
-- This module pays the EXACT group-order and rational
-- 2:1 normalization arithmetic. Native Agda F7 field/group
-- representations and kernel-certified Maschke application
-- remain a separate semantic transport gate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _*_; _/_)
import Data.Rational.Tactic.RingSolver as Ring

a5GroupSize : Nat
a5GroupSize = 60

binaryIcosahedralSize : Nat
binaryIcosahedralSize = 120

projectiveActorOrder : Nat
projectiveActorOrder = 3 * (a5GroupSize * (a5GroupSize * a5GroupSize))

spinActorOrder : Nat
spinActorOrder =
  3 * (binaryIcosahedralSize * (binaryIcosahedralSize * binaryIcosahedralSize))

projectiveActorOrderExact : projectiveActorOrder ≡ 648000
projectiveActorOrderExact = refl

spinActorOrderExact : spinActorOrder ≡ 5184000
spinActorOrderExact = refl

-- Division algorithm: remainder is THREE, strictly below 7.
-- Establishing non-divisibility then uses ordinary uniqueness
-- of Euclidean division, not a phantom Agda Maschke proof.
projectiveOrderSevenQuotient :
  projectiveActorOrder ≡ 7 * 92571 + 3
projectiveOrderSevenQuotient = refl

spinOrderSevenQuotient :
  spinActorOrder ≡ 7 * 740571 + 3
spinOrderSevenQuotient = refl

projectiveCoordinateCount : Nat
projectiveCoordinateCount = 3 * a5GroupSize

spinCoordinateCount : Nat
spinCoordinateCount = 3 * binaryIcosahedralSize

projectiveCoordinatesAre180 : projectiveCoordinateCount ≡ 180
projectiveCoordinatesAre180 = refl

spinCoordinatesAre360 : spinCoordinateCount ≡ 360
spinCoordinatesAre360 = refl

coordinateCoverDegreeTwo :
  spinCoordinateCount ≡ 2 * projectiveCoordinateCount
coordinateCoverDegreeTwo = refl

-- Over Q, the normalized uniform mean agrees exactly with a
-- double-cover pullback: 2*(1/360) = 1/180. Over F7 the
-- corresponding inverse residues are 5 and 3, respectively.
projectiveUniformWeight : ℚ
projectiveUniformWeight = + 1 / 180

spinUniformWeight : ℚ
spinUniformWeight = + 1 / 360

twofoldNormalizedMeanCoefficient :
  ((+ 2 / 1) * spinUniformWeight) ≡ projectiveUniformWeight
twofoldNormalizedMeanCoefficient = Ring.solve-∀

-- Explicit F7 residues of 180, 360 and full actor orders:
projective180AsSevenQuotient : 180 ≡ 7 * 25 + 5
projective180AsSevenQuotient = refl

spin360AsSevenQuotient : 360 ≡ 7 * 51 + 3
spin360AsSevenQuotient = refl

-- In F7, (180)^(-1)=3, (360)^(-1)=5;
-- 2*(360)^(-1)=10=3=(180)^(-1).
-- The exact F7 equalities, the actual SL2F5->A5 quotient
-- and the normalized finite actor orbit sums are checked
-- in scripts/alexander_horned_c3_f7_full_actor_reynolds.py.
