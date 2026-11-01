module DASHI.Physics.Closure.NSTriadKNPointwiseDangerDriftNoGoRound82Exact where

------------------------------------------------------------------------
-- ROUND82 / POINTWISE-DRIFT NO-GO
--
-- The repository's adversarial compact-Gamma search correctly treats
--
--   danger => Bdot < 0 pointwise
--
-- as a falsifiable *strong* candidate.  The deterministic occupation theorem
-- does not need that statement.  This exact two-slot model exhibits the logical
-- separation:
--
--   both slots are declared dangerous;
--   slot 1 has Bdot = -1;
--   slot 2 has Bdot = +1/2;
--
-- so pointwise negative drift fails at slot 2, while the integrated net escape
-- is 1/2.  With residence=2 and cost=1/4, that same integrated margin pays
--
--   cost * residence = 1/2.
--
-- Thus intermittent replenishment during danger is compatible with the exact
-- occupation inequality consumed by Round82.  This is a finite algebraic
-- countermodel to making pointwise negativity a necessary proof obligation;
-- it is not a Navier--Stokes counterexample.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _+_; _-_; _*_; _<_)
import Data.Rational.Properties as ℚP
open ℚP using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)

oneHalf : ℚ
oneHalf = Int.+ 1 / 2

oneFourth : ℚ
oneFourth = Int.+ 1 / 4

firstDangerDrift : ℚ
firstDangerDrift = 0ℚ - 1ℚ

secondDangerDrift : ℚ
secondDangerDrift = oneHalf

integratedNetDrift : ℚ
integratedNetDrift = firstDangerDrift + secondDangerDrift

integratedEscapeMargin : ℚ
integratedEscapeMargin = 0ℚ - integratedNetDrift

dangerousResidence : ℚ
dangerousResidence = 1ℚ + 1ℚ

dangerCost : ℚ
dangerCost = oneFourth

secondDangerousSlotHasPositiveDrift : 0ℚ < secondDangerDrift
secondDangerousSlotHasPositiveDrift =
  toWitness {a? = 0ℚ <? secondDangerDrift} _

integratedNetDriftIsNegativeHalf :
  integratedNetDrift ≡ 0ℚ - oneHalf
integratedNetDriftIsNegativeHalf = solve []

integratedEscapeMarginIsHalf :
  integratedEscapeMargin ≡ oneHalf
integratedEscapeMarginIsHalf = solve []

integratedDangerOccupationPaidExactly :
  dangerCost * dangerousResidence ≡ integratedEscapeMargin
integratedDangerOccupationPaidExactly = solve []

round82PointwiseNegativeDangerDriftIsNecessary : Bool
round82PointwiseNegativeDangerDriftIsNecessary = false

round82IntegratedOccupationCanSurviveIntermittentReplenishment : Bool
round82IntegratedOccupationCanSurviveIntermittentReplenishment = true

round82IntegratedOccupationCanSurviveIntermittentReplenishmentIsTrue :
  round82IntegratedOccupationCanSurviveIntermittentReplenishment ≡ true
round82IntegratedOccupationCanSurviveIntermittentReplenishmentIsTrue = refl
