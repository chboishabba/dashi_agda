module DASHI.Moonshine.Base369MonsterThreeLocalTenByNineRefactorBidiExact where

------------------------------------------------------------------------
-- THREE-LOCAL REFACTOR THROUGH THE TYPED 10 x 9 SURFACE
--
-- Existing sourced Monster 3-local arithmetic gives
--
--   10 * 3^8 = 90 * 3^6 = 65610,
--   3^8 = 9 * 3^6.
--
-- The Base369 pointed-appraisal lane independently owns a typed 10 x 9
-- relational surface of size 90.  Substituting that typed factor makes the
-- arithmetic meeting transparent:
--
--   10 * 3^8
--     = 10 * 9 * 3^6
--     = (10 x 9) * 729.
--
-- This remains a refactor of dimensions.  The 3^8.Omega^-(8,3).2 chart and
-- the extraspecial 3^(1+12) Heisenberg chart are deliberately not identified.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

import DASHI.Moonshine.MonsterThreeLocalE8LeechBridgeExact as ThreeLocal
import DASHI.Moonshine.Base369Monster3BMultiplicityTenByNineBidiExact as Ninety

threePowerEightViaNineTimesThreePowerSix :
  ThreeLocal.threePowerEight ≡ 9 * ThreeLocal.threePowerSix
threePowerEightViaNineTimesThreePowerSix =
  ThreeLocal.threePowerEightIsNineTimesThreePowerSix

tenTimesThreePowerEightViaTenByNine :
  10 * ThreeLocal.threePowerEight
  ≡ Ninety.tenByNineDimension * ThreeLocal.threePowerSix
tenTimesThreePowerEightViaTenByNine = refl

tenByNineTimesThreePowerSixIs65610 :
  Ninety.tenByNineDimension * ThreeLocal.threePowerSix ≡ 65610
tenByNineTimesThreePowerSixIs65610 = refl

threePhaseThreeLocalRefactor : Nat
threePhaseThreeLocalRefactor =
  3 * (Ninety.tenByNineDimension * ThreeLocal.threePowerSix)

threePhaseThreeLocalRefactorIs196830 :
  threePhaseThreeLocalRefactor ≡ 196830
threePhaseThreeLocalRefactorIs196830 = refl

record ThreeLocalTenByNineBoundary : Set where
  constructor threeLocalTenByNineBoundary
  field
    sourcedThreePowerEightChartOwned : Bool
    sourcedThreePowerSixChartOwned : Bool
    typedBase369TenByNineFactorOwned : Bool
    common65610RefactorExact : Bool
    common196830ThreePhaseRefactorExact : Bool
    threePowerEightGroupIdentifiedWithExtraspecialKernel : Bool
    arithmeticRefactorCreatesEquivariantMap : Bool

canonicalThreeLocalTenByNineBoundary : ThreeLocalTenByNineBoundary
canonicalThreeLocalTenByNineBoundary =
  threeLocalTenByNineBoundary true true true true true false false
