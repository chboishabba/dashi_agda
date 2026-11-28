module DASHI.Physics.YangMills.YMClayCMP102Section34FactorialMassAcceptanceExact where

------------------------------------------------------------------------
-- Source-native acceptance root: original CMP102 factorial singleton,
-- exact Bishop finite ratio-bank, ORIGINAL coefficient masses and
-- existing signed Cauchy shifted-wing order owner.
--
-- NO claim that original factorial successor ratio has a native
-- proof: two explicit original A/B ratio premise types remain.
-- No interacting SU(N) measure, OS or same-H mass gap is inferred.
-- Requires pinned Agda 2.9, Bishop vendor and --safe graph.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Real as R
import Sequence as Seq

import DASHI.Foundations.BishopFiniteRatioBudgetExact as Budget
import DASHI.Physics.YangMills.YMClayCMP102OriginalFactorialSingletonExact as Singleton
import DASHI.Physics.YangMills.YMClayCMP102OriginalFactorialMassBudgetExact as Mass
import DASHI.Physics.YangMills.YMClayCMP102OriginalFactorialNatGrowthExact as NatGrowth
import DASHI.Physics.YangMills.YMClayCMP102OriginalFactorialRatioBishopExact as Ratio
import DASHI.Physics.YangMills.YMClayCMP102OriginalShiftedWingOrderExact as Wings
import DASHI.Physics.YangMills.YMClayCMP102OriginalEndpointCauchyShiftExact as Original

originalAMassFromOriginalFactorialRatio :
  Mass.OriginalARatio → ∀ count →
  R._≤_ (Seq.SeriesOf Original.aCoefficient count)
    (R._⋆ (+ 6 / 11))
originalAMassFromOriginalFactorialRatio =
  Mass.originalAAllFiniteMassFromFactorialRatio

originalBMassFromOriginalFactorialRatio :
  Mass.OriginalBRatio → ∀ count →
  R._≤_ (Seq.SeriesOf Original.bCoefficient count)
    (R._⋆ (+ 10 / 57))
originalBMassFromOriginalFactorialRatio =
  Mass.originalBAllFiniteMassFromFactorialRatio

originalActualAShiftedWing = Wings.originalAShiftedAbsoluteWing
originalActualBShiftedWing = Wings.originalBShiftedAbsoluteWing
originalActualSignedTailTriangle =
  Wings.originalSignedCauchyTailTriangleBound

-- Section34B all-index source: the TWO formerly explicit ratio
-- leaves are now source-written from actual Nat factorial growth
-- through the original rational embedding/order theorem.
originalNativeANatDenominatorGrowth =
  NatGrowth.originalADenominatorGrowth
originalNativeBNatDenominatorGrowth =
  NatGrowth.originalBDenominatorGrowth
originalNativeARatio = Ratio.originalARatioBishop
originalNativeBRatio = Ratio.originalBRatioBishop

-- Literal original A/B finite SeriesOf masses: NO ratio premises.
originalNativeAMassUnconditional :
  ∀ count →
  R._≤_ (Seq.SeriesOf Original.aCoefficient count)
    (R._⋆ (+ 6 / 11))
originalNativeAMassUnconditional =
  Ratio.originalAllAMassBelowSixElevenths

originalNativeBMassUnconditional :
  ∀ count →
  R._≤_ (Seq.SeriesOf Original.bCoefficient count)
    (R._⋆ (+ 10 / 57))
originalNativeBMassUnconditional =
  Ratio.originalAllBMassBelowTenFiftySevenths
