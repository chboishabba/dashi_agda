module DASHI.Analysis.RiemannReflectionOrbitDefectRegression where

------------------------------------------------------------------------
-- Focused regression root for the 2026 reflection-orbit lane.
--
-- Primary analytic calibration:
-- Levent Alpöge and Ralph Furman,
-- "More than two thirds of the zeta zeros are simple and on the critical line",
-- arXiv:2608.13637 (2026), DOI: 10.48550/arXiv.2608.13637.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannReflectionOrbitDefectExact as Orbit
import DASHI.Analysis.RiemannReflectionPairBlockExact as Block
import DASHI.Analysis.RiemannWeilOffLineHyperbolicBlockExact as Hyperbolic
import DASHI.Analysis.RiemannComplexPoissonPairEnergyExact as PairEnergy
import DASHI.Analysis.RiemannReflectionC3OrbitShapeBridgeExact as C3Bridge

regressionReflectInvolutive :
  (x : Orbit.CentredReflectionState) → Orbit.reflect (Orbit.reflect x) ≡ x
regressionReflectInvolutive = Orbit.reflectInvolutive

regressionFixedImpliesCentre :
  (x : Orbit.CentredReflectionState) →
  Orbit.reflect x ≡ x → x ≡ Orbit.criticalCentre
regressionFixedImpliesCentre = Orbit.reflectionFixedImpliesCriticalCentre

regressionZeroDefectImpliesCentre :
  (x : Orbit.CentredReflectionState) →
  Orbit.squaredDefect x ≡ 0 → x ≡ Orbit.criticalCentre
regressionZeroDefectImpliesCentre = Orbit.zeroDefectImpliesCriticalCentre

regressionLeftRightCountsEqual :
  (p : Orbit.ReflectionPopulation) → Orbit.leftCount p ≡ Orbit.rightCount p
regressionLeftRightCountsEqual = Orbit.leftRightCountsEqual

regressionNonFixedSplitsIntoEqualSides :
  (p : Orbit.ReflectionPopulation) →
  Orbit.nonFixedCount p ≡ Orbit.leftCount p + Orbit.rightCount p
regressionNonFixedSplitsIntoEqualSides = Orbit.nonFixedSplitsIntoEqualSides

regressionTraceBlindButDefectRetained :
  Block.traceLike (Block.reflectionDefectBlock Block.nearPair)
    ≡ Block.traceLike (Block.reflectionDefectBlock Block.farPair)
regressionTraceBlindButDefectRetained = Block.nearAndFarTraceCollide

regressionNearDefectOne :
  Block.determinantMagnitudeLike (Block.reflectionDefectBlock Block.nearPair) ≡ 1
regressionNearDefectOne = Block.nearPairDefectIsOne

regressionFarDefectNine :
  Block.determinantMagnitudeLike (Block.reflectionDefectBlock Block.farPair) ≡ 9
regressionFarDefectNine = Block.farPairDefectIsNine

regressionOffLineCountTwoPairBudgets :
  (p : Orbit.ReflectionPopulation) →
  Orbit.nonFixedCount p
    ≡ Hyperbolic.sourcePositiveIndexBudget p
      + Hyperbolic.sourcePositiveIndexBudget p
regressionOffLineCountTwoPairBudgets =
  Hyperbolic.offLineCountIsTwoSourcePositiveBudgets

regressionSignatureCannotRecoverDefect :
  (decode : Nat → Nat) →
  ((x : Orbit.CentredReflectionState) →
    decode (Hyperbolic.sourceSignatureCode x) ≡ Orbit.squaredDefect x) →
  ⊥
regressionSignatureCannotRecoverDefect =
  Hyperbolic.sourceSignatureCannotDetermineSquaredDefect

-- New local producer: the same bare hyperbolic role can carry a strictly
-- larger Hermitian/Frobenius residual once complex-Poisson norm information is
-- retained.  These checks exercise the exact polynomial block identity.
regressionNearPairFrobeniusTwenty :
  PairEnergy.pairBlockFrobeniusSquared PairEnergy.nearPairEnergy ≡ 20
regressionNearPairFrobeniusTwenty = PairEnergy.nearPairFrobeniusIsTwenty

regressionFarPairFrobeniusHundred :
  PairEnergy.pairBlockFrobeniusSquared PairEnergy.farPairEnergy ≡ 100
regressionFarPairFrobeniusHundred = PairEnergy.farPairFrobeniusIsHundred

regressionNearPairExcessSixteen :
  PairEnergy.pairBlockFrobeniusExcess PairEnergy.nearPairEnergy ≡ 16
regressionNearPairExcessSixteen = PairEnergy.nearPairExcessIsSixteen

regressionFarPairExcessNinetySix :
  PairEnergy.pairBlockFrobeniusExcess PairEnergy.farPairEnergy ≡ 96
regressionFarPairExcessNinetySix = PairEnergy.farPairExcessIsNinetySix

regressionC3InverseRoleInvariant :
  C3Bridge.c3OrbitRole C3Bridge.zetaPhase
    ≡ C3Bridge.c3OrbitRole C3Bridge.zetaInversePhase
regressionC3InverseRoleInvariant = C3Bridge.c3NontrivialPairHasSingleRole

regressionZetaRoleCanHideDistinctDefect :
  C3Bridge.zetaOrbitRole (Orbit.offLine Orbit.left 0)
    ≡ C3Bridge.zetaOrbitRole (Orbit.offLine Orbit.right 2)
regressionZetaRoleCanHideDistinctDefect =
  C3Bridge.zetaSameRoleCanRetainDifferentDefects
