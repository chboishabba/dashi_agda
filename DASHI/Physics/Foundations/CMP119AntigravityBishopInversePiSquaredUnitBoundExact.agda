{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityBishopInversePiSquaredUnitBoundExact where

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_)
open import Data.Sum.Base using (inj₂)

import Real as Bishop
import RealProperties as BishopP
import Inverse as BishopInverse

import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopMachinPiRationalWindowExact as Window
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- CONSTRUCTIVE NUMERICAL NORMALIZATION FOR THE SU(2) TRACE COEFFICIENT
--
-- Existing repo theorem: 3 < bishopMachinPi.
-- Hence 1 < bishopMachinPi, and positivity plus inverse antitonicity gives
--
--   0 < pi^{-1} < 1.
--
-- Squaring on the positive cone yields
--
--   0 < pi^{-2} < 1.
--
-- This proves the numerical inequality needed by S4b without decimal pi,
-- floating point, or an imported transcendental oracle.
------------------------------------------------------------------------

oneU threeU : ℚᵘ
oneU = + 1 / 1
threeU = + 3 / 1

oneReal threeReal : Bishop.ℝ
oneReal = Bishop._⋆ oneU
threeReal = Bishop._⋆ threeU

oneBelowThree : Bishop._<_ oneReal threeReal
oneBelowThree =
  BishopP.p<q⇒p⋆<q⋆
    oneU threeU
    (ℚ.positive⁻¹ (+ 2 / 1))

oneBelowMachinPi : Bishop._<_ oneReal Machin.bishopMachinPi
oneBelowMachinPi =
  BishopP.<-trans oneBelowThree Window.threeBelowMachinPi

onePositive : Bishop._<_ Bishop.0ℝ oneReal
onePositive =
  BishopP.p<q⇒p⋆<q⋆
    (+ 0 / 1) oneU
    (ℚ.positive⁻¹ oneU)

machinPiPositive : Bishop._<_ Bishop.0ℝ Machin.bishopMachinPi
machinPiPositive =
  BishopP.<-trans onePositive oneBelowMachinPi

oneNonzero : oneReal Bishop.≄ Bishop.0ℝ
oneNonzero = inj₂ onePositive

machinPiNonzero : Machin.bishopMachinPi Bishop.≄ Bishop.0ℝ
machinPiNonzero = inj₂ machinPiPositive

inversePi : Bishop.ℝ
inversePi =
  BishopInverse._⁻¹ Machin.bishopMachinPi machinPiNonzero

inverseOne : Bishop.ℝ
inverseOne =
  BishopInverse._⁻¹ oneReal oneNonzero

inverseOneIsOne :
  inverseOne Bishop.≃ oneReal
inverseOneIsOne =
  BishopP.≃-symm
    (BishopInverse.⁻¹-unique
      oneReal oneReal oneNonzero
      (BishopP.*-identityʳ oneReal))

inversePiPositive :
  Bishop._<_ Bishop.0ℝ inversePi
inversePiPositive =
  BishopInverse.0<x⇒0<x⁻¹
    machinPiNonzero
    machinPiPositive

inversePiBelowOne :
  Bishop._<_ inversePi oneReal
inversePiBelowOne =
  BishopP.<-respʳ-≃
    inverseOneIsOne
    (BishopInverse.x<y∧posx,y⇒y⁻¹<x⁻¹
      oneBelowMachinPi
      oneNonzero
      machinPiNonzero
      (BishopP.0<x⇒posx onePositive)
      (BishopP.0<x⇒posx machinPiPositive))

inversePiNonnegative : Bishop.NonNegative inversePi
inversePiNonnegative =
  BishopP.pos⇒nonNeg (BishopP.0<x⇒posx inversePiPositive)

inversePiAtMostOne :
  Bishop._≤_ inversePi oneReal
inversePiAtMostOne =
  BishopP.<⇒≤ inversePiBelowOne

inversePiSquared : Bishop.ℝ
inversePiSquared = Bishop._*_ inversePi inversePi

inversePiSquaredAtMostOne :
  Bishop._≤_ inversePiSquared oneReal
inversePiSquaredAtMostOne =
  let
    first :
      (inversePi Bishop.* inversePi)
      Bishop.≤
      (oneReal Bishop.* oneReal)
    first =
      BishopP.*-mono-≤
        inversePiNonnegative inversePiNonnegative
        inversePiAtMostOne inversePiAtMostOne
  in
  BishopP.≤-respʳ-≃
    (BishopP.*-identityʳ oneReal)
    first

bishopMachinInversePiSquaredUnitBoundLevel : ProofLevel
bishopMachinInversePiSquaredUnitBoundLevel = machineChecked

-- Remaining semantic seam: identify the inversePiSquared field used by the
-- selected SU(2) trace/running-coupling convention with this exact Bishop value.
selectedYMInversePiSquaredIsBishopMachinValueLevel : ProofLevel
selectedYMInversePiSquaredIsBishopMachinValueLevel = conditional
