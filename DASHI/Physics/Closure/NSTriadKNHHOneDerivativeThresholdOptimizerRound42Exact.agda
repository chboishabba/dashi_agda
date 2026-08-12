module DASHI.Physics.Closure.NSTriadKNHHOneDerivativeThresholdOptimizerRound42Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Round 40 proved the exact optimizer for
--
--   A sqrt(delta) + B/delta
--
-- using delta=r^2 and the rational balance A r^3 = 2 B.  Round 42 now knows
-- the actual bad constant produced by the one-derivative inverse-shell route:
--
--   B = 2 C_bad.
--
-- Hence the balanced scale is characterized exactly by
--
--   A r^3 = 4 C_bad.
--
-- This file connects that physical constant to the existing optimizer rather
-- than introducing another optimization layer.  It also proves that, under
-- the existing squared-threshold same-object bridge,
--
--   (2 C_bad)/delta
--
-- is literally the Round-42 bounded thresholded HH-bad cost.  Thus once the
-- physical good coefficient A and scale-free C_bad are known, the threshold
-- optimizer has no hidden bad-side coefficient left.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHAnalyticThresholdOptimizerRound40Exact as Opt
import DASHI.Physics.Closure.NSTriadKNHHSquaredThresholdRepresentationRound40Exact as Squared
import DASHI.Physics.Closure.NSTriadKNHHBadInverseShellDensityFromSchurRound41Exact as Density
import DASHI.Physics.Closure.NSTriadKNHHBadThresholdedOwnerCostRound42Exact as BadCost

oneDerivativeBadOptimizerConstant : ℚ → ℚ
oneDerivativeBadOptimizerConstant Cbad = Sharp.two * Cbad

oneDerivativeBadOptimizerConstantNonnegative :
  ∀ Cbad → 0ℚ ≤ Cbad → 0ℚ ≤ oneDerivativeBadOptimizerConstant Cbad
oneDerivativeBadOptimizerConstantNonnegative Cbad CbadNN =
  Opt.mulNonnegative Opt.twoNonnegative CbadNN

boundedBadCostIsOptimizerBadTax :
  ∀ {effectiveViscosity density : ℚ} {shell : Nat}
    (representation : Squared.SquaredDirectionalThreshold)
    (certificate : Density.OneDerivativeInverseShellDensityCertificate
      effectiveViscosity density shell) →
  BadCost.boundedThresholdedHHBadCost
      (Squared.directionalParameter representation) certificate
  ≡ Squared.physicalBadTaxAtSquaredThreshold
      (oneDerivativeBadOptimizerConstant
        (Density.scaleFreeConstant certificate))
      representation
boundedBadCostIsOptimizerBadTax representation certificate =
  let
    Cbad = Density.scaleFreeConstant certificate
    deltaInverse = Threshold.thresholdInverse
      (Squared.directionalParameter representation)

    physicalBadMeaning :
      Squared.physicalBadTaxAtSquaredThreshold
        (oneDerivativeBadOptimizerConstant Cbad) representation
      ≡ oneDerivativeBadOptimizerConstant Cbad * deltaInverse
    physicalBadMeaning =
      Squared.badTaxUsesLiteralDeltaInverse
        (oneDerivativeBadOptimizerConstant Cbad) representation

    boundedMeaning :
      BadCost.boundedThresholdedHHBadCost
        (Squared.directionalParameter representation) certificate
      ≡ oneDerivativeBadOptimizerConstant Cbad * deltaInverse
    boundedMeaning = solve (Cbad ∷ deltaInverse ∷ Sharp.two ∷ [])
  in
  trans boundedMeaning (sym physicalBadMeaning)

record OneDerivativeBalancedHHThreshold
    {effectiveViscosity density : ℚ} {shell : Nat}
    (A : ℚ)
    (certificate : Density.OneDerivativeInverseShellDensityCertificate
      effectiveViscosity density shell) : Set where
  field
    selectedScale : Threshold.PositiveThreshold
    A-nonnegative : 0ℚ ≤ A
    physicalCubicBalance :
      A
        * Opt.scaleValue selectedScale
        * Opt.scaleValue selectedScale
        * Opt.scaleValue selectedScale
      ≡ Sharp.two * (Sharp.two * Density.scaleFreeConstant certificate)

open OneDerivativeBalancedHHThreshold public

asRound40BalancedThreshold :
  ∀ {effectiveViscosity density : ℚ} {shell : Nat} {A : ℚ}
    {certificate : Density.OneDerivativeInverseShellDensityCertificate
      effectiveViscosity density shell} →
  OneDerivativeBalancedHHThreshold A certificate →
  Opt.BalancedHHThreshold
    A
    (oneDerivativeBadOptimizerConstant
      (Density.scaleFreeConstant certificate))
asRound40BalancedThreshold {certificate = certificate} balance =
  Opt.balanced-hh-threshold
    (selectedScale balance)
    (A-nonnegative balance)
    (oneDerivativeBadOptimizerConstantNonnegative
      (Density.scaleFreeConstant certificate)
      (Density.scaleFreeConstantNonnegative certificate))
    (physicalCubicBalance balance)

oneDerivativeBalancedThresholdIsGlobalMinimum :
  ∀ {effectiveViscosity density : ℚ} {shell : Nat} {A : ℚ}
    {certificate : Density.OneDerivativeInverseShellDensityCertificate
      effectiveViscosity density shell} →
  (balance : OneDerivativeBalancedHHThreshold A certificate) →
  (candidate : Threshold.PositiveThreshold) →
  Opt.combinedHHTax
      A
      (oneDerivativeBadOptimizerConstant
        (Density.scaleFreeConstant certificate))
      (selectedScale balance)
  ≤
  Opt.combinedHHTax
      A
      (oneDerivativeBadOptimizerConstant
        (Density.scaleFreeConstant certificate))
      candidate
oneDerivativeBalancedThresholdIsGlobalMinimum balance =
  Opt.globalBalancedThresholdMinimum (asRound40BalancedThreshold balance)

oneDerivativeBadConstantToThresholdOptimizerClosed : Bool
oneDerivativeBadConstantToThresholdOptimizerClosed = true

oneDerivativeBalancedScaleLawClosed : Bool
oneDerivativeBalancedScaleLawClosed = true

physicalHHGoodCoefficientAStillRequired : Bool
physicalHHGoodCoefficientAStillRequired = true

oneDerivativeBadConstantToThresholdOptimizerClosedIsTrue :
  oneDerivativeBadConstantToThresholdOptimizerClosed ≡ true
oneDerivativeBadConstantToThresholdOptimizerClosedIsTrue = refl
