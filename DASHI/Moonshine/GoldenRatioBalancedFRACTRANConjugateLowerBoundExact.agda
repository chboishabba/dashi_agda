module DASHI.Moonshine.GoldenRatioBalancedFRACTRANConjugateLowerBoundExact where

------------------------------------------------------------------------
-- UNIFORM LOWER BOUND FOR THE CONJUGATE GOLDEN-RATIO FACTOR
--
-- We do not need the stronger theorem psi_B < 0.  The already-proved strict
-- positivity sqrt(5)_B > 0 gives
--
--   psi_B = 1/2 (1 - sqrt(5)_B) < 1/2.
--
-- Every balanced-FRACTRAN macro ratio satisfies r_n >= 1, hence
--
--   1/2 < r_n - psi_B.
--
-- This is exactly the uniform factor-separation receipt needed after the
-- quadratic factorisation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Integer.Base as ℤ using (+_; +≤+)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)
open import Data.Rational.Unnormalised as ℚ using
  (0ℚᵘ; _/_; _≤_; *≤*)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopGoldenRatioCarrierExact as Phi
import DASHI.Foundations.BishopNatSquareRootPositiveExact as RootPositive
import DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopRatioCarrierExact as Ratio
import DASHI.Moonshine.GoldenRatioBalancedFRACTRANNormOneInvariantExact as Norm
import DASHI.Moonshine.GoldenRatioBishopQuadraticFactorisationBidiExact as Factor
import DASHI.Moonshine.GoldenRatioBalancedFRACTRANRationalDefectExact as RationalDefect

------------------------------------------------------------------------
-- 1. Every two-step macro output has numerator >= denominator.
------------------------------------------------------------------------

macroStepHiGeLo :
  (pair : Ratio.PositiveFibPair) →
  Ratio.positiveLo (Ratio.positiveFibTwoStep pair)
  ≤ Ratio.positiveHi (Ratio.positiveFibTwoStep pair)
macroStepHiGeLo pair =
  let
    p = Ratio.positiveHi pair
    q = Ratio.positiveLo pair
    raw : p + q ≤ (p + q) + p
    raw = NatP.m≤m+n (p + q) p
    rearrange : (p + q) + p ≡ p + p + q
    rearrange =
      solve 2
        (λ p q → (p :+ q) :+ p := (p :+ p) :+ q)
        refl p q
  in
  NatP.≤-trans
    raw
    (NatP.≤-reflexive rearrange)
  where
  open Norm using (twoStepHiFormula; twoStepLoFormula)

macroHiGeLo :
  (n : Nat) →
  Ratio.positiveLo (Ratio.iteratePositiveMacro n)
  ≤ Ratio.positiveHi (Ratio.iteratePositiveMacro n)
macroHiGeLo zero = s≤s z≤n
macroHiGeLo (suc n)
  rewrite Norm.twoStepLoFormula (Ratio.iteratePositiveMacro n)
        | Norm.twoStepHiFormula (Ratio.iteratePositiveMacro n) =
  let
    p = Ratio.positiveHi (Ratio.iteratePositiveMacro n)
    q = Ratio.positiveLo (Ratio.iteratePositiveMacro n)
    raw : p + q ≤ (p + q) + p
    raw = NatP.m≤m+n (p + q) p
    rearrange : (p + q) + p ≡ p + p + q
    rearrange =
      solve 2
        (λ p q → (p :+ q) :+ p := (p :+ p) :+ q)
        refl p q
  in
  NatP.≤-trans raw (NatP.≤-reflexive rearrange)

------------------------------------------------------------------------
-- 2. Therefore one <= every rational/Bishop macro ratio.
------------------------------------------------------------------------

oneBelowMacroRational :
  (n : Nat) →
  RationalDefect.oneQ ℚ.≤
    Ratio.positiveRatioRational (Ratio.iteratePositiveMacro n)
oneBelowMacroRational n =
  ℚ.*≤* (ℤ.+≤+ (macroHiGeLo n))

oneBelowMacroBishop :
  (n : Nat) →
  BishopReal._≤_
    Phi.one
    (Ratio.balancedFRACTRANBishopRatioSequence n)
oneBelowMacroBishop n =
  BishopP.p≤q⇒p⋆≤q⋆
    RationalDefect.oneQ
    (Ratio.positiveRatioRational (Ratio.iteratePositiveMacro n))
    (oneBelowMacroRational n)

------------------------------------------------------------------------
-- 3. psi_B < 1/2 using only sqrt(5)_B > 0.
------------------------------------------------------------------------

sqrtFivePositive : BishopReal._<_ BishopReal.0ℝ Phi.sqrtFive
sqrtFivePositive =
  RootPositive.canonicalFloorSquareRootStrictlyPositive
    (s≤s z≤n)

halfPositive : BishopReal.Positive Phi.half
halfPositive =
  BishopP.posp⇒posp⋆
    (+ 1 / 2)
    (ℚP.positive⁻¹ (+ 1 / 2))

oneMinusSqrtFiveBelowOne :
  BishopReal._<_
    (BishopReal._-_ Phi.one Phi.sqrtFive)
    Phi.one
oneMinusSqrtFiveBelowOne =
  BishopP.0<ε⇒x-ε<x Phi.one sqrtFivePositive

psiBelowHalfRaw :
  BishopReal._<_
    Factor.bishopPsi
    (BishopReal._*_ Phi.half Phi.one)
psiBelowHalfRaw =
  BishopP.*-monoʳ-<-pos
    halfPositive
    oneMinusSqrtFiveBelowOne

psiBelowHalf : BishopReal._<_ Factor.bishopPsi Phi.half
psiBelowHalf =
  BishopP.<-respʳ-≃
    (BishopP.*-identityʳ Phi.half)
    psiBelowHalfRaw

------------------------------------------------------------------------
-- 4. 1/2 < r_n - psi_B uniformly.
------------------------------------------------------------------------

oneMinusHalfIsHalf :
  BishopReal._≃_
    (BishopReal._-_ Phi.one Phi.half)
    Phi.half
oneMinusHalfIsHalf =
  let open BishopP.ℝ-Solver
  in solve 0
    (Κ (+ 1 / 1) ⊖ Κ (+ 1 / 2) ⊜ Κ (+ 1 / 2))
    BishopP.≃-refl

oneMinusHalfBelowOneMinusPsi :
  BishopReal._<_
    (BishopReal._-_ Phi.one Phi.half)
    (BishopReal._-_ Phi.one Factor.bishopPsi)
oneMinusHalfBelowOneMinusPsi =
  BishopP.+-monoʳ-<
    Phi.one
    (BishopP.neg-mono-< psiBelowHalf)

oneMinusPsiBelowMacroMinusPsi :
  (n : Nat) →
  BishopReal._≤_
    (BishopReal._-_ Phi.one Factor.bishopPsi)
    (BishopReal._-_
      (Ratio.balancedFRACTRANBishopRatioSequence n)
      Factor.bishopPsi)
oneMinusPsiBelowMacroMinusPsi n =
  BishopP.+-monoˡ-≤
    (BishopReal.- Factor.bishopPsi)
    (oneBelowMacroBishop n)

halfBelowMacroMinusPsi :
  (n : Nat) →
  BishopReal._<_
    Phi.half
    (BishopReal._-_
      (Ratio.balancedFRACTRANBishopRatioSequence n)
      Factor.bishopPsi)
halfBelowMacroMinusPsi n =
  BishopP.<-respˡ-≃
    oneMinusHalfIsHalf
    (BishopP.<-≤-trans
      oneMinusHalfBelowOneMinusPsi
      (oneMinusPsiBelowMacroMinusPsi n))

------------------------------------------------------------------------
-- 5. Frontier.
------------------------------------------------------------------------

record ConjugateLowerBoundFrontier : Set where
  constructor conjugate-lower-bound-frontier
  field
    macroNumeratorAtLeastDenominator : Bool
    macroRatioAtLeastOneOnBishop : Bool
    sqrtFiveStrictlyPositiveReused : Bool
    psiStrictlyBelowHalf : Bool
    uniformHalfLowerBoundOnRatioMinusPsi : Bool
    productCancellationToPhiLimitPaid : Bool

canonicalConjugateLowerBoundFrontier : ConjugateLowerBoundFrontier
canonicalConjugateLowerBoundFrontier =
  conjugate-lower-bound-frontier true true true true true false
