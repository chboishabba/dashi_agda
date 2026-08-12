module DASHI.Physics.Closure.NSTriadKNHHBadLiveBudgetTargetRound48Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Gyula Farkas.
-- Title: "Theorie der einfachen Ungleichungen".
-- Journal fuer die reine und angewandte Mathematik 124 (1902), 1--27.
-- DOI: no DOI assigned to the historical article.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Convert every proved Com/kernel hard floor immediately into the sharp
-- remaining HH-bad ceiling target.  With boundary zero, HH-good soft and the
-- Bony quartet fixed at 1/16,
--
--   H2 = 2 C_* + tau_Com + tau_kernel + 1/16.
--
-- Therefore
--
--   H2 < 1
--     iff
--   C_* < 15/32 - (tau_Com + tau_kernel)/2.
--
-- The H1 and H0 targets are obtained by setting the corresponding floor to
-- zero.  This lets the physical proof maintain one live scalar target while
-- Com and kernel are being classified.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_; _<_; positive)
import Data.Rational.Properties as ℚP
open ℚP using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; subst₂; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHardGateHierarchyRound47Exact as Gate

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward : A → B
    backward : B → A

open _↔_ public
infix 2 _↔_

fifteenThirtySeconds : ℚ
fifteenThirtySeconds = Int.+ 15 / 32

halfPositive : 0ℚ < Sharp.half
halfPositive = toWitness {a? = 0ℚ <? Sharp.half} _

twoPositive : 0ℚ < Sharp.two
twoPositive = toWitness {a? = 0ℚ <? Sharp.two} _

allowableHHBadCeiling : ℚ → ℚ → ℚ
allowableHHBadCeiling comFloor kernelFloor =
  fifteenThirtySeconds
    - Sharp.half * (comFloor + kernelFloor)

h2StrictImpliesLiveCeilingTarget :
  ∀ ceiling comFloor kernelFloor →
  Gate.hardGateH2 ceiling comFloor kernelFloor < 1ℚ →
  ceiling < allowableHHBadCeiling comFloor kernelFloor
h2StrictImpliesLiveCeilingTarget ceiling comFloor kernelFloor h2Strict =
  let
    closed :
      Sharp.two * ceiling + comFloor + kernelFloor + Gate.oneSixteenth
      < 1ℚ
    closed = h2Strict

    shifted :
      Sharp.two * ceiling
      < Sharp.two * allowableHHBadCeiling comFloor kernelFloor
    shifted =
      subst₂ _<_
        (solve (ceiling ∷ comFloor ∷ kernelFloor ∷ []))
        (solve (comFloor ∷ kernelFloor ∷ []))
        (ℚP.+-cancelʳ-<
          (comFloor + kernelFloor + Gate.oneSixteenth)
          (subst
            (λ right →
              Sharp.two * ceiling
                + (comFloor + kernelFloor + Gate.oneSixteenth)
              < right)
            (solve (comFloor ∷ kernelFloor ∷ []))
            (subst
              (λ left →
                left
                < 1ℚ)
              (solve (ceiling ∷ comFloor ∷ kernelFloor ∷ []))
              closed)))

    halved :
      Sharp.half * (Sharp.two * ceiling)
      < Sharp.half
        * (Sharp.two * allowableHHBadCeiling comFloor kernelFloor)
    halved =
      let instance halfPosI = positive halfPositive
      in ℚP.*-monoʳ-<-pos Sharp.half shifted
  in
  subst₂ _<_
    (solve (ceiling ∷ []))
    (solve (comFloor ∷ kernelFloor ∷ []))
    halved

liveCeilingTargetImpliesH2Strict :
  ∀ ceiling comFloor kernelFloor →
  ceiling < allowableHHBadCeiling comFloor kernelFloor →
  Gate.hardGateH2 ceiling comFloor kernelFloor < 1ℚ
liveCeilingTargetImpliesH2Strict ceiling comFloor kernelFloor target =
  let
    doubled :
      Sharp.two * ceiling
      < Sharp.two * allowableHHBadCeiling comFloor kernelFloor
    doubled =
      let instance twoPosI = positive twoPositive
      in ℚP.*-monoʳ-<-pos Sharp.two target

    shifted :
      Sharp.two * ceiling + comFloor + kernelFloor + Gate.oneSixteenth
      < Sharp.two * allowableHHBadCeiling comFloor kernelFloor
        + comFloor + kernelFloor + Gate.oneSixteenth
    shifted =
      ℚP.+-mono-<-≤
        (ℚP.+-mono-<-≤ doubled ℚP.≤-refl)
        ℚP.≤-refl
  in
  subst
    (λ right → Gate.hardGateH2 ceiling comFloor kernelFloor < right)
    (solve (comFloor ∷ kernelFloor ∷ []))
    shifted

h2StrictIffLiveHHBadCeilingTarget :
  ∀ ceiling comFloor kernelFloor →
  (Gate.hardGateH2 ceiling comFloor kernelFloor < 1ℚ)
  ↔ (ceiling < allowableHHBadCeiling comFloor kernelFloor)
h2StrictIffLiveHHBadCeilingTarget ceiling comFloor kernelFloor =
  iff
    (h2StrictImpliesLiveCeilingTarget ceiling comFloor kernelFloor)
    (liveCeilingTargetImpliesH2Strict ceiling comFloor kernelFloor)

allowableWithSoftCom : ∀ kernelFloor →
  allowableHHBadCeiling 0ℚ kernelFloor
  ≡ fifteenThirtySeconds - Sharp.half * kernelFloor
allowableWithSoftCom kernelFloor = solve (kernelFloor ∷ [])

allowableWithSoftComAndKernel :
  allowableHHBadCeiling 0ℚ 0ℚ ≡ fifteenThirtySeconds
allowableWithSoftComAndKernel = solve []

liveHHBadBudgetTargetExposed : Bool
liveHHBadBudgetTargetExposed = true

liveHHBadBudgetTargetExposedIsTrue :
  liveHHBadBudgetTargetExposed ≡ true
liveHHBadBudgetTargetExposedIsTrue = refl
