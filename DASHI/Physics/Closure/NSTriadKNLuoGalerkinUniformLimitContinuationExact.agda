module DASHI.Physics.Closure.NSTriadKNLuoGalerkinUniformLimitContinuationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Rupert L. Frank; Fedor Sukochev; Dmitriy Zanin.
-- Title: "Endpoint Schatten Class Properties of Commutators".
-- Advances in Mathematics 450 (2024), article 109738.
-- DOI: 10.1016/j.aim.2024.109738.
-- arXiv DOI: 10.48550/arXiv.2405.10652.
--
-- Classical PDE reference:
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- PURPOSE
-- Formalise the exact order-theoretic last step in the proposed Galerkin
-- strategy. A selected sequence of finite truncations obeys one uniform
-- terminal bound. The physical quantity is bounded by the selected
-- approximation plus an error sequence tending to zero. Thus the physical
-- quantity lies within every positive epsilon of the uniform bound.
--
-- To obtain an exact continuation threshold one retains an explicit positive
-- margin between the uniform finite bound and that threshold, then chooses a
-- sufficiently late Galerkin stage whose error lies below the margin.
--
-- This corrects the invalid shortcut "physical <= one fixed approximation".
-- No compactness, convergence, or lower semicontinuity is manufactured.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
import Data.Nat.Properties as ℕₚ
open import Data.Rational.Base using (ℚ; _/_; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚₚ

import DASHI.Physics.Closure.NSTriadKNLuoTerminalInteractionDepletionTransferExact as Limit

record GalerkinUniformLimitData : Set where
  constructor galerkin-uniform-limit-data
  field
    approximationSquared : Nat → ℚ
    physicalLimitSquared uniformTerminalBound : ℚ

    uniformApproximationBound :
      (cutoff : Nat) →
      approximationSquared cutoff ≤ uniformTerminalBound

    selectedCutoff : Nat → Nat
    approximationError : Nat → ℚ

    errorTendsToZero :
      Limit.TendsToZero approximationError

    physicalBelowSelectedApproximationPlusError :
      (stage : Nat) →
      physicalLimitSquared
      ≤ approximationSquared (selectedCutoff stage)
        + approximationError stage

open GalerkinUniformLimitData public

record WithinEveryPositiveError
  (value upper : ℚ) : Set where
  constructor within-every-positive-error
  field
    withinError :
      (epsilon : ℚ) →
      Int.+ 0 / 1 < epsilon →
      value ≤ upper + epsilon

open WithinEveryPositiveError public

galerkinUniformBoundUpToEveryPositiveError :
  (dataSet : GalerkinUniformLimitData) →
  WithinEveryPositiveError
    (physicalLimitSquared dataSet)
    (uniformTerminalBound dataSet)
galerkinUniformBoundUpToEveryPositiveError dataSet =
  within-every-positive-error
    (λ epsilon epsilonPositive →
      let
        errorTail =
          Limit.eventuallySmall
            (errorTendsToZero dataSet)
            epsilon
            epsilonPositive

        stage = Limit.cutoff errorTail

        selectedApproximationBound :
          approximationSquared dataSet (selectedCutoff dataSet stage)
          ≤ uniformTerminalBound dataSet
        selectedApproximationBound =
          uniformApproximationBound dataSet (selectedCutoff dataSet stage)

        errorBound :
          approximationError dataSet stage ≤ epsilon
        errorBound =
          Limit.tailBound errorTail stage ℕₚ.≤-refl

        summedBound :
          approximationSquared dataSet (selectedCutoff dataSet stage)
            + approximationError dataSet stage
          ≤ uniformTerminalBound dataSet + epsilon
        summedBound =
          ℚₚ.+-mono-≤ selectedApproximationBound errorBound
      in
      ℚₚ.≤-trans
        (physicalBelowSelectedApproximationPlusError dataSet stage)
        summedBound)

record GalerkinContinuationMarginData : Set where
  constructor galerkin-continuation-margin-data
  field
    limitData : GalerkinUniformLimitData
    continuationThreshold margin : ℚ

    marginPositive : Int.+ 0 / 1 < margin

    uniformBoundPlusMarginBelowThreshold :
      uniformTerminalBound limitData + margin
      ≤ continuationThreshold

open GalerkinContinuationMarginData public

physicalLimitBelowContinuationThresholdWithMargin :
  (dataSet : GalerkinContinuationMarginData) →
  physicalLimitSquared (limitData dataSet)
  ≤ continuationThreshold dataSet
physicalLimitBelowContinuationThresholdWithMargin dataSet =
  let
    approximateBound =
      withinError
        (galerkinUniformBoundUpToEveryPositiveError (limitData dataSet))
        (margin dataSet)
        (marginPositive dataSet)
  in
  ℚₚ.≤-trans
    approximateBound
    (uniformBoundPlusMarginBelowThreshold dataSet)
