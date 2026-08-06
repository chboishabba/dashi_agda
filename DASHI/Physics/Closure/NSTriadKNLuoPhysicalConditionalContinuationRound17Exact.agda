module DASHI.Physics.Closure.NSTriadKNLuoPhysicalConditionalContinuationRound17Exact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin;
-- Raphaël Danchin.
-- Bony DOI: 10.24033/asens.1404.
-- Bahouri-Chemin-Danchin DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- PURPOSE
-- Close the physical conditional continuation route rather than stopping at a
-- finite theorem receipt.  Every Galerkin cutoff supplies the checked annular
-- four-class estimate
--
--   |N_q^N|² <= (1/4096) E_q².
--
-- The physical interaction is controlled by a selected Galerkin subsequence
-- plus an error tending to zero.  An explicit positive margin then upgrades the
-- uniform finite bound to the requested physical continuation threshold.
--
-- The theorem remains conditional on the concrete analytic inputs contained
-- in the annular data and on the stated Galerkin convergence estimate.  It does
-- not claim unconditional Navier-Stokes regularity.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_; _+_; _≤_; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoAnnularFourClassContinuationExact as Annular
import DASHI.Physics.Closure.NSTriadKNLuoRound14SquaredFourClassClosureExact as Four
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicGalerkinFourClassContinuationExact as Continue
import DASHI.Physics.Closure.NSTriadKNLuoGalerkinUniformLimitContinuationExact as Limit
import DASHI.Physics.Closure.NSTriadKNLuoTerminalInteractionDepletionTransferExact as Vanish

finiteInteractionSquared :
  ∀ {shell} →
  Annular.AnnularContinuationData shell →
  ℚ
finiteInteractionSquared dataSet =
  L2.square
    (Four.totalInteraction
      (Annular.asFourClassBudget
        (Annular.fourClassData dataSet)))

record PhysicalConditionalContinuationData (shell : Nat) : Set₁ where
  constructor physical-conditional-continuation-data
  field
    finiteData :
      Nat → Annular.AnnularContinuationData shell

    physicalInteractionSquared : ℚ
    outputEnvelopeSquared : ℚ
    continuationThreshold margin : ℚ

    selectedCutoff : Nat → Nat
    approximationError : Nat → ℚ

    errorTendsToZero :
      Vanish.TendsToZero approximationError

    outputEnvelopeStable :
      (cutoff : Nat) →
      Annular.outputEnvelopeSquared
        (Annular.fourClassData (finiteData cutoff))
      ≡ outputEnvelopeSquared

    physicalBelowSelectedFinitePlusError :
      (stage : Nat) →
      physicalInteractionSquared
      ≤ finiteInteractionSquared
          (finiteData (selectedCutoff stage))
        + approximationError stage

    marginPositive :
      Int.+ 0 / 1 < margin

    finiteBoundPlusMarginBelowThreshold :
      Continue.oneOver4096 * outputEnvelopeSquared + margin
      ≤ continuationThreshold

open PhysicalConditionalContinuationData public

finiteUniformBound :
  ∀ {shell}
    (dataSet : PhysicalConditionalContinuationData shell)
    (cutoff : Nat) →
  finiteInteractionSquared (finiteData dataSet cutoff)
  ≤ Continue.oneOver4096 * outputEnvelopeSquared dataSet
finiteUniformBound dataSet cutoff
  rewrite
    outputEnvelopeStable dataSet cutoff =
  Annular.annularTerminalSmallnessSquared
    (finiteData dataSet cutoff)

asGalerkinUniformLimitData :
  ∀ {shell} →
  PhysicalConditionalContinuationData shell →
  Limit.GalerkinUniformLimitData
asGalerkinUniformLimitData dataSet =
  Limit.galerkin-uniform-limit-data
    (λ cutoff →
      finiteInteractionSquared (finiteData dataSet cutoff))
    (physicalInteractionSquared dataSet)
    (Continue.oneOver4096 * outputEnvelopeSquared dataSet)
    (finiteUniformBound dataSet)
    (selectedCutoff dataSet)
    (approximationError dataSet)
    (errorTendsToZero dataSet)
    (physicalBelowSelectedFinitePlusError dataSet)

asContinuationMarginData :
  ∀ {shell} →
  PhysicalConditionalContinuationData shell →
  Limit.GalerkinContinuationMarginData
asContinuationMarginData dataSet =
  Limit.galerkin-continuation-margin-data
    (asGalerkinUniformLimitData dataSet)
    (continuationThreshold dataSet)
    (margin dataSet)
    (marginPositive dataSet)
    (finiteBoundPlusMarginBelowThreshold dataSet)

physicalConditionalContinuation :
  ∀ {shell}
    (dataSet : PhysicalConditionalContinuationData shell) →
  physicalInteractionSquared dataSet
  ≤ continuationThreshold dataSet
physicalConditionalContinuation dataSet =
  Limit.physicalLimitBelowContinuationThresholdWithMargin
    (asContinuationMarginData dataSet)
