{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityGaussianProjectionSourceBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Total
import DASHI.Physics.Foundations.CMP119AntigravityRichBrillouinRationalGaussianProjectionExact as Gaussian
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- TOTAL CMP109 BETA WELD != GAUSSIAN PROJECTION WELD
--
-- The preferred trajectory constructor owns
--
--   source beta = rational beta_Z + rational beta_int.
--
-- That theorem fixes the total one-step coefficient but does not select a
-- decomposition of the total coefficient into Gaussian and interaction parts.
-- S4's rich Brillouin bypass needs the stronger Gaussian same-object theorem
--
--   rich coefficient ~= embed(rational beta_Z).
--
-- This module makes the non-implication explicit in the API so future callers
-- cannot discharge the Gaussian seam with the total source recurrence alone.
------------------------------------------------------------------------

record TotalAndGaussianSourceBoundary
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (weld : Total.CMP109LiteralPlaquetteCoefficientWeld trajectory)
    (rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ) : Set₁ where
  field
    gaussianProjection :
      Gaussian.RichBrillouinRationalGaussianProjection
        (Total.asPhysicalRunningCouplingData weld)
        rich

open TotalAndGaussianSourceBoundary public

totalSourceBetaWeldDeterminesGaussianProjection : Bool
totalSourceBetaWeldDeterminesGaussianProjection = false

gaussianProjectionIsIndependentSourcePayment : Bool
gaussianProjectionIsIndependentSourcePayment = true

totalSourceBetaWeldDeterminesGaussianProjectionIsFalse :
  totalSourceBetaWeldDeterminesGaussianProjection ≡ false
totalSourceBetaWeldDeterminesGaussianProjectionIsFalse = refl

gaussianProjectionIsIndependentSourcePaymentIsTrue :
  gaussianProjectionIsIndependentSourcePayment ≡ true
gaussianProjectionIsIndependentSourcePaymentIsTrue = refl

gaussianProjectionSourceBoundaryLevel : ProofLevel
gaussianProjectionSourceBoundaryLevel = machineChecked

gaussianProjectionPhysicalIdentificationLevel : ProofLevel
gaussianProjectionPhysicalIdentificationLevel = conditional
