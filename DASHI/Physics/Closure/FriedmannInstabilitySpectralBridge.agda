module DASHI.Physics.Closure.FriedmannInstabilitySpectralBridge where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.FriedmannInstabilitySaddleReceipt as Authority
import DASHI.Physics.Closure.FriedmannSTVEigenvalueSignKernel as Spectrum

------------------------------------------------------------------------
-- Proof-shaped bridge from the sourced Friedmann theorem boundary to the
-- concrete STV eigenvalue sign kernel.
--
-- This bridge deliberately proves less than the paper's cosmological prose:
--
--   * the authority-backed saddle statement is present;
--   * the exact gauge-fixed sign pattern is internally represented;
--   * the unique surviving negative mode occurs at STV order n = 2;
--   * no dark-energy, LCDM, continuum-existence, or observational promotion
--     follows from that spectral fact alone.

record FriedmannInstabilitySpectralBridge : Set where
  field
    sourcedSaddleBoundary :
      Authority.friedmannUnstableSaddlePoint
        Authority.canonicalFriedmannInstabilitySaddleReceipt
      ≡ true

    spectralKernel : Spectrum.GaugeFixedSTVSpectralKernel

    orderTwoBModeNegative :
      Spectrum.Negative
        (Spectrum.gaugeFixedEigenvalue Spectrum.bTwo)

    orderTwoBModeUnique :
      (m : Spectrum.GaugeFixedMode Spectrum.orderTwo) ->
      Spectrum.Negative (Spectrum.gaugeFixedEigenvalue m) ->
      m ≡ Spectrum.bTwo

    allHigherGaugeFixedModesPositive :
      {k : Nat} ->
      (m : Spectrum.GaugeFixedMode (Spectrum.higher k)) ->
      Spectrum.Positive (Spectrum.gaugeFixedEigenvalue m)

    darkEnergyRemovalNotDerived :
      Authority.darkEnergyRemoved
        Authority.canonicalFriedmannInstabilitySaddleReceipt
      ≡ false

    LCDMFalsificationNotDerived :
      Authority.LCDMFalsified
        Authority.canonicalFriedmannInstabilitySaddleReceipt
      ≡ false

    cosmologyPromotionRemainsFailClosed :
      Authority.cosmologyPromoted
        Authority.canonicalFriedmannInstabilitySaddleReceipt
      ≡ false

canonicalFriedmannInstabilitySpectralBridge :
  FriedmannInstabilitySpectralBridge
canonicalFriedmannInstabilitySpectralBridge =
  record
    { sourcedSaddleBoundary =
        Authority.friedmannInstabilitySaddlePointAuthorityBacked
    ; spectralKernel =
        Spectrum.canonicalGaugeFixedSTVSpectralKernel
    ; orderTwoBModeNegative =
        Spectrum.orderTwoBIsNegative
    ; orderTwoBModeUnique =
        Spectrum.orderTwoBIsUniqueNegative
    ; allHigherGaugeFixedModesPositive =
        Spectrum.gaugeFixedHigherPositive
    ; darkEnergyRemovalNotDerived =
        Authority.friedmannInstabilityDoesNotRemoveDarkEnergyHere
    ; LCDMFalsificationNotDerived =
        Authority.friedmannInstabilityDoesNotFalsifyLCDMHere
    ; cosmologyPromotionRemainsFailClosed =
        Authority.friedmannInstabilityCosmologyPromotionStillFailClosed
    }

------------------------------------------------------------------------
-- Direct exported consequences.

friedmannOrderTwoCarriesTheUniqueGaugeFixedNegativeMode :
  (m : Spectrum.GaugeFixedMode Spectrum.orderTwo) ->
  Spectrum.Negative (Spectrum.gaugeFixedEigenvalue m) ->
  m ≡ Spectrum.bTwo
friedmannOrderTwoCarriesTheUniqueGaugeFixedNegativeMode =
  Spectrum.orderTwoBIsUniqueNegative

friedmannHigherOrdersAddNoNegativeGaugeFixedModes :
  {k : Nat} ->
  (m : Spectrum.GaugeFixedMode (Spectrum.higher k)) ->
  Spectrum.Positive (Spectrum.gaugeFixedEigenvalue m)
friedmannHigherOrdersAddNoNegativeGaugeFixedModes =
  Spectrum.gaugeFixedHigherPositive

friedmannSpectralInstabilityDoesNotPromoteCosmology :
  Authority.cosmologyPromoted
    Authority.canonicalFriedmannInstabilitySaddleReceipt
  ≡ false
friedmannSpectralInstabilityDoesNotPromoteCosmology = refl
