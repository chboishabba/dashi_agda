{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySelectedInverseCouplingNoGoExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Foundations.CMP119AntigravityWeakCouplingTraceEnergyNoGoExact as NoGo
import DASHI.Physics.Foundations.CMP119AntigravityLorentzianF2ContinuationExact as Continuation
import DASHI.Physics.Foundations.CMP119AntigravityTraceCoefficientInverseCouplingFirewallExact as Coeff

------------------------------------------------------------------------
-- AG-S4 / SELECTED CMP119 COUPLING VALUE -> WEAK-COUPLING NO-GO
--
-- The RG slope 11/(12 pi^2) cannot fill this record.  A selected same-object
-- inverse-coupling VALUE is required.  In normalized rational coordinates the
-- SU(2) anomaly threshold is 11/24 before the common 1/pi^2 normalization.
------------------------------------------------------------------------

record SelectedInverseCouplingNoGoCertificate
    (continuation : Continuation.LorentzianF2ContinuationReceipt) : Set₁ where
  field
    anomalyMagnitude : ℚ
    inverseCouplingValue : ℚ
    nonnegativeMargin : ℚ

    anomalyMagnitudeNonnegative :
      0ℚ ≤ anomalyMagnitude

    marginNonnegative :
      0ℚ ≤ nonnegativeMargin

    anomalyMagnitudeIsSU2ThresholdHalf :
      (1ℚ + 1ℚ) * anomalyMagnitude
      ≡ Coeff.selectedWeakCouplingNoGoThresholdRational

    selectedInverseCouplingDecomposition :
      inverseCouplingValue
      ≡
      (1ℚ + 1ℚ) * anomalyMagnitude + nonnegativeMargin

    -- Same-object provenance: the value is the inverse coupling multiplying
    -- the Lorentzian E^2+B^2 energy density on this selected CMP119 source.
    selectedInverseCouplingSameObject : Set
    selectedInverseCouplingSameObjectWitness :
      selectedInverseCouplingSameObject

open SelectedInverseCouplingNoGoCertificate public

asWeakCouplingYMTraceEnergyData :
  (continuation : Continuation.LorentzianF2ContinuationReceipt) →
  SelectedInverseCouplingNoGoCertificate continuation →
  NoGo.WeakCouplingYMTraceEnergyData
asWeakCouplingYMTraceEnergyData continuation certificate = record
  { NoGo.WeakCouplingYMTraceEnergyData.kappa =
      anomalyMagnitude certificate
  ; NoGo.WeakCouplingYMTraceEnergyData.margin =
      nonnegativeMargin certificate
  ; NoGo.WeakCouplingYMTraceEnergyData.electricSquare =
      Continuation.electricSquare continuation
  ; NoGo.WeakCouplingYMTraceEnergyData.magneticSquare =
      Continuation.magneticSquare continuation
  ; NoGo.WeakCouplingYMTraceEnergyData.kappaNonnegative =
      anomalyMagnitudeNonnegative certificate
  ; NoGo.WeakCouplingYMTraceEnergyData.marginNonnegative =
      marginNonnegative certificate
  ; NoGo.WeakCouplingYMTraceEnergyData.electricSquareNonnegative =
      Continuation.electricSquareNonnegative continuation
  ; NoGo.WeakCouplingYMTraceEnergyData.magneticSquareNonnegative =
      Continuation.magneticSquareNonnegative continuation
  }

selectedInverseCouplingCertificateBlocksNegativeActiveStress :
  (continuation : Continuation.LorentzianF2ContinuationReceipt) →
  (certificate : SelectedInverseCouplingNoGoCertificate continuation) →
  0ℚ ≤
  NoGo.activeStress
    (asWeakCouplingYMTraceEnergyData continuation certificate)
selectedInverseCouplingCertificateBlocksNegativeActiveStress
    continuation certificate =
  NoGo.activeStressNonnegative
    (asWeakCouplingYMTraceEnergyData continuation certificate)

selectedCMP119InverseCouplingCertificateLevel : Bool
selectedCMP119InverseCouplingCertificateLevel = false

selectedCMP119InverseCouplingCertificateStillRequired : Bool
selectedCMP119InverseCouplingCertificateStillRequired = true
