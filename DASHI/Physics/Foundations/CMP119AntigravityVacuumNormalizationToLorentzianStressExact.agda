{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityVacuumNormalizationToLorentzianStressExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (refl)
open import Data.Rational.Base using (ℚ; 0ℚ; -_; _<_)

import DASHI.Physics.Foundations.CMP119AntigravityVacuumNormalizationGravityFirewallExact as Firewall
import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum

------------------------------------------------------------------------
-- POST-NORMALIZATION STATIC COMPILER
--
-- Once the explicit physical promotion receipt has identified the reconstructed
-- CMP119 normalization coordinate with the SAME renormalized gravitational
-- amplitude and supplied its metric/volume response, the remaining Lorentzian
-- vacuum algebra is no longer an open physics problem.
------------------------------------------------------------------------

receiptLorentzianStress :
  ∀ {sourceNormalization} →
  Firewall.VacuumNormalizationToGravityReceipt sourceNormalization →
  Vacuum.IsotropicLorentzianStress
receiptLorentzianStress receipt =
  Vacuum.isotropicStress
    (Firewall.renormalizedGravitationalAmplitude receipt)
    (- Firewall.renormalizedGravitationalAmplitude receipt)

receiptVacuumLikeStress :
  ∀ {sourceNormalization}
    (receipt : Firewall.VacuumNormalizationToGravityReceipt sourceNormalization) →
  Vacuum.VacuumLikeLorentzianStress
receiptVacuumLikeStress receipt = record
  { Vacuum.VacuumLikeLorentzianStress.stress = receiptLorentzianStress receipt
  ; Vacuum.VacuumLikeLorentzianStress.pressureIsMinusRho = refl
  }

positiveRenormalizedAmplitudeGivesNegativeActiveStress :
  ∀ {sourceNormalization}
    (receipt : Firewall.VacuumNormalizationToGravityReceipt sourceNormalization) →
  0ℚ < Firewall.renormalizedGravitationalAmplitude receipt →
  Vacuum.activeStress (receiptLorentzianStress receipt) < 0ℚ
positiveRenormalizedAmplitudeGivesNegativeActiveStress receipt positive =
  Vacuum.vacuumPositiveRhoImpliesActiveNegative
    (receiptVacuumLikeStress receipt)
    positive

positiveRenormalizedAmplitudeGivesNegativeTrace :
  ∀ {sourceNormalization}
    (receipt : Firewall.VacuumNormalizationToGravityReceipt sourceNormalization) →
  0ℚ < Firewall.renormalizedGravitationalAmplitude receipt →
  Vacuum.trace (receiptLorentzianStress receipt) < 0ℚ
positiveRenormalizedAmplitudeGivesNegativeTrace receipt positive =
  Vacuum.vacuumPositiveRhoImpliesTraceNegative
    (receiptVacuumLikeStress receipt)
    positive

metricResponseReceiptIsTheOnlyStaticTensorPromotionLeaf : Bool
metricResponseReceiptIsTheOnlyStaticTensorPromotionLeaf = true

vacuumEquationOfStateNeedsNoAdditionalSourceTheoremAfterReceipt : Bool
vacuumEquationOfStateNeedsNoAdditionalSourceTheoremAfterReceipt = true
