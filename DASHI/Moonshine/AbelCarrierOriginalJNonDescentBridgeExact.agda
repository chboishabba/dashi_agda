module DASHI.Moonshine.AbelCarrierOriginalJNonDescentBridgeExact where

-- Reuses the pre-existing modular-j no-descent owner, rather than
-- duplicating its theorem. This module intentionally has no --safe
-- pragma: legacy dependency graph must be audited before promotion.

open import Agda.Primitive using (Set; Set₁)
open import Agda.Builtin.Equality using (_≡_)
import DASHI.Moonshine.AbelCarrierFixedLocusTransportExact as Carrier
import DASHI.Moonshine.JInvariant369LevelNonDescentThroughJExact as Existing
import DASHI.Moonshine.JInvariant369PhaseLevelSeparationExact as Separation
import DASHI.Moonshine.JInvariantTetrationAbelModularTransportExact as T

record NoDescentIntake (C : Carrier.AbelCarrier) : Set₁ where
  field
    noTranslationFixedPoint :
      (z : Carrier.Coordinate C) →
      Carrier.translate C z ≡ z → Separation.Empty
    decoder : Carrier.Base C → Carrier.Coordinate C
    decoderEquation : (x : Carrier.Fine C) →
      Carrier.abel C x ≡ decoder (Carrier.observed C x)

open NoDescentIntake public

asOriginalInvariantBaseAttempt :
  (C : Carrier.AbelCarrier) →
  NoDescentIntake C →
  Existing.InvariantBaseTranslationAttempt
    (Carrier.Fine C) (Carrier.Base C) (Carrier.Coordinate C)
asOriginalInvariantBaseAttempt C N = record
  { Existing.InvariantBaseTranslationAttempt.transform = Carrier.step C
  ; Existing.InvariantBaseTranslationAttempt.baseAt = Carrier.observed C
  ; Existing.InvariantBaseTranslationAttempt.baseInvariant =
      Carrier.quotientStepInvariant C
  ; Existing.InvariantBaseTranslationAttempt.fibreAt = Carrier.abel C
  ; Existing.InvariantBaseTranslationAttempt.translateFibre =
      Carrier.translate C
  ; Existing.InvariantBaseTranslationAttempt.translationFixedPointFree =
      noTranslationFixedPoint N
  ; Existing.InvariantBaseTranslationAttempt.fibreTranslates =
      Carrier.abelCommutes C
  ; Existing.InvariantBaseTranslationAttempt.decodeFromBase = decoder N
  ; Existing.InvariantBaseTranslationAttempt.fibreFactorsThroughBase =
      decoderEquation N
  }

originalJNoDescentConsumed :
  (C : Carrier.AbelCarrier) →
  (N : NoDescentIntake C) →
  (x : Carrier.Fine C) →
  Separation.Empty
originalJNoDescentConsumed C N x =
  Existing.fibreCannotDescendThroughInvariantBase
    (asOriginalInvariantBaseAttempt C N) x

-- Existing abstract T/j transport embeds into the carrier-parametric
-- construction without asserting that its coordinate is C or Q_p.

asCarrier : T.AbelModularExpSystem → Carrier.AbelCarrier
asCarrier S = record
  { Carrier.AbelCarrier.Fine = T.Point S
  ; Carrier.AbelCarrier.Coordinate = T.Coordinate S
  ; Carrier.AbelCarrier.Base = T.JValue S
  ; Carrier.AbelCarrier.step = T.exponential S
  ; Carrier.AbelCarrier.translate = T.translate S
  ; Carrier.AbelCarrier.abel = T.abel S
  ; Carrier.AbelCarrier.quotient = T.modularJ S
  ; Carrier.AbelCarrier.abelCommutes = T.abelExponentialLaw S
  ; Carrier.AbelCarrier.quotientInvariant = T.modularTranslationLaw S
  }

originalTransportEqualsCarrierTransport :
  (S : T.AbelModularExpSystem) →
  (w : T.Point S) →
  T.transportedJ S w ≡ Carrier.observed (asCarrier S) w
originalTransportEqualsCarrierTransport S w = Agda.Builtin.Equality.refl
