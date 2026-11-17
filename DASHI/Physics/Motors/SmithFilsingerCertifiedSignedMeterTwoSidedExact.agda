module DASHI.Physics.Motors.SmithFilsingerCertifiedSignedMeterTwoSidedExact where

-- F10/F13/F15: TWO-SIDED signed rational meter uncertainty.
--
-- Reuse the canonical proof-carrying finite-sum upper enclosure TWICE:
-- original signed residual and its additive inverse. Do NOT invent a
-- new interval solver or pretend the Nat integer-quantum no-go vanished.
--
-- Each error certificate contains actual finite terms and certified
-- aggregate containment. The NEGATIVE residual and its exact pairing
-- to the original signed residual must be independently established.
-- Physical calibration / original device / Maxwell integration are
-- not derived merely by this record. No invented data or simulation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Data.Rational.Base as ℚ
import DASHI.Core.ProofCarryingFiniteSumEnclosureExact as Cert
import DASHI.Physics.Motors.SmithFilsingerCertifiedSignedMeterResidualExact as Meter
import DASHI.Physics.Motors.SmithFilsingerSpaceTimePoyntingTelescopeExact as SpaceTime

record TwoSidedMeterCertificate
  (w : SpaceTime.FiniteSpaceTimeWindow) : Set₁ where
  field
    original : Meter.SelectedOriginalCertifiedMeter w

    negativeCertificate :
      Cert.ProofCarryingFiniteSumEnclosure Meter.rationalAdditiveCarrier
    negativeUpper :
      Cert.ProofCarryingFiniteSumUpperEnclosure
        Meter.rationalAdditiveCarrier negativeCertificate

    -- This equality is substantive: it pairs *the same signed residual
    -- observations* across positive/negative certificates, not merely
    -- two unrelated bounds with reassuring labels.
    exactOppositeErrorSum :
      Cert.foldScalars Meter.rationalAdditiveCarrier
        (Cert.mapValues
          (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm
            (Meter.SelectedOriginalCertifiedMeter.certificate original))
          (Cert.ProofCarryingFiniteSumEnclosure.terms
            (Meter.SelectedOriginalCertifiedMeter.certificate original)))
      ≡ ℚ.- (Cert.foldScalars Meter.rationalAdditiveCarrier
          (Cert.mapValues
            (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm
              negativeCertificate)
            (Cert.ProofCarryingFiniteSumEnclosure.terms
              negativeCertificate)))

    -- Both canonical upper certificate relations must be the real
    -- RATIONAL order, or have proved sound inclusion into that order.
    positiveUpperIsRationalOrder :
      ∀ {x y : ℚ.ℚ} →
      Cert.ProofCarryingFiniteSumUpperEnclosure.lessOrEqual
        (Meter.SelectedOriginalCertifiedMeter.upper original) x y →
      ℚ._≤_ x y

    negativeUpperIsRationalOrder :
      ∀ {x y : ℚ.ℚ} →
      Cert.ProofCarryingFiniteSumUpperEnclosure.lessOrEqual
        negativeUpper x y →
      ℚ._≤_ x y

    -- These are laws of the chosen ordered rational carrier. They
    -- are explicit proof obligations rather than arbitrary relations.
    negativeReversesOrder :
      ∀ {x y : ℚ.ℚ} →
      ℚ._≤_ x y → ℚ._≤_ (ℚ.- y) (ℚ.- x)

    translateOrder :
      ∀ {x y base : ℚ.ℚ} →
      ℚ._≤_ x y →
      ℚ._≤_ (base ℚ.+ x) (base ℚ.+ y)

open TwoSidedMeterCertificate public

-- The canonical positive error upper becomes a receiver upper.
twoSidedOriginalReceiverUpper :
  (w : SpaceTime.FiniteSpaceTimeWindow)
  (d : TwoSidedMeterCertificate w) →
  ℚ._≤_ (SpaceTime.FiniteSpaceTimeWindow.usefulReceiverWork w)
    (Meter.SelectedOriginalCertifiedMeter.observedNetTerminalWork
       (original d)
      ℚ.+ Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper
        (Meter.SelectedOriginalCertifiedMeter.upper (original d)))
twoSidedOriginalReceiverUpper w d =
  subst
    (λ x → ℚ._≤_ x upperValue)
    (sym (Meter.originalUsefulReceiverEqualsMeterPlusResidual
      w (original d)))
    (translateOrder d
      (positiveUpperIsRationalOrder d
        (Meter.originalSignedResidualBelowCertifiedUpper
          w (original d))))
  where
    upperValue : ℚ.ℚ
    upperValue =
      Meter.SelectedOriginalCertifiedMeter.observedNetTerminalWork
        (original d)
      ℚ.+ Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper
        (Meter.SelectedOriginalCertifiedMeter.upper (original d))

    subst : (P : ℚ.ℚ → Set) {x y : ℚ.ℚ} →
      x ≡ y → P x → P y
    subst P refl p = p

-- The reverse/error certificate becomes a lower receiver bound:
--      observed - upper(negative residual) <= original physical work.
-- An UNSIGNED absolute-error model is NOT required.
twoSidedOriginalReceiverLower :
  (w : SpaceTime.FiniteSpaceTimeWindow)
  (d : TwoSidedMeterCertificate w) →
  ℚ._≤_
    (Meter.SelectedOriginalCertifiedMeter.observedNetTerminalWork
       (original d)
      ℚ.+ (ℚ.- Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper
        (negativeUpper d)))
    (SpaceTime.FiniteSpaceTimeWindow.usefulReceiverWork w)
twoSidedOriginalReceiverLower w d =
  subst
    (λ x → ℚ._≤_ lowerValue x)
    (sym (Meter.originalUsefulReceiverEqualsMeterPlusResidual
      w (original d)))
    (translateOrder d
      (subst
        (λ x → ℚ._≤_
          (ℚ.- Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper
            (negativeUpper d)) x)
        (sym (exactOppositeErrorSum d))
        (negativeReversesOrder d
          (negativeUpperIsRationalOrder d
            (Cert.finiteSumBelowCertifiedUpper (negativeUpper d))))))
  where
    lowerValue : ℚ.ℚ
    lowerValue =
      Meter.SelectedOriginalCertifiedMeter.observedNetTerminalWork
        (original d)
      ℚ.+ (ℚ.- Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper
        (negativeUpper d))

    subst : (P : ℚ.ℚ → Set) {x y : ℚ.ℚ} →
      x ≡ y → P x → P y
    subst P refl p = p
