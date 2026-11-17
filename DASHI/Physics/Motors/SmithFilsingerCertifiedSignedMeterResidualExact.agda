module DASHI.Physics.Motors.SmithFilsingerCertifiedSignedMeterResidualExact where

-- F10/F13/F15: ACTUAL finite signed meter error accounting in ℚ.
-- No global exact rational/real -> Nat signed-quantum conversion exists
-- with nonzero odd unit preservation (see SignedMeterQuantisationNoGo).
--
-- Reuse: Core.ProofCarryingFiniteSumEnclosureExact (generic certified
-- finite-sum upper); SpaceTimePoyntingTelescopeExact (source-window owner);
-- Rational ring normaliser; do NOT implement another interval framework.
--
-- The original source/terminal identification and physical calibration
-- remain independent, contentful premises. There is NO fitted value,
-- no measurement, no simulation and no unlicensed environmental source.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (trans; sym; cong)
import Data.Rational.Base as ℚ
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Core.ProofCarryingFiniteSumEnclosureExact as Cert
import DASHI.Physics.Motors.SmithFilsingerSpaceTimePoyntingTelescopeExact as SpaceTime

rationalAdditiveCarrier : Cert.FiniteAdditiveCarrier
rationalAdditiveCarrier = record
  { Cert.Scalar = ℚ.ℚ
  ; Cert.zeroS = ℚ.0ℚ
  ; Cert.addS = ℚ._+_
  }

foldRational : ∀ {A : Set} → (A → ℚ.ℚ) → List A → ℚ.ℚ
foldRational {A} f xs =
  Cert.foldScalars rationalAdditiveCarrier (Cert.mapValues f xs)

-- A per-term signed meter reading and its separately identified
-- residual on the SAME signed physical work carrier.
record FiniteSignedMeterWork
  (certificate : Cert.ProofCarryingFiniteSumEnclosure
    rationalAdditiveCarrier) : Set₁ where
  private
    module C = Cert.ProofCarryingFiniteSumEnclosure certificate
  field
    physicalWork : C.Term → ℚ.ℚ
    meteredWork : C.Term → ℚ.ℚ
    -- This equation is independently calibrated for EACH term;
    -- its sign and units are not obtained by naming an error field.
    perTermCalibration :
      (term : C.Term) →
      physicalWork term ≡
        meteredWork term ℚ.+ C.evaluateTerm term

open FiniteSignedMeterWork public

-- Exactly additive error propagation, with NO rounding-to-Nat step.
-- A signed negative residual is allowed, unlike an unsigned abs-budget.
signedResidualsTelescope :
  (certificate : Cert.ProofCarryingFiniteSumEnclosure
     rationalAdditiveCarrier)
  (meter : FiniteSignedMeterWork certificate)
  (xs : List (Cert.ProofCarryingFiniteSumEnclosure.Term certificate)) →
  foldRational (physicalWork meter) xs
    ≡ foldRational (meteredWork meter) xs ℚ.+
        foldRational
          (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm certificate) xs
signedResidualsTelescope certificate meter [] =
  ℚRing.solve-∀
signedResidualsTelescope certificate meter (x ∷ xs)
  rewrite perTermCalibration meter x
        | signedResidualsTelescope certificate meter xs =
  ℚRing.solve-∀
    (meteredWork meter x)
    (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm certificate x)
    (foldRational (meteredWork meter) xs)
    (foldRational
      (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm certificate) xs)

-- A contentful selected original terminal work observation: the actual
-- full 4D rational signed Poynting window and the finite source-meter
-- samples are identified by a supplied physical trace/calibration law.
record SelectedOriginalCertifiedMeter
  (window : SpaceTime.FiniteSpaceTimeWindow) : Set₁ where
  field
    certificate :
      Cert.ProofCarryingFiniteSumEnclosure rationalAdditiveCarrier
    meter : FiniteSignedMeterWork certificate

    -- THESE are substantive provenance/clock/geometry/units obligations,
    -- not manufactured by the generic finite-sum algebra above.
    physicalTermsAreOriginalReceiver :
      foldRational (physicalWork meter)
        (Cert.ProofCarryingFiniteSumEnclosure.terms certificate)
      ≡ SpaceTime.FiniteSpaceTimeWindow.usefulReceiverWork window

    observedNetTerminalWork : ℚ.ℚ
    meteredTermsAreActualReading :
      foldRational (meteredWork meter)
        (Cert.ProofCarryingFiniteSumEnclosure.terms certificate)
      ≡ observedNetTerminalWork

    -- The upper certificate must refer to the SAME per-term error list.
    -- It is a proof-bearing, not freely chosen, interval upper receipt.
    upper :
      Cert.ProofCarryingFiniteSumUpperEnclosure
        rationalAdditiveCarrier certificate

open SelectedOriginalCertifiedMeter public

-- The physically identified signed rational receiver work is the
-- original reported terminal reading PLUS the actual finite error
-- aggregate. This is a theorem, not an independent ledger assumption.
originalUsefulReceiverEqualsMeterPlusResidual :
  (window : SpaceTime.FiniteSpaceTimeWindow)
  (m : SelectedOriginalCertifiedMeter window) →
  SpaceTime.FiniteSpaceTimeWindow.usefulReceiverWork window
    ≡ observedNetTerminalWork m ℚ.+
      Cert.foldScalars rationalAdditiveCarrier
        (Cert.mapValues
          (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm
            (certificate m))
          (Cert.ProofCarryingFiniteSumEnclosure.terms
            (certificate m)))
originalUsefulReceiverEqualsMeterPlusResidual window m =
  trans (sym (physicalTermsAreOriginalReceiver m))
    (trans
      (signedResidualsTelescope (certificate m) (meter m)
        (Cert.ProofCarryingFiniteSumEnclosure.terms (certificate m)))
      (cong
        (λ x → x ℚ.+
          Cert.foldScalars rationalAdditiveCarrier
            (Cert.mapValues
              (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm
                (certificate m))
              (Cert.ProofCarryingFiniteSumEnclosure.terms
                (certificate m))))
        (meteredTermsAreActualReading m)))

-- Reuse canonical finite-sum *upper* certificate on the SAME residual
-- aggregate. No invented interval condition, no assertion that the
-- independently measured error bound is small, and no physical promotion.
originalSignedResidualBelowCertifiedUpper :
  (window : SpaceTime.FiniteSpaceTimeWindow)
  (m : SelectedOriginalCertifiedMeter window) →
  Cert.ProofCarryingFiniteSumUpperEnclosure.lessOrEqual (upper m)
    (Cert.foldScalars rationalAdditiveCarrier
      (Cert.mapValues
        (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm (certificate m))
        (Cert.ProofCarryingFiniteSumEnclosure.terms (certificate m))))
    (Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper (upper m))
originalSignedResidualBelowCertifiedUpper window m =
  Cert.finiteSumBelowCertifiedUpper (upper m)


-- The upper endpoint is now transported all the way from the signed
-- residual sum to the physically SAME ORIGINAL receiver work, but ONLY
-- when the certified order is additive. This is a proof-bearing extra
-- property, not a free assertion that every arbitrary relation is ≤.
record SignedMeterUpperMonotonicity
  (window : SpaceTime.FiniteSpaceTimeWindow)
  (m : SelectedOriginalCertifiedMeter window) : Set₁ where
  private
    _≼_ =
      Cert.ProofCarryingFiniteSumUpperEnclosure.lessOrEqual (upper m)
  field
    upperStableUnderObservedMeterWork :
      ∀ {a b : ℚ.ℚ} →
      a ≼ b →
      (observedNetTerminalWork m ℚ.+ a)
        ≼ (observedNetTerminalWork m ℚ.+ b)

-- One-sided rigorous signed meter/work inequality. The residual bound
-- may be negative or positive: the ordered theorem does not declare
-- that measured work came from the environment, and does not assume
-- the external field has an original-device physical witness.
originalReceiverBelowObservedPlusCertifiedResidual :
  (window : SpaceTime.FiniteSpaceTimeWindow)
  (m : SelectedOriginalCertifiedMeter window)
  (law : SignedMeterUpperMonotonicity window m) →
  Cert.ProofCarryingFiniteSumUpperEnclosure.lessOrEqual (upper m)
    (SpaceTime.FiniteSpaceTimeWindow.usefulReceiverWork window)
    (observedNetTerminalWork m ℚ.+
      Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper (upper m))
originalReceiverBelowObservedPlusCertifiedResidual window m law =
  subst
    (λ z →
      Cert.ProofCarryingFiniteSumUpperEnclosure.lessOrEqual (upper m)
        z
        (observedNetTerminalWork m ℚ.+
          Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper (upper m)))
    (sym (originalUsefulReceiverEqualsMeterPlusResidual window m))
    (SignedMeterUpperMonotonicity.upperStableUnderObservedMeterWork law
      (originalSignedResidualBelowCertifiedUpper window m))
  where
    subst :
      {A : Set} (P : A → Set) {x y : A} →
      x ≡ y → P x → P y
    subst P refl proof = proof
