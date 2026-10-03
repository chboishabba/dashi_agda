module DASHI.ComputerScience.TekumParsedBandMembershipExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base as ℤ using (+_)
import Data.Integer.Properties as ℤP
import Data.Nat.Properties as NatP
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _<_; Positive; positive)
import Data.Rational.Properties as ℚP
open import Data.Rational.Unnormalised.Base as ℚᵘ
  using (ℚᵘ; 1ℚᵘ; _/_; _+_; _≃_; *≡*)
import Data.Rational.Unnormalised.Properties as ℚᵘP
open import Relation.Binary.PropositionalEquality using (cong₂; trans)
open import Relation.Binary.PropositionalEquality.≡-Reasoning

import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.ComputerScience.TekumFractionRationalRangeExact as Fraction
import DASHI.ComputerScience.TekumSignificandRangeExact as Sig
import DASHI.ComputerScience.TekumTriadicScaleExact as Scale
import DASHI.ComputerScience.TekumExponentBandExact as Band
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumOrdinaryFactorizationExact as Factor

------------------------------------------------------------------------
-- ACTUAL PARSER MAGNITUDE IN THE SOURCE EXPONENT BAND
--
-- This file closes the semantic gap between the parser's literal exact
-- significand and the already-proved abstract source band 1/2 < 1+f < 3/2.
------------------------------------------------------------------------

rawSourceFraction :
  ∀ {extra r payload} →
  Source.ParsedPayload extra r payload → ℚᵘ
rawSourceFraction parsed =
  let instance denominatorNonZero =
        Factor.balancedPow3NonZero (Factor.sourceFractionWidth parsed)
  in BT.toInteger (BT.eval (Source.fractionLST parsed))
     ℚᵘ./ BT.pow3 (Factor.sourceFractionWidth parsed)

rawSourceFractionIsExistingRaw :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  rawSourceFraction parsed ℚᵘ.≃ Fraction.rawFraction (Source.fractionLST parsed)
rawSourceFractionIsExistingRaw parsed
  rewrite Fraction.fractionDenominatorIsPowerThree (Factor.sourceFractionWidth parsed) =
  ℚᵘP.≃-refl

rawUnsignedSignificandOnePlusFraction :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  Factor.rawUnsignedSourceSignificand parsed
  ℚᵘ.≃ (1ℚᵘ ℚᵘ.+ rawSourceFraction parsed)
rawUnsignedSignificandOnePlusFraction parsed
  rewrite NatP.*-identityˡ (BT.pow3 (Factor.sourceFractionWidth parsed))
        | ℤP.*-identityˡ (+ (BT.pow3 (Factor.sourceFractionWidth parsed)))
        | ℤP.*-identityʳ (BT.toInteger (BT.eval (Source.fractionLST parsed))) =
  ℚᵘ.*≡* refl

canonicalSourceFraction :
  ∀ {extra r payload} →
  Source.ParsedPayload extra r payload → ℚ
canonicalSourceFraction parsed = ℚ.fromℚᵘ (rawSourceFraction parsed)

canonicalSourceFractionIsExisting :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  canonicalSourceFraction parsed
  ≡ Fraction.canonicalFraction (Source.fractionLST parsed)
canonicalSourceFractionIsExisting parsed =
  ℚP.fromℚᵘ-cong (rawSourceFractionIsExistingRaw parsed)

rawOneCanonical : ℚ.fromℚᵘ 1ℚᵘ ≡ 1ℚ
rawOneCanonical = refl

canonicalUnsignedSignificandIsSourceSignificand :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  Factor.canonicalUnsignedSignificand parsed
  ≡ Sig.significand (Source.fractionLST parsed)
canonicalUnsignedSignificandIsSourceSignificand parsed =
  begin
    Factor.canonicalUnsignedSignificand parsed
      ≡⟨ ℚP.fromℚᵘ-cong
           (rawUnsignedSignificandOnePlusFraction parsed) ⟩
    ℚ.fromℚᵘ (1ℚᵘ ℚᵘ.+ rawSourceFraction parsed)
      ≡⟨ Factor.fromRawSum 1ℚᵘ (rawSourceFraction parsed) ⟩
    ℚ.fromℚᵘ 1ℚᵘ ℚ.+ canonicalSourceFraction parsed
      ≡⟨ cong₂ ℚ._+_ rawOneCanonical
           (canonicalSourceFractionIsExisting parsed) ⟩
    1ℚ ℚ.+ Fraction.canonicalFraction (Source.fractionLST parsed)
      ∎

parsedMagnitude :
  ∀ {extra r payload} →
  Source.ParsedPayload extra r payload → ℚ
parsedMagnitude parsed =
  Factor.canonicalUnsignedSignificand parsed
  ℚ.* Factor.canonicalSourceScale parsed

parsedMagnitudeIsSourceFormula :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  parsedMagnitude parsed
  ≡ Sig.significand (Source.fractionLST parsed)
      ℚ.* Scale.triadicScale (Factor.sourceExponentInteger parsed)
parsedMagnitudeIsSourceFormula parsed
  rewrite canonicalUnsignedSignificandIsSourceSignificand parsed
        | Factor.canonicalSourceScaleIsTriadicScale parsed = refl

parsedMagnitudePositive :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  0ℚ < parsedMagnitude parsed
parsedMagnitudePositive parsed
  rewrite parsedMagnitudeIsSourceFormula parsed =
  let
    sigBand = Sig.significandStrictBand (Source.fractionLST parsed)

    sigPositive : 0ℚ < Sig.significand (Source.fractionLST parsed)
    sigPositive = ℚP.<-trans Band.bandLowerPositiveZero (proj₁ sigBand)

    instance scalePositive : Positive (Scale.triadicScale (Factor.sourceExponentInteger parsed))
        scalePositive = positive (Scale.triadicScalePositive (Factor.sourceExponentInteger parsed))
  in
  ℚP.*-monoʳ-<-pos
    (Scale.triadicScale (Factor.sourceExponentInteger parsed))
    sigPositive
  where
  -- The lower band coefficient is positive, hence 0 < 1/2.
  Band.bandLowerPositiveZero : 0ℚ < Sig.significand (Source.fractionLST parsed)
  Band.bandLowerPositiveZero =
    ℚP.<-trans
      (Band.bandLowerPositive (Factor.sourceExponentInteger parsed))
      (ℚP.*-monoʳ-<-pos
        (Scale.triadicScale (Factor.sourceExponentInteger parsed))
        (proj₁ (Sig.significandStrictBand (Source.fractionLST parsed))))

parsedMagnitudeInExponentBand :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  Band.InBand (Factor.sourceExponentInteger parsed) (parsedMagnitude parsed)
parsedMagnitudeInExponentBand parsed
  rewrite parsedMagnitudeIsSourceFormula parsed =
  lower , upper
  where
  exponent = Factor.sourceExponentInteger parsed
  sigBand = Sig.significandStrictBand (Source.fractionLST parsed)

  instance
    scalePositive : Positive (Scale.triadicScale exponent)
    scalePositive = positive (Scale.triadicScalePositive exponent)

  lower :
    Band.bandLower exponent
    < Sig.significand (Source.fractionLST parsed) ℚ.* Scale.triadicScale exponent
  lower =
    ℚP.*-monoʳ-<-pos (Scale.triadicScale exponent) (proj₁ sigBand)

  upper :
    Sig.significand (Source.fractionLST parsed) ℚ.* Scale.triadicScale exponent
    < Band.bandUpper exponent
  upper =
    ℚP.*-monoʳ-<-pos (Scale.triadicScale exponent) (proj₂ sigBand)
