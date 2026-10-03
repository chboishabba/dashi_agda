module DASHI.ComputerScience.TekumParsedBandMembershipExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base as ℤ using (+_)
import Data.Integer.Properties as ℤP
import Data.Nat.Properties as NatP
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; ½; -_; _+_; _*_; _<_; Positive; positive)
import Data.Rational.Properties as ℚP
open ℚP using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)
open import Data.Rational.Unnormalised.Base as ℚᵘ
  using (ℚᵘ; 1ℚᵘ; _/_; _+_; _≃_; *≡*)
import Data.Rational.Unnormalised.Properties as ℚᵘP
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.ComputerScience.TekumAnchorCodecExact as Anchor
import DASHI.ComputerScience.TekumFractionRationalRangeExact as Fraction
import DASHI.ComputerScience.TekumSignificandRangeExact as Sig
import DASHI.ComputerScience.TekumTriadicScaleExact as Scale
import DASHI.ComputerScience.TekumExponentBandExact as Band
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumOrdinaryFactorizationExact as Factor

------------------------------------------------------------------------
-- ACTUAL PARSER MAGNITUDE IN THE SOURCE EXPONENT BAND
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

zeroBelowHalf : 0ℚ < ½
zeroBelowHalf = toWitness {a? = 0ℚ <? ½} _

parsedMagnitudePositive :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  0ℚ < parsedMagnitude parsed
parsedMagnitudePositive parsed
  rewrite parsedMagnitudeIsSourceFormula parsed =
  let
    sigBand = Sig.significandStrictBand (Source.fractionLST parsed)

    sigPositive : 0ℚ < Sig.significand (Source.fractionLST parsed)
    sigPositive = ℚP.<-trans zeroBelowHalf (proj₁ sigBand)

    instance scalePositive : Positive (Scale.triadicScale (Factor.sourceExponentInteger parsed))
        scalePositive = positive (Scale.triadicScalePositive (Factor.sourceExponentInteger parsed))
  in
  ℚP.*-monoʳ-<-pos
    (Scale.triadicScale (Factor.sourceExponentInteger parsed))
    sigPositive

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

------------------------------------------------------------------------
-- Literal parser value = external sign applied to the positive magnitude.
------------------------------------------------------------------------

zeroTimes : (x : ℚ) → 0ℚ ℚ.* x ≡ 0ℚ
zeroTimes = solve-∀

applyRationalSignMul :
  (s : Anchor.TekumSign) (x y : ℚ) →
  Factor.applyRationalSign s x ℚ.* y
  ≡ Factor.applyRationalSign s (x ℚ.* y)
applyRationalSignMul Anchor.negativeSign x y =
  sym (ℚP.neg-distribˡ-* x y)
applyRationalSignMul Anchor.zeroSign x y = zeroTimes y
applyRationalSignMul Anchor.positiveSign x y = refl

parsedOrdinaryRationalIsSignedMagnitude :
  ∀ {extra r payload}
  (word : Data.Vec.Vec DASHI.Algebra.Trit.Trit (8 + extra))
  (parsed : Source.ParsedPayload extra r payload) →
  Source.ordinaryRationalFromParsed word parsed
  ≡ Factor.applyRationalSign (Source.signOfWord word) (parsedMagnitude parsed)
parsedOrdinaryRationalIsSignedMagnitude word parsed =
  trans
    (Factor.parsedOrdinaryCanonicalProduct word parsed)
    (trans
      (cong
        (λ s → s ℚ.* Factor.canonicalSourceScale parsed)
        (Factor.canonicalSignedSignificandIsApplySign word parsed))
      (applyRationalSignMul
        (Source.signOfWord word)
        (Factor.canonicalUnsignedSignificand parsed)
        (Factor.canonicalSourceScale parsed)))
