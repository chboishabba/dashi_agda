module DASHI.Foundations.Base369PolyphaseCharacters where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import Base369 using
  ( TriTruth
  ; tri-low
  ; tri-mid
  ; tri-high
  )
open import DASHI.Foundations.Base369TriTruthField using
  ( triZero
  ; triOne
  ; triAdd
  ; triNeg
  ; triMul
  ; triDistribˡ
  )

------------------------------------------------------------------------
-- Symbolic exponents for the three irreducible character sectors of C3.
--
-- A genuine complex character has the form
--   chi_m(k) = exp(2 pi i m k / 3).
-- This finite module checks the exponent arithmetic m*k mod 3 exactly.
-- Mapping those exponents to complex roots of unity remains behind the
-- explicit analytic boundary below.

data C3Sequence : Set where
  zeroSequence : C3Sequence
  positiveSequence : C3Sequence
  negativeSequence : C3Sequence

sequenceExponent : C3Sequence → TriTruth
sequenceExponent zeroSequence = triZero
sequenceExponent positiveSequence = triOne
sequenceExponent negativeSequence = triNeg triOne

characterExponent3 : C3Sequence → TriTruth → TriTruth
characterExponent3 mode phase =
  triMul (sequenceExponent mode) phase

characterExponent3-additive :
  (mode : C3Sequence) →
  (x y : TriTruth) →
  characterExponent3 mode (triAdd x y) ≡
  triAdd
    (characterExponent3 mode x)
    (characterExponent3 mode y)
characterExponent3-additive mode x y =
  triDistribˡ (sequenceExponent mode) x y

------------------------------------------------------------------------
-- Exact exponent tables.

zeroSequence-at-low :
  characterExponent3 zeroSequence tri-low ≡ tri-low
zeroSequence-at-low = refl

zeroSequence-at-mid :
  characterExponent3 zeroSequence tri-mid ≡ tri-low
zeroSequence-at-mid = refl

zeroSequence-at-high :
  characterExponent3 zeroSequence tri-high ≡ tri-low
zeroSequence-at-high = refl

positiveSequence-at-low :
  characterExponent3 positiveSequence tri-low ≡ tri-low
positiveSequence-at-low = refl

positiveSequence-at-mid :
  characterExponent3 positiveSequence tri-mid ≡ tri-mid
positiveSequence-at-mid = refl

positiveSequence-at-high :
  characterExponent3 positiveSequence tri-high ≡ tri-high
positiveSequence-at-high = refl

negativeSequence-at-low :
  characterExponent3 negativeSequence tri-low ≡ tri-low
negativeSequence-at-low = refl

negativeSequence-at-mid :
  characterExponent3 negativeSequence tri-mid ≡ tri-high
negativeSequence-at-mid = refl

negativeSequence-at-high :
  characterExponent3 negativeSequence tri-high ≡ tri-mid
negativeSequence-at-high = refl

------------------------------------------------------------------------
-- Sequence labels retain the engineering reading without identifying it
-- with an imported electrical theorem.

sequenceLabel : C3Sequence → String
sequenceLabel zeroSequence = "zero/common sequence"
sequenceLabel positiveSequence = "positive/counterclockwise sequence"
sequenceLabel negativeSequence = "negative/clockwise sequence"

record C3CharacterReceipt : Set where
  constructor mkC3CharacterReceipt
  field
    mode : C3Sequence
    exponent : TriTruth
    exponentMatchesMode : exponent ≡ sequenceExponent mode
    additiveExponentLaw :
      (x y : TriTruth) →
      characterExponent3 mode (triAdd x y) ≡
      triAdd
        (characterExponent3 mode x)
        (characterExponent3 mode y)
    engineeringLabel : String

c3CharacterReceipt : C3Sequence → C3CharacterReceipt
c3CharacterReceipt mode =
  mkC3CharacterReceipt
    mode
    (sequenceExponent mode)
    refl
    (characterExponent3-additive mode)
    (sequenceLabel mode)

zeroSequenceReceipt : C3CharacterReceipt
zeroSequenceReceipt = c3CharacterReceipt zeroSequence

positiveSequenceReceipt : C3CharacterReceipt
positiveSequenceReceipt = c3CharacterReceipt positiveSequence

negativeSequenceReceipt : C3CharacterReceipt
negativeSequenceReceipt = c3CharacterReceipt negativeSequence

------------------------------------------------------------------------
-- Complex/analytic promotion boundary.

record PolyphaseCharacterAnalyticBoundary : Set where
  constructor mkPolyphaseCharacterAnalyticBoundary
  field
    finiteExponentArithmeticChecked : Bool
    complexRootOfUnityRealisationPromoted : Bool
    complexRootOfUnityRealisationPromotedIsFalse :
      complexRootOfUnityRealisationPromoted ≡ false
    FourierReconstructionPromoted : Bool
    FourierReconstructionPromotedIsFalse :
      FourierReconstructionPromoted ≡ false
    interpretation : String

polyphaseCharacterAnalyticBoundary :
  PolyphaseCharacterAnalyticBoundary
polyphaseCharacterAnalyticBoundary =
  mkPolyphaseCharacterAnalyticBoundary
    true
    false
    refl
    false
    refl
    "The C3 exponent table and additive law are checked; complex roots of unity, DFT reconstruction, and physical symmetrical-component authority require separate scalar and engineering bridges"
