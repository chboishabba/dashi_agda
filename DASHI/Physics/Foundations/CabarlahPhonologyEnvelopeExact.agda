module DASHI.Physics.Foundations.CabarlahPhonologyEnvelopeExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- This is an uncertainty envelope induced by the conventional English spelling
-- and comparison with documented southeast-Queensland phonological systems.
-- It is not a reconstruction of a Jarowair or Wakka lexical item.

data InitialVelarHypothesis : Set where
  kLikeVelar : InitialVelarHypothesis
  gLikeVelar : InitialVelarHypothesis

data MedialLabialHypothesis : Set where
  pLikeLabial : MedialLabialHypothesis
  bLikeLabial : MedialLabialHypothesis

data RhoticHypothesis : Set where
  noDistinctRhotic : RhoticHypothesis
  apicalTap : RhoticHypothesis
  apicalTrill : RhoticHypothesis
  retroflexApproximant : RhoticHypothesis

data FinalVowelHypothesis : Set where
  shortFinalA : FinalVowelHypothesis
  longFinalA : FinalVowelHypothesis

record PhonologyEnvelopePoint : Set where
  constructor envelopePoint
  field
    initialVelar : InitialVelarHypothesis
    medialLabial : MedialLabialHypothesis
    rhotic : RhoticHypothesis
    finalVowel : FinalVowelHypothesis

open PhonologyEnvelopePoint public

initialVelarCount : Nat
initialVelarCount = 2

medialLabialCount : Nat
medialLabialCount = 2

rhoticCount : Nat
rhoticCount = 4

finalVowelCount : Nat
finalVowelCount = 2

envelopeProductCount : Nat
envelopeProductCount =
  initialVelarCount
  * medialLabialCount
  * rhoticCount
  * finalVowelCount

envelopeProductCountIsThirtyTwo : envelopeProductCount ≡ 32
envelopeProductCountIsThirtyTwo = refl

------------------------------------------------------------------------
-- The count is a product of uncertainty coordinates, not a claim that all 32
-- points are attested or phonotactically valid words.

kPNoRhoticShort : PhonologyEnvelopePoint
kPNoRhoticShort =
  envelopePoint kLikeVelar pLikeLabial noDistinctRhotic shortFinalA

gPNoRhoticShort : PhonologyEnvelopePoint
gPNoRhoticShort =
  envelopePoint gLikeVelar pLikeLabial noDistinctRhotic shortFinalA

kAndGEnvelopePointsDistinct :
  kPNoRhoticShort ≡ gPNoRhoticShort → ⊥
kAndGEnvelopePointsDistinct ()

data ConventionalToponymForm : Set where
  cabarlahForm : ConventionalToponymForm

renderAsConventionalToponym :
  PhonologyEnvelopePoint → ConventionalToponymForm
renderAsConventionalToponym _ = cabarlahForm

kAndGRenderEqually :
  renderAsConventionalToponym kPNoRhoticShort
  ≡ renderAsConventionalToponym gPNoRhoticShort
kAndGRenderEqually = refl

EnvelopeRenderInjective : Set
EnvelopeRenderInjective =
  (x y : PhonologyEnvelopePoint) →
  renderAsConventionalToponym x ≡ renderAsConventionalToponym y →
  x ≡ y

envelopeRenderIsNotInjective : ¬ EnvelopeRenderInjective
envelopeRenderIsNotInjective injective =
  kAndGEnvelopePointsDistinct
    (injective kPNoRhoticShort gPNoRhoticShort refl)

------------------------------------------------------------------------
-- Orthographic caution flags.  The spelling does not certify voicing, rhotic
-- manner, vowel length, or a final /h/ segment.

record PhonologyEnvelopeBoundary : Set where
  constructor phonologyEnvelopeBoundary
  field
    initialCDeterminesEnglishVoicelessK : Bool
    initialCDeterminesEnglishVoicelessKIsFalse :
      initialCDeterminesEnglishVoicelessK ≡ false

    medialBDeterminesEnglishVoicedB : Bool
    medialBDeterminesEnglishVoicedBIsFalse :
      medialBDeterminesEnglishVoicedB ≡ false

    writtenRDeterminesRhoticManner : Bool
    writtenRDeterminesRhoticMannerIsFalse :
      writtenRDeterminesRhoticManner ≡ false

    finalAhDeterminesLongVowel : Bool
    finalAhDeterminesLongVowelIsFalse :
      finalAhDeterminesLongVowel ≡ false

    finalHDeterminesSourceHPhoneme : Bool
    finalHDeterminesSourceHPhonemeIsFalse :
      finalHDeterminesSourceHPhoneme ≡ false

    finiteEnvelopeIsRecoveredLexicon : Bool
    finiteEnvelopeIsRecoveredLexiconIsFalse :
      finiteEnvelopeIsRecoveredLexicon ≡ false

open PhonologyEnvelopeBoundary public

canonicalPhonologyEnvelopeBoundary : PhonologyEnvelopeBoundary
canonicalPhonologyEnvelopeBoundary =
  phonologyEnvelopeBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
