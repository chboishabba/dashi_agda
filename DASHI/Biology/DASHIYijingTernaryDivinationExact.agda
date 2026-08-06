module DASHI.Biology.DASHIYijingTernaryDivinationExact where

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic

------------------------------------------------------------------------
-- DASHI/Yijing finite carrier.
--
-- The received Yijing line carrier is binary.  DASHI retains the opposed
-- signs and adds a typed mediating/residual state.  This module therefore
-- treats the binary reading as a context-indexed partial observation of a
-- balanced-ternary substrate rather than identifying the two systems.

powNat : Nat → Nat → Nat
powNat base zero = 1
powNat base (suc n) = base * powNat base n

ternaryStateCount : Nat → Nat
ternaryStateCount = powNat 3

TernaryTrigram : Set
TernaryTrigram = Vec Triadic.KernelTrit 3

TernaryHexagram : Set
TernaryHexagram = Vec Triadic.KernelTrit 6

TernaryNineSheet : Set
TernaryNineSheet = Vec Triadic.KernelTrit 9

ternaryTrigramCountIsTwentySeven : ternaryStateCount 3 ≡ 27
ternaryTrigramCountIsTwentySeven = refl

ternaryHexagramCountIsSevenHundredTwentyNine : ternaryStateCount 6 ≡ 729
ternaryHexagramCountIsSevenHundredTwentyNine = refl

ternaryNineSheetCountIsNineteenThousandSixHundredEightyThree :
  ternaryStateCount 9 ≡ 19683
ternaryNineSheetCountIsNineteenThousandSixHundredEightyThree = refl

canonicalTernaryTrigram : TernaryTrigram
canonicalTernaryTrigram =
  Triadic.negativeTrit vcons
  Triadic.zeroTrit vcons
  Triadic.positiveTrit vcons
  vnil

canonicalTernaryHexagram : TernaryHexagram
canonicalTernaryHexagram =
  Triadic.negativeTrit vcons
  Triadic.zeroTrit vcons
  Triadic.positiveTrit vcons
  Triadic.positiveTrit vcons
  Triadic.zeroTrit vcons
  Triadic.negativeTrit vcons
  vnil

------------------------------------------------------------------------
-- Context-indexed yin/yang observation.

data YinYangObservation : Set where
  yinObservation : YinYangObservation
  yangObservation : YinYangObservation
  unresolvedObservation : YinYangObservation

data SignView : Set where
  directView : SignView
  reversedView : SignView

signInView : SignView → Triadic.KernelTrit → Triadic.KernelTrit
signInView directView x = x
signInView reversedView x = Triadic.negateTrit x

observeYinYang : SignView → Triadic.KernelTrit → YinYangObservation
observeYinYang view x with signInView view x
... | Triadic.negativeTrit = yinObservation
... | Triadic.zeroTrit = unresolvedObservation
... | Triadic.positiveTrit = yangObservation

sameTritCanReverseObservedPolarity :
  observeYinYang directView Triadic.positiveTrit ≡ yangObservation
  ×
  observeYinYang reversedView Triadic.positiveTrit ≡ yinObservation
sameTritCanReverseObservedPolarity = refl , refl

zeroRemainsUnresolvedUnderBothViews :
  observeYinYang directView Triadic.zeroTrit ≡ unresolvedObservation
  ×
  observeYinYang reversedView Triadic.zeroTrit ≡ unresolvedObservation
zeroRemainsUnresolvedUnderBothViews = refl , refl

------------------------------------------------------------------------
-- Moving-line update.  A moving position reverses the opposed sign while the
-- mediating zero is fixed by global inversion.

applyMovingMask :
  ∀ {n : Nat} → Vec Bool n → Vec Triadic.KernelTrit n → Vec Triadic.KernelTrit n
applyMovingMask vnil vnil = vnil
applyMovingMask (false vcons mask) (x vcons xs) =
  x vcons applyMovingMask mask xs
applyMovingMask (true vcons mask) (x vcons xs) =
  Triadic.negateTrit x vcons applyMovingMask mask xs

canonicalMovingMask : Vec Bool 6
canonicalMovingMask =
  false vcons
  false vcons
  true vcons
  false vcons
  false vcons
  true vcons
  vnil

canonicalResultingHexagram : TernaryHexagram
canonicalResultingHexagram =
  Triadic.negativeTrit vcons
  Triadic.zeroTrit vcons
  Triadic.negativeTrit vcons
  Triadic.positiveTrit vcons
  Triadic.zeroTrit vcons
  Triadic.positiveTrit vcons
  vnil

canonicalMovingResultIsExact :
  applyMovingMask canonicalMovingMask canonicalTernaryHexagram
  ≡ canonicalResultingHexagram
canonicalMovingResultIsExact = refl

------------------------------------------------------------------------
-- Predicate-normal-form reading surface.

data ReadingAtom : Set where
  signAtom : Nat → Triadic.KernelTrit → ReadingAtom
  movingAtom : Nat → ReadingAtom
  contextAtom : SignView → ReadingAtom
  correspondenceAtom : Nat → Nat → ReadingAtom
  associativeEvocationAtom : Nat → ReadingAtom
  externalPredictionAtom : Nat → ReadingAtom

data ReadingAuthority : Set where
  structuralAuthority : ReadingAuthority
  associativeAuthority : ReadingAuthority
  externalPredictiveAuthority : ReadingAuthority

record DivinationReading : Set where
  constructor divinationReading
  field
    questionContext : Nat
    initialHexagram : TernaryHexagram
    movingMask : Vec Bool 6
    resultingHexagram : TernaryHexagram
    normalizedAtoms : List ReadingAtom
    authority : ReadingAuthority

open DivinationReading public

canonicalAssociativeReading : DivinationReading
canonicalAssociativeReading =
  divinationReading
    1
    canonicalTernaryHexagram
    canonicalMovingMask
    canonicalResultingHexagram
    (contextAtom directView
      ∷ movingAtom 3
      ∷ movingAtom 6
      ∷ associativeEvocationAtom 1
      ∷ [])
    associativeAuthority

record TernaryDivinationBoundary : Set where
  constructor ternaryDivinationBoundary
  field
    ternaryZeroIsAlwaysSynthesis : Bool
    ternaryZeroIsAlwaysSynthesisIsFalse :
      ternaryZeroIsAlwaysSynthesis ≡ false

    binaryObservationRecoversAllTernaryInformation : Bool
    binaryObservationRecoversAllTernaryInformationIsFalse :
      binaryObservationRecoversAllTernaryInformation ≡ false

    associativeReadingEntailsExternalPrediction : Bool
    associativeReadingEntailsExternalPredictionIsFalse :
      associativeReadingEntailsExternalPrediction ≡ false

    contextualPolarityIsIntrinsicFixedSign : Bool
    contextualPolarityIsIntrinsicFixedSignIsFalse :
      contextualPolarityIsIntrinsicFixedSign ≡ false

open TernaryDivinationBoundary public

canonicalTernaryDivinationBoundary : TernaryDivinationBoundary
canonicalTernaryDivinationBoundary =
  ternaryDivinationBoundary false refl false refl false refl false refl
