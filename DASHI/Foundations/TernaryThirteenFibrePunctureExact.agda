{-# OPTIONS --safe #-}
module DASHI.Foundations.TernaryThirteenFibrePunctureExact where

------------------------------------------------------------------------
-- H1.02-04: a literal last-coordinate zero section and nonzero
-- complement, distinct from puncturing the ONE global all-zero word.
-- The semantic original central-completion carrier has not yet been
-- identified with these words; no semantic identity is claimed here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Foundations.TernaryThirteenFibreSplitExact as F

zeroTritWord : (n : Nat) → F.TritWord n
zeroTritWord zero = tt
zeroTritWord (suc n) = F.neutral , zeroTritWord n

lastTrit : F.TritWord 13 → F.Trit
lastTrit word =
  proj₁ (proj₂ (F.ternaryThirteenSplitTwelvePlusOne word))

singleTrit : F.Trit → F.TritWord 1
singleTrit t = t , tt

-- 12-axis zero section into a fully *unpunctured* 13-word.
centralCoordinateZeroSection :
  F.TritWord 12 → F.TritWord 13
centralCoordinateZeroSection xs =
  F.ternaryThirteenJoinTwelvePlusOne
    (xs , singleTrit F.neutral)

centralCoordinateZeroSectionSplit :
  (xs : F.TritWord 12) →
  F.ternaryThirteenSplitTwelvePlusOne
    (centralCoordinateZeroSection xs)
  ≡ (xs , singleTrit F.neutral)
centralCoordinateZeroSectionSplit xs =
  F.ternaryThirteenSplitRoundTrip
    (xs , singleTrit F.neutral)

centralCoordinateZeroSectionLastNeutral :
  (xs : F.TritWord 12) →
  lastTrit (centralCoordinateZeroSection xs) ≡ F.neutral
centralCoordinateZeroSectionLastNeutral xs =
  cong (λ pair → proj₁ (proj₂ pair))
    (centralCoordinateZeroSectionSplit xs)

-- The last-coordinate puncture has exactly two trit choices.
data NonzeroTrit : Set where
  negativeNonzero positiveNonzero : NonzeroTrit

nonzeroTrit : NonzeroTrit → F.Trit
nonzeroTrit negativeNonzero = F.negative
nonzeroTrit positiveNonzero = F.positive

nonzeroIsNotNeutral :
  (value : NonzeroTrit) →
  ¬ (nonzeroTrit value ≡ F.neutral)
nonzeroIsNotNeutral negativeNonzero ()
nonzeroIsNotNeutral positiveNonzero ()

nonzeroFromNotNeutral :
  (t : F.Trit) →
  ¬ (t ≡ F.neutral) → NonzeroTrit
nonzeroFromNotNeutral F.negative neq = negativeNonzero
nonzeroFromNotNeutral F.neutral neq = ⊥-elim (neq refl)
nonzeroFromNotNeutral F.positive neq = positiveNonzero

nonzeroFromNotNeutralRoundTrip :
  (p : NonzeroTrit) →
  nonzeroFromNotNeutral (nonzeroTrit p)
    (nonzeroIsNotNeutral p) ≡ p
nonzeroFromNotNeutralRoundTrip negativeNonzero = refl
nonzeroFromNotNeutralRoundTrip positiveNonzero = refl

nonzeroToFromNotNeutral :
  (t : F.Trit) (neq : ¬ (t ≡ F.neutral)) →
  nonzeroTrit (nonzeroFromNotNeutral t neq) ≡ t
nonzeroToFromNotNeutral F.negative neq = refl
nonzeroToFromNotNeutral F.neutral neq = ⊥-elim (neq refl)
nonzeroToFromNotNeutral F.positive neq = refl

LastPuncture13 : Set
LastPuncture13 = F.TritWord 12 × NonzeroTrit

centralCoordinatePunctureComplement :
  LastPuncture13 → F.TritWord 13
centralCoordinatePunctureComplement (xs , p) =
  F.ternaryThirteenJoinTwelvePlusOne
    (xs , singleTrit (nonzeroTrit p))

centralCoordinatePunctureSplit :
  (x : F.TritWord 13) →
  ¬ (lastTrit x ≡ F.neutral) →
  LastPuncture13
centralCoordinatePunctureSplit x neq
  with F.ternaryThirteenSplitTwelvePlusOne x
... | xs , (t , tt) =
  xs , nonzeroFromNotNeutral t neq

centralPunctureLastNonzero :
  (xs : LastPuncture13) →
  ¬ (lastTrit (centralCoordinatePunctureComplement xs) ≡ F.neutral)
centralPunctureLastNonzero (xs , p) eq =
  nonzeroIsNotNeutral p
    (trans
      (sym
        (cong (λ q → proj₁ (proj₂ q))
          (F.ternaryThirteenSplitRoundTrip
            (xs , singleTrit (nonzeroTrit p)))))
      eq)

-- Full left-inverse on the genuine two-state complement.
centralPunctureSplitRoundTrip :
  (xs : LastPuncture13) →
  centralCoordinatePunctureSplit
    (centralCoordinatePunctureComplement xs)
    (centralPunctureLastNonzero xs)
  ≡ xs
centralPunctureSplitRoundTrip (xs , negativeNonzero)
  rewrite F.ternaryThirteenSplitRoundTrip
    (xs , singleTrit F.negative) = refl
centralPunctureSplitRoundTrip (xs , positiveNonzero)
  rewrite F.ternaryThirteenSplitRoundTrip
    (xs , singleTrit F.positive) = refl

-- Full right-inverse at the underlying 13-word level. We do not
-- need proof irrelevance for the witness that the suffix is nonzero.
centralPunctureJoinRoundTrip :
  (x : F.TritWord 13)
  (neq : ¬ (lastTrit x ≡ F.neutral)) →
  centralCoordinatePunctureComplement
    (centralCoordinatePunctureSplit x neq) ≡ x
centralPunctureJoinRoundTrip x neq
  with F.ternaryThirteenSplitTwelvePlusOne x
... | xs , (F.negative , tt) =
  F.ternaryThirteenJoinRoundTrip x
... | xs , (F.neutral , tt) =
  ⊥-elim (neq refl)
... | xs , (F.positive , tt) =
  F.ternaryThirteenJoinRoundTrip x

-- Puncturing the global origin instead is a *different* predicate.
GlobalOriginPuncture13 : Set
GlobalOriginPuncture13 =
  Σ (F.TritWord 13) (λ word → ¬ (word ≡ zeroTritWord 13))

originalThirteenOriginIsNeutral :
  lastTrit (zeroTritWord 13) ≡ F.neutral
originalThirteenOriginIsNeutral = refl

-- Every last-coordinate puncture is globally nonzero.
-- The reverse implication is false: a word with nonzero first
-- coordinate and neutral last coordinate is globally nonzero.
lastCoordinatePunctureImpliesGlobalPuncture :
  LastPuncture13 → GlobalOriginPuncture13
lastCoordinatePunctureImpliesGlobalPuncture xs =
  centralCoordinatePunctureComplement xs ,
  λ eq →
    centralPunctureLastNonzero xs
      (trans
        (cong lastTrit eq)
        originalThirteenOriginIsNeutral)

-- A witness distinguishing the *two* puncture notions.
firstNonzeroThenZero : F.TritWord 13
firstNonzeroThenZero =
  F.positive , zeroTritWord 12

firstNonzeroThenZeroIsNotOrigin :
  ¬ (firstNonzeroThenZero ≡ zeroTritWord 13)
firstNonzeroThenZeroIsNotOrigin ()

firstNonzeroThenZeroLastNeutral :
  lastTrit firstNonzeroThenZero ≡ F.neutral
firstNonzeroThenZeroLastNeutral = refl

globalPunctureDoesNotForceLastPuncture :
  ((x : F.TritWord 13) →
    ¬ (x ≡ zeroTritWord 13) →
    ¬ (lastTrit x ≡ F.neutral)) →
  ⊥
globalPunctureDoesNotForceLastPuncture alleged =
  alleged firstNonzeroThenZero
    firstNonzeroThenZeroIsNotOrigin
    firstNonzeroThenZeroLastNeutral
