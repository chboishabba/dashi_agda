module DASHI.Biology.TernaryCanonicalOrientationExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic

------------------------------------------------------------------------
-- Aristotle-return theorem surface.
--
-- Ported theorem shape from the supplied archive:
--   Lean/Integration/TernaryHub.lean
--
-- The Lean owner shows that several independent ternary carriers transport to
-- one balanced Z/3 hub and that polarity inversion transports to negation.
-- This Agda surface records the repo-native finite consequence used by the
-- conscious-access stack: once neutral state and polarity are fixed, the
-- remaining convention is orientation.

data TernaryOrientation : Set where
  canonicalOrientation : TernaryOrientation
  reversedOrientation : TernaryOrientation

orientTrit : TernaryOrientation → Triadic.KernelTrit → Triadic.KernelTrit
orientTrit canonicalOrientation t = t
orientTrit reversedOrientation t = Triadic.negateTrit t

orientNeutralFixed :
  (o : TernaryOrientation) →
  orientTrit o Triadic.zeroTrit ≡ Triadic.zeroTrit
orientNeutralFixed canonicalOrientation = refl
orientNeutralFixed reversedOrientation = refl

orientCommutesWithNegation :
  (o : TernaryOrientation) (t : Triadic.KernelTrit) →
  orientTrit o (Triadic.negateTrit t)
  ≡
  Triadic.negateTrit (orientTrit o t)
orientCommutesWithNegation canonicalOrientation t = refl
orientCommutesWithNegation reversedOrientation Triadic.negativeTrit = refl
orientCommutesWithNegation reversedOrientation Triadic.zeroTrit = refl
orientCommutesWithNegation reversedOrientation Triadic.positiveTrit = refl

orientInvolutive :
  (o : TernaryOrientation) (t : Triadic.KernelTrit) →
  orientTrit o (orientTrit o t) ≡ t
orientInvolutive canonicalOrientation t = refl
orientInvolutive reversedOrientation = Triadic.negateTritInvolutive

canonicalPositiveStaysPositive :
  orientTrit canonicalOrientation Triadic.positiveTrit
  ≡ Triadic.positiveTrit
canonicalPositiveStaysPositive = refl

reversedPositiveBecomesNegative :
  orientTrit reversedOrientation Triadic.positiveTrit
  ≡ Triadic.negativeTrit
reversedPositiveBecomesNegative = refl

------------------------------------------------------------------------
-- A convention-covariant observer carries its orientation explicitly.

record OrientedTernaryObserver : Set₁ where
  constructor orientedTernaryObserver
  field
    Observation : Set
    orientation : TernaryOrientation
    readCanonical : Triadic.KernelTrit → Observation

open OrientedTernaryObserver public

readOriented :
  (O : OrientedTernaryObserver) →
  Triadic.KernelTrit → Observation O
readOriented O t = readCanonical O (orientTrit (orientation O) t)

record TernaryOrientationBoundary : Set where
  constructor ternaryOrientationBoundary
  field
    signConventionIsIntrinsicPhysics : Bool
    signConventionIsIntrinsicPhysicsIsFalse :
      signConventionIsIntrinsicPhysics ≡ false

    neutralStateChangesUnderOrientation : Bool
    neutralStateChangesUnderOrientationIsFalse :
      neutralStateChangesUnderOrientation ≡ false

canonicalTernaryOrientationBoundary : TernaryOrientationBoundary
canonicalTernaryOrientationBoundary =
  ternaryOrientationBoundary false refl false refl
