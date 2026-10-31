module DASHI.Moonshine.OggPrimeFourierWindingExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Formalise the exact finite part of the 3Blue1Brown-style winding picture
-- for the canonical fifteen Ogg / Monster prime lanes without inventing a
-- second prime carrier or pretending that Agda already owns an analytic
-- complex exponential over arbitrary real frequency.
--
-- Existing owners reused here:
--
-- * MoonshinePrimeLaneReceiptSurface: the canonical fifteen Ogg prime lanes;
-- * OggPrimeControlMatrixExact: the five odd-prime controls <= 71 that are
--   explicitly externally non-Ogg;
-- * TriadicDepthOneCharacters / C3FourierConjugationExact: exact symbolic
--   third roots of unity and Fourier conjugation;
-- * SSP15AffineC3TranslationExact: existing proof that a genuine C3 action is
--   already present on part of the SSP15 finite data.
--
-- New content is only the winding/contrast observation layer:
--
--   O(ω) = sum_{p in Ogg} exp(i p ω)
--   X(ω) = sum_{q in nonOgg} exp(i q ω)
--   C(ω) = O(ω) - 3 X(ω).
--
-- At ω = 0 the coefficient sum is exactly 15 - 3*5 = 0.  In this Agda
-- owner we prove that finite centering theorem and the exact C3 root-of-unity
--/chirality specialization.  The arbitrary-real analytic exponential is left
-- to a prover/carrier that actually owns it (mirrored in Lean).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Integer using (ℤ; +_; -[1+_]) renaming (_+_ to _+ℤ_)
open import Data.List.Base using (List; []; _∷_; map)

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Moonshine.C3FourierConjugationExact as Fourier
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.SSP15AffineC3TranslationExact as Affine
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- Canonical support sets are imported, not reconstructed semantically.

oggPrimeNats : List Nat
oggPrimeNats = Lane.canonicalMonsterPrimeLaneNats

nonOggPrimeNats : List Nat
nonOggPrimeNats = map Matrix.primeLevel Matrix.nonOggPrimeControls

nonOggPrimeNatsExact :
  nonOggPrimeNats ≡ 37 ∷ 43 ∷ 53 ∷ 61 ∷ 67 ∷ []
nonOggPrimeNatsExact = refl

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ xs) = 1 + listCount xs

oggPrimeCount : Nat
oggPrimeCount = listCount oggPrimeNats

nonOggPrimeCount : Nat
nonOggPrimeCount = listCount nonOggPrimeNats

oggPrimeCountIsFifteen : oggPrimeCount ≡ 15
oggPrimeCountIsFifteen = refl

nonOggPrimeCountIsFive : nonOggPrimeCount ≡ 5
nonOggPrimeCountIsFive = refl

------------------------------------------------------------------------
-- Centered Ogg-vs-control Fourier contrast.
--
-- Each Ogg lane carries coefficient +1 and each of the five non-Ogg controls
-- carries coefficient -3.  The zero-frequency/DC coefficient therefore
-- vanishes exactly.  This is the finite algebraic fact behind removing the
-- trivial size imbalance before looking for phase coherence.

contrastCoefficients : List ℤ
contrastCoefficients =
  + 1 ∷ + 1 ∷ + 1 ∷ + 1 ∷ + 1
  ∷ + 1 ∷ + 1 ∷ + 1 ∷ + 1 ∷ + 1
  ∷ + 1 ∷ + 1 ∷ + 1 ∷ + 1 ∷ + 1
  ∷ -[1+ 2 ] ∷ -[1+ 2 ] ∷ -[1+ 2 ] ∷ -[1+ 2 ] ∷ -[1+ 2 ]
  ∷ []

sumℤ : List ℤ → ℤ
sumℤ [] = + 0
sumℤ (x ∷ xs) = x +ℤ sumℤ xs

contrastCoefficientCount : listCount contrastCoefficients ≡ 20
contrastCoefficientCount = refl

contrastCoefficientsSumZero : sumℤ contrastCoefficients ≡ + 0
contrastCoefficientsSumZero = refl

------------------------------------------------------------------------
-- Exact C3 specialization of the winding phase.
--
-- At ω = 2π/3, exp(i p ω) depends only on p mod 3.  We retain only the exact
-- symbolic root-of-unity index here.  `phase0`, `phase1`, `phase2` are the
-- repository's exact 1, ζ, ζ² carrier.

phaseIndex3 : Lane.MonsterPrimeLane → Nat
phaseIndex3 Lane.p2 = 2
phaseIndex3 Lane.p3 = 0
phaseIndex3 Lane.p5 = 2
phaseIndex3 Lane.p7 = 1
phaseIndex3 Lane.p11 = 2
phaseIndex3 Lane.p13 = 1
phaseIndex3 Lane.p17 = 2
phaseIndex3 Lane.p19 = 1
phaseIndex3 Lane.p23 = 2
phaseIndex3 Lane.p29 = 2
phaseIndex3 Lane.p31 = 1
phaseIndex3 Lane.p41 = 2
phaseIndex3 Lane.p47 = 2
phaseIndex3 Lane.p59 = 2
phaseIndex3 Lane.p71 = 2

phaseFromIndex3 : Nat → C3.C3Phase
phaseFromIndex3 0 = Fourier.one
phaseFromIndex3 1 = Fourier.zeta
phaseFromIndex3 _ = Fourier.zetaSquared

positiveC3Phase : Lane.MonsterPrimeLane → C3.C3Phase
positiveC3Phase p = phaseFromIndex3 (phaseIndex3 p)

positiveC3PhaseExact :
  (p : Lane.MonsterPrimeLane) →
  positiveC3Phase p ≡ phaseFromIndex3 (phaseIndex3 p)
positiveC3PhaseExact p = refl

negativeC3Phase : Lane.MonsterPrimeLane → C3.C3Phase
negativeC3Phase p = Fourier.inversePhase (positiveC3Phase p)

negativeWindingIsConjugation :
  (p : Lane.MonsterPrimeLane) →
  negativeC3Phase p ≡ Fourier.inversePhase (positiveC3Phase p)
negativeWindingIsConjugation p = refl

negativeWindingIsInvolutive :
  (p : Lane.MonsterPrimeLane) →
  Fourier.inversePhase (negativeC3Phase p) ≡ positiveC3Phase p
negativeWindingIsInvolutive p = Fourier.inversePhaseInvolutive (positiveC3Phase p)

------------------------------------------------------------------------
-- Cross-pollination receipt: this winding specialization consumes, rather
-- than replaces, the repo's pre-existing exact C3 SSP action.

existingAffineC3ActionReused : Bool
existingAffineC3ActionReused = true

existingAffineC3ActionReusedIsTrue : existingAffineC3ActionReused ≡ true
existingAffineC3ActionReusedIsTrue = refl

p5AffinePhaseStartsAtFourierOne :
  Affine.mobileModePhase Affine.fiveMode ≡ Fourier.one
p5AffinePhaseStartsAtFourierOne = refl

p5To17AffineStepIsMultiplyByZeta :
  Affine.mobileModePhase (Affine.advance12 Affine.fiveMode)
  ≡ C3.multiplyPhase Fourier.zeta (Affine.mobileModePhase Affine.fiveMode)
p5To17AffineStepIsMultiplyByZeta = Affine.advance12IsMultiplyByZeta Affine.fiveMode

------------------------------------------------------------------------
-- Promotion firewalls.

analyticFourierCompletionClaimed : Bool
analyticFourierCompletionClaimed = false

analyticFourierCompletionClaimedIsFalse :
  analyticFourierCompletionClaimed ≡ false
analyticFourierCompletionClaimedIsFalse = refl

arbitraryModulusCyclotomicFamilyClaimed : Bool
arbitraryModulusCyclotomicFamilyClaimed = false

arbitraryModulusCyclotomicFamilyClaimedIsFalse :
  arbitraryModulusCyclotomicFamilyClaimed ≡ false
arbitraryModulusCyclotomicFamilyClaimedIsFalse = refl

radialPrimeSpiralIdentifiedWithFourierSum : Bool
radialPrimeSpiralIdentifiedWithFourierSum = false

radialPrimeSpiralIdentifiedWithFourierSumIsFalse :
  radialPrimeSpiralIdentifiedWithFourierSum ≡ false
radialPrimeSpiralIdentifiedWithFourierSumIsFalse = refl

oggPrimeFourierPatternExplainsMonstrousMoonshine : Bool
oggPrimeFourierPatternExplainsMonstrousMoonshine = false

oggPrimeFourierPatternExplainsMonstrousMoonshineIsFalse :
  oggPrimeFourierPatternExplainsMonstrousMoonshine ≡ false
oggPrimeFourierPatternExplainsMonstrousMoonshineIsFalse = refl
