module DASHI.Physics.Closure.R2P227729HermitianThirteenPairFourierCodecExact where

------------------------------------------------------------------------
-- REAL FOURIER FIELDS: ONE REAL CENTER + THIRTEEN CONJUGATE PAIRS.
--
-- Reuse source owners:
--   BalancedTernaryAntipodalOrbitExact (C2 action, 14 orbit labels)
--   R2P227729AntipodalThirteenFiveOrbitFourierCutExact
--   R2P227729FourierObserverIncidenceExact
--   C3CubeCyclotomicFourierExact (actual Q(omega) and conjugation)
--
-- New: an exact compact lossless codec for a *hermitian* coefficient
-- field f on integer k∈{-1,0,+1}^3 with f(-k)=conj(f(k)).
--
-- One real rational centre (k=0), and exactly 9+3+1=13 complex-like
-- rational-cyclotomic positive-orbit coefficients.  The original
-- 27 arbitrary complex amplitudes do NOT have this representation.
--
-- This is an exact finite source-written Agda theorem only if the
-- Agda kernel successfully checks it (not yet executed). No FFT4,
-- NS velocity, nonlinear aliasing, Monster 3B or lab clock statement.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Biology.Physical.C3CubeCyclotomicFourierExact as C3
import DASHI.Physics.Closure.R2P2ThreeModeBinaryTernaryNSAliasingCutExact as M
import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as I
import DASHI.Physics.Closure.R2P227729AntipodalThirteenFiveOrbitFourierCutExact as Ant

zeroModeCube : I.ModeCube27
zeroModeCube = I.modeCube M.modeZero M.modeZero M.modeZero

representative : Orbit.AntipodalClass27 → I.ModeCube27
representative Orbit.centre27 = zeroModeCube
representative (Orbit.firstPositive27 b c) =
  I.modeCube M.modePlus (I.sspToMode b) (I.sspToMode c)
representative (Orbit.secondPositive27 c) =
  I.modeCube M.modeZero M.modePlus (I.sspToMode c)
representative Orbit.thirdPositive27 =
  I.modeCube M.modeZero M.modeZero M.modePlus

representativeHasCorrectOrbit :
  (orbit : Orbit.AntipodalClass27) →
  Ant.antipodalClass27 (representative orbit) ≡ orbit
representativeHasCorrectOrbit Orbit.centre27 = refl
representativeHasCorrectOrbit (Orbit.firstPositive27 b c) = refl
representativeHasCorrectOrbit (Orbit.secondPositive27 c) = refl
representativeHasCorrectOrbit Orbit.thirdPositive27 = refl

-- Canonical orientation: look at the FIRST nonzero signed component.
-- Zero itself is canonical. The opposite of a nonzero canonical mode
-- is not canonical, so one complex amplitude represents each pair.
positiveSide : I.ModeCube27 → Bool
positiveSide (I.modeCube M.modePlus b c) = true
positiveSide (I.modeCube M.modeMinus b c) = false
positiveSide (I.modeCube M.modeZero M.modePlus c) = true
positiveSide (I.modeCube M.modeZero M.modeMinus c) = false
positiveSide (I.modeCube M.modeZero M.modeZero M.modePlus) = true
positiveSide (I.modeCube M.modeZero M.modeZero M.modeMinus) = false
positiveSide (I.modeCube M.modeZero M.modeZero M.modeZero) = true

chooseCube : Bool → I.ModeCube27 → I.ModeCube27 → I.ModeCube27
chooseCube true p q = p
chooseCube false p q = q

negatedSSPBackToMode :
  (m : M.ThreeMode) →
  I.sspToMode (Orbit.strictAntipode (M.modeToBalancedSSP m))
    ≡ Ant.negateMode m
negatedSSPBackToMode M.modeMinus = refl
negatedSSPBackToMode M.modeZero = refl
negatedSSPBackToMode M.modePlus = refl

-- The selected representative is either m or -m, selected by
-- the canonical sign. Proof uses the original orbit classifier.
representativeMatchesSelectedOrientation :
  (m : I.ModeCube27) →
  representative (Ant.antipodalClass27 m)
    ≡ chooseCube (positiveSide m) m (Ant.negateCube m)
representativeMatchesSelectedOrientation (I.modeCube M.modePlus b c)
  rewrite I.sspToModeAfterRoundTrip b
        | I.sspToModeAfterRoundTrip c = refl
representativeMatchesSelectedOrientation (I.modeCube M.modeMinus b c)
  rewrite negatedSSPBackToMode b
        | negatedSSPBackToMode c = refl
representativeMatchesSelectedOrientation (I.modeCube M.modeZero M.modePlus c)
  rewrite I.sspToModeAfterRoundTrip c = refl
representativeMatchesSelectedOrientation (I.modeCube M.modeZero M.modeMinus c)
  rewrite negatedSSPBackToMode c = refl
representativeMatchesSelectedOrientation
  (I.modeCube M.modeZero M.modeZero M.modePlus) = refl
representativeMatchesSelectedOrientation
  (I.modeCube M.modeZero M.modeZero M.modeMinus) = refl
representativeMatchesSelectedOrientation
  (I.modeCube M.modeZero M.modeZero M.modeZero) = refl

record PackedHermitian27 : Set where
  field
    -- One real scalar is enough at the unique zero frequency.
    centreReal : ℚ
    -- Original quotient firstPositive27 b c carries exactly 3²=9.
    firstPositiveCoefficient : SSP.SSPTrit → SSP.SSPTrit → C3.Cyclotomic3
    -- Original secondPositive27 c carries exactly 3.
    secondPositiveCoefficient : SSP.SSPTrit → C3.Cyclotomic3
    -- The last nonzero orbit is (0,0,+1).
    thirdPositiveCoefficient : C3.Cyclotomic3
open PackedHermitian27 public

packedAtOrbit : PackedHermitian27 → Orbit.AntipodalClass27 → C3.Cyclotomic3
packedAtOrbit packed Orbit.centre27 = C3.cyc (centreReal packed) 0ℚ
packedAtOrbit packed (Orbit.firstPositive27 b c) =
  firstPositiveCoefficient packed b c
packedAtOrbit packed (Orbit.secondPositive27 c) =
  secondPositiveCoefficient packed c
packedAtOrbit packed Orbit.thirdPositive27 =
  thirdPositiveCoefficient packed

packedMode : PackedHermitian27 → I.ModeCube27 → C3.Cyclotomic3
packedMode packed mode with positiveSide mode
... | true = packedAtOrbit packed (Ant.antipodalClass27 mode)
... | false = C3.conjC (packedAtOrbit packed (Ant.antipodalClass27 mode))

record Hermitian27 : Set where
  field
    coefficient : I.ModeCube27 → C3.Cyclotomic3
    -- Required: the original *signed orientation* identifies conjugates.
    conjugateAtNegative :
      (mode : I.ModeCube27) →
      coefficient (Ant.negateCube mode) ≡ C3.conjC (coefficient mode)
    -- Source-provided zero-mode is real. This condition prevents
    -- pretending a generic complex DC coefficient fits one ℚ.
    zeroReal : ℚ
    zeroRealCorrect : coefficient zeroModeCube ≡ C3.cyc zeroReal 0ℚ
open Hermitian27 public

packHermitian27 : Hermitian27 → PackedHermitian27
packHermitian27 source = record
  { centreReal = zeroReal source
  ; firstPositiveCoefficient = λ b c →
      coefficient source (representative (Orbit.firstPositive27 b c))
  ; secondPositiveCoefficient = λ c →
      coefficient source (representative (Orbit.secondPositive27 c))
  ; thirdPositiveCoefficient =
      coefficient source (representative Orbit.thirdPositive27)
  }

packedAtOrbitAfterPacking :
  (source : Hermitian27) (orbit : Orbit.AntipodalClass27) →
  packedAtOrbit (packHermitian27 source) orbit
    ≡ coefficient source (representative orbit)
packedAtOrbitAfterPacking source Orbit.centre27 =
  sym (zeroRealCorrect source)
packedAtOrbitAfterPacking source (Orbit.firstPositive27 b c) = refl
packedAtOrbitAfterPacking source (Orbit.secondPositive27 c) = refl
packedAtOrbitAfterPacking source Orbit.thirdPositive27 = refl

-- The actual lossless theorem for every of the 27 coefficients,
-- including all antipodal mates and the real central coefficient.
decodeAfterEncodeHermitian27 :
  (source : Hermitian27) (mode : I.ModeCube27) →
  packedMode (packHermitian27 source) mode ≡ coefficient source mode
decodeAfterEncodeHermitian27 source mode with positiveSide mode
... | true
  rewrite packedAtOrbitAfterPacking source (Ant.antipodalClass27 mode)
        | representativeMatchesSelectedOrientation mode = refl
... | false
  rewrite packedAtOrbitAfterPacking source (Ant.antipodalClass27 mode)
        | representativeMatchesSelectedOrientation mode =
  trans
    (cong C3.conjC (conjugateAtNegative source mode))
    (C3.conjugationInvolutive (coefficient source mode))

-- Source 13 nonzero orbits + one centre: a storage symmetry, not a
-- quotient group operation or a reduction of real Fourier dimensions.
storedIndependentComplexPairs : 9 + 3 + 1 ≡ 13
storedIndependentComplexPairs = refl

realScalarDegreesOfFreedom : 1 + 13 * 2 ≡ 27
realScalarDegreesOfFreedom = refl
