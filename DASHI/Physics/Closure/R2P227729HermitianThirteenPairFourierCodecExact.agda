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

------------------------------------------------------------------------
-- SOURCE FIVE-IN-NINE: one real centre and four complex conjugate pairs.
-- Uses original *global C2 antipode* quotient, not the D4 3-orbit
-- cell quotient, nor the five D4 irreducible representation species.
------------------------------------------------------------------------

plane9Zero : Ant.Plane9
plane9Zero = M.modeZero , M.modeZero

plane9Representative : Orbit.AntipodalClass9 → Ant.Plane9
plane9Representative Orbit.centre9 = plane9Zero
plane9Representative Orbit.firstAxis9 = M.modePlus , M.modeZero
plane9Representative Orbit.secondAxis9 = M.modeZero , M.modePlus
plane9Representative Orbit.sameSignDiagonal9 = M.modePlus , M.modePlus
plane9Representative Orbit.oppositeSignDiagonal9 = M.modePlus , M.modeMinus

planeRepresentativeHasCorrectClass :
  (orbit : Orbit.AntipodalClass9) →
  Ant.antipodalClass9 (plane9Representative orbit) ≡ orbit
planeRepresentativeHasCorrectClass Orbit.centre9 = refl
planeRepresentativeHasCorrectClass Orbit.firstAxis9 = refl
planeRepresentativeHasCorrectClass Orbit.secondAxis9 = refl
planeRepresentativeHasCorrectClass Orbit.sameSignDiagonal9 = refl
planeRepresentativeHasCorrectClass Orbit.oppositeSignDiagonal9 = refl

planePositiveSide : Ant.Plane9 → Bool
planePositiveSide (M.modePlus , b) = true
planePositiveSide (M.modeMinus , b) = false
planePositiveSide (M.modeZero , M.modePlus) = true
planePositiveSide (M.modeZero , M.modeMinus) = false
planePositiveSide (M.modeZero , M.modeZero) = true

choosePlane9 : Bool → Ant.Plane9 → Ant.Plane9 → Ant.Plane9
choosePlane9 true a b = a
choosePlane9 false a b = b

planeRepresentativeMatchesSelectedOrientation :
  (plane : Ant.Plane9) →
  plane9Representative (Ant.antipodalClass9 plane)
    ≡ choosePlane9 (planePositiveSide plane)
         plane (Ant.negatePlane9 plane)
planeRepresentativeMatchesSelectedOrientation (M.modeMinus , M.modeMinus) = refl
planeRepresentativeMatchesSelectedOrientation (M.modeMinus , M.modeZero) = refl
planeRepresentativeMatchesSelectedOrientation (M.modeMinus , M.modePlus) = refl
planeRepresentativeMatchesSelectedOrientation (M.modeZero , M.modeMinus) = refl
planeRepresentativeMatchesSelectedOrientation (M.modeZero , M.modeZero) = refl
planeRepresentativeMatchesSelectedOrientation (M.modeZero , M.modePlus) = refl
planeRepresentativeMatchesSelectedOrientation (M.modePlus , M.modeMinus) = refl
planeRepresentativeMatchesSelectedOrientation (M.modePlus , M.modeZero) = refl
planeRepresentativeMatchesSelectedOrientation (M.modePlus , M.modePlus) = refl

record PackedHermitian9 : Set where
  field
    planeCentreReal : ℚ
    firstAxisCoefficient : C3.Cyclotomic3
    secondAxisCoefficient : C3.Cyclotomic3
    sameDiagonalCoefficient : C3.Cyclotomic3
    oppositeDiagonalCoefficient : C3.Cyclotomic3
open PackedHermitian9 public

packedNineAtOrbit : PackedHermitian9 → Orbit.AntipodalClass9 → C3.Cyclotomic3
packedNineAtOrbit packed Orbit.centre9 =
  C3.cyc (planeCentreReal packed) 0ℚ
packedNineAtOrbit packed Orbit.firstAxis9 = firstAxisCoefficient packed
packedNineAtOrbit packed Orbit.secondAxis9 = secondAxisCoefficient packed
packedNineAtOrbit packed Orbit.sameSignDiagonal9 = sameDiagonalCoefficient packed
packedNineAtOrbit packed Orbit.oppositeSignDiagonal9 =
  oppositeDiagonalCoefficient packed

packedPlane9 : PackedHermitian9 → Ant.Plane9 → C3.Cyclotomic3
packedPlane9 packed plane with planePositiveSide plane
... | true = packedNineAtOrbit packed (Ant.antipodalClass9 plane)
... | false = C3.conjC (packedNineAtOrbit packed (Ant.antipodalClass9 plane))

record Hermitian9 : Set where
  field
    coefficient9 : Ant.Plane9 → C3.Cyclotomic3
    conjugateAtNegative9 :
      (plane : Ant.Plane9) →
      coefficient9 (Ant.negatePlane9 plane)
        ≡ C3.conjC (coefficient9 plane)
    zero9Real : ℚ
    zero9RealCorrect :
      coefficient9 plane9Zero ≡ C3.cyc zero9Real 0ℚ
open Hermitian9 public

packHermitian9 : Hermitian9 → PackedHermitian9
packHermitian9 source = record
  { planeCentreReal = zero9Real source
  ; firstAxisCoefficient = coefficient9 source
      (plane9Representative Orbit.firstAxis9)
  ; secondAxisCoefficient = coefficient9 source
      (plane9Representative Orbit.secondAxis9)
  ; sameDiagonalCoefficient = coefficient9 source
      (plane9Representative Orbit.sameSignDiagonal9)
  ; oppositeDiagonalCoefficient = coefficient9 source
      (plane9Representative Orbit.oppositeSignDiagonal9)
  }

packedNineAtOrbitAfterPacking :
  (source : Hermitian9) (orbit : Orbit.AntipodalClass9) →
  packedNineAtOrbit (packHermitian9 source) orbit
    ≡ coefficient9 source (plane9Representative orbit)
packedNineAtOrbitAfterPacking source Orbit.centre9 =
  sym (zero9RealCorrect source)
packedNineAtOrbitAfterPacking source Orbit.firstAxis9 = refl
packedNineAtOrbitAfterPacking source Orbit.secondAxis9 = refl
packedNineAtOrbitAfterPacking source Orbit.sameSignDiagonal9 = refl
packedNineAtOrbitAfterPacking source Orbit.oppositeSignDiagonal9 = refl

decodeAfterEncodeHermitian9 :
  (source : Hermitian9) (plane : Ant.Plane9) →
  packedPlane9 (packHermitian9 source) plane ≡ coefficient9 source plane
decodeAfterEncodeHermitian9 source plane with planePositiveSide plane
... | true
  rewrite packedNineAtOrbitAfterPacking source (Ant.antipodalClass9 plane)
        | planeRepresentativeMatchesSelectedOrientation plane = refl
... | false
  rewrite packedNineAtOrbitAfterPacking source (Ant.antipodalClass9 plane)
        | planeRepresentativeMatchesSelectedOrientation plane =
  trans
    (cong C3.conjC (conjugateAtNegative9 source plane))
    (C3.conjugationInvolutive (coefficient9 source plane))

storedIndependentComplexPlanePairs : 4 ≡ 4
storedIndependentComplexPlanePairs = refl

planeRealScalarDegreesOfFreedom : 1 + 4 * 2 ≡ 9
planeRealScalarDegreesOfFreedom = refl

-- Five vs fourteen are source orbit counts; the codecs are not D4 group
-- irreducible decomposition, and the Fourier operator is not compressed
-- by simply deleting signed/complex residuals.
