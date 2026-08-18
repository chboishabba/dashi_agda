module DASHI.Moonshine.FrickeDeckSpectralMultiplicityObserverExact where

------------------------------------------------------------------------
-- FOURTH AXIS: MULTIPLICITY-COPY IDENTITY INSIDE THE p=37 STANDARD ISOTYPIC
--
-- P37MarkedDeckIsotypicJointDecompositionExact proves
--
--   standard isotypic dimension = 12
--   standard multiplicity block dimension = 6
--   12 = 2 * 6.
--
-- Its source-native Hecke/Frobenius operators act as two copies of the same
-- six-dimensional block.  This file constructs that direct sum explicitly and
-- proves a new observer no-go:
--
--   (coarse selector, deck irrep, scalar spectrum)
--
-- does NOT recover which multiplicity copy carries a mode.
--
-- Two distinct vectors supported in different six-dimensional copies inherit
-- exactly the same (T3,T5,F)=(1,0,+1) packet from the existing standard mode A.
-- The missing coordinate is therefore genuine multiplicity-space identity,
-- not another scalar Hecke eigenvalue.
--
-- This is the precise finite theorem behind the reusable principle
--
--   operator eigencharacter != multiplicity-space identity.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational using (0ℚ)

import DASHI.Moonshine.P37MarkedDeckIsotypicJointDecompositionExact as Iso
import DASHI.Moonshine.P37MarkedDeckIsotypicPolynomialExact as Poly
import DASHI.Moonshine.FrickeDeckSpectralObserverThreeAxisExact as Three

------------------------------------------------------------------------
-- Explicit 12-dimensional standard isotypic carrier = 6 + 6.
------------------------------------------------------------------------

record StandardIsotypic12 : Set where
  constructor standardIso12
  field
    copy0 copy1 : Iso.StdBlock3
open StandardIsotypic12 public

zero12 : StandardIsotypic12
zero12 = standardIso12 Poly.zeroStd Poly.zeroStd

standardT3Iso12 : StandardIsotypic12 → StandardIsotypic12
standardT3Iso12 x =
  standardIso12 (Iso.standardT3 (copy0 x)) (Iso.standardT3 (copy1 x))

standardT5Iso12 : StandardIsotypic12 → StandardIsotypic12
standardT5Iso12 x =
  standardIso12 (Iso.standardT5 (copy0 x)) (Iso.standardT5 (copy1 x))

standardFIso12 : StandardIsotypic12 → StandardIsotypic12
standardFIso12 x =
  standardIso12 (Iso.standardF (copy0 x)) (Iso.standardF (copy1 x))

------------------------------------------------------------------------
-- Same source-native eigenpacket in two different multiplicity copies.
------------------------------------------------------------------------

modeAInCopy0 modeAInCopy1 : StandardIsotypic12
modeAInCopy0 = standardIso12 Three.standardModeA Poly.zeroStd
modeAInCopy1 = standardIso12 Poly.zeroStd Three.standardModeA

modeAInCopy0T3 : standardT3Iso12 modeAInCopy0 ≡ modeAInCopy0
modeAInCopy0T3
  rewrite Three.standardModeAT3 = refl

modeAInCopy1T3 : standardT3Iso12 modeAInCopy1 ≡ modeAInCopy1
modeAInCopy1T3
  rewrite Three.standardModeAT3 = refl

modeAInCopy0T5Zero : standardT5Iso12 modeAInCopy0 ≡ zero12
modeAInCopy0T5Zero
  rewrite Three.standardModeAT5 = refl

modeAInCopy1T5Zero : standardT5Iso12 modeAInCopy1 ≡ zero12
modeAInCopy1T5Zero
  rewrite Three.standardModeAT5 = refl

modeAInCopy0FEven : standardFIso12 modeAInCopy0 ≡ modeAInCopy0
modeAInCopy0FEven
  rewrite Three.standardModeAF = refl

modeAInCopy1FEven : standardFIso12 modeAInCopy1 ≡ modeAInCopy1
modeAInCopy1FEven
  rewrite Three.standardModeAF = refl

modeACopiesDistinct : modeAInCopy0 ≡ modeAInCopy1 → ⊥
modeACopiesDistinct ()

------------------------------------------------------------------------
-- Three-axis observation is identical on the two copy-supported modes.
------------------------------------------------------------------------

data MultiplicityCopy : Set where
  multiplicity0 multiplicity1 : MultiplicityCopy

threeAxisForModeA : Three.ThreeAxisObservation
threeAxisForModeA = Three.threeAxisObservation Three.modeA

threeAxisByCopy : MultiplicityCopy → Three.ThreeAxisObservation
threeAxisByCopy multiplicity0 = threeAxisForModeA
threeAxisByCopy multiplicity1 = threeAxisForModeA

sameThreeAxisAcrossMultiplicityCopies :
  threeAxisByCopy multiplicity0 ≡ threeAxisByCopy multiplicity1
sameThreeAxisAcrossMultiplicityCopies = refl

ThreeAxisDeterminesMultiplicity : Set
ThreeAxisDeterminesMultiplicity =
  Σ (Three.ThreeAxisObservation → MultiplicityCopy)
    (λ decode →
      (c : MultiplicityCopy) → decode (threeAxisByCopy c) ≡ c)

threeAxisCannotDetermineMultiplicity : ThreeAxisDeterminesMultiplicity → ⊥
threeAxisCannotDetermineMultiplicity (decode , factors) with
  trans
    (sym (factors multiplicity0))
    (trans
      (cong decode sameThreeAxisAcrossMultiplicityCopies)
      (factors multiplicity1))
... | ()

------------------------------------------------------------------------
-- Refined observer retains the multiplicity coordinate explicitly.
------------------------------------------------------------------------

record FourAxisObservation : Set where
  constructor fourAxis
  field
    threeAxis : Three.ThreeAxisObservation
    multiplicity : MultiplicityCopy
open FourAxisObservation public

fourAxisByCopy : MultiplicityCopy → FourAxisObservation
fourAxisByCopy c = fourAxis (threeAxisByCopy c) c

fourAxisSeparatesMultiplicityCopies :
  fourAxisByCopy multiplicity0 ≡ fourAxisByCopy multiplicity1 → ⊥
fourAxisSeparatesMultiplicityCopies ()

record FrickeDeckSpectralMultiplicityObserverBoundary : Set where
  field
    standardIsotypicTwelveConstructedAsSixPlusSix : Bool
    bothCopiesCarrySameModeAEigenpacket : Bool
    threeAxisObserverCollidesAcrossCopies : Bool
    multiplicityCoordinateRequiredForCopyIdentity : Bool
    fourAxisObserverSeparatesCopyWitness : Bool
    scalarEigencharacterIdentifiedWithMultiplicityIdentity : Bool

canonicalFrickeDeckSpectralMultiplicityObserverBoundary :
  FrickeDeckSpectralMultiplicityObserverBoundary
canonicalFrickeDeckSpectralMultiplicityObserverBoundary = record
  { standardIsotypicTwelveConstructedAsSixPlusSix = true
  ; bothCopiesCarrySameModeAEigenpacket = true
  ; threeAxisObserverCollidesAcrossCopies = true
  ; multiplicityCoordinateRequiredForCopyIdentity = true
  ; fourAxisObserverSeparatesCopyWitness = true
  ; scalarEigencharacterIdentifiedWithMultiplicityIdentity = false
  }
