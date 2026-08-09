module DASHI.Biology.EisensteinNineRingInterferenceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Serge Lang,
-- "Algebraic Number Theory", second edition, Springer, 1994.
-- DOI: 10.1007/978-1-4612-0853-2.
--
-- DASHI CONTRIBUTION
--
-- Give an exact rational-coordinate Eisenstein carrier for the symmetric
-- ternary phases 1, omega and omega^2.  Prove the norm polarization identity,
-- exact three-phase cancellation, and a host--guest interference law without
-- floating point or trigonometric approximation.  Separately construct the
-- pointed-square quotient in which the two orientations of the vacant state
-- are identified while the two occupied orientations remain distinct.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper

record Eisenstein : Set where
  constructor eisenstein
  field
    realCoordinate : ℚ
    omegaCoordinate : ℚ

open Eisenstein public

add : Eisenstein → Eisenstein → Eisenstein
add (eisenstein a b) (eisenstein c d) =
  eisenstein (a + c) (b + d)

multiply : Eisenstein → Eisenstein → Eisenstein
multiply (eisenstein a b) (eisenstein c d) =
  eisenstein
    (a * c - b * d)
    (a * d + b * c - b * d)

conjugate : Eisenstein → Eisenstein
conjugate (eisenstein a b) =
  eisenstein (a - b) (0ℚ - b)

norm : Eisenstein → ℚ
norm (eisenstein a b) = a * a - a * b + b * b

crossTerm : Eisenstein → Eisenstein → ℚ
crossTerm (eisenstein a b) (eisenstein c d) =
  (+ 2) * a * c - a * d - b * c + (+ 2) * b * d

one : Eisenstein
one = eisenstein (+ 1) 0ℚ

omega : Eisenstein
omega = eisenstein 0ℚ (+ 1)

omegaSquared : Eisenstein
omegaSquared = eisenstein (0ℚ - (+ 1)) (0ℚ - (+ 1))

omegaSquareReal : realCoordinate (multiply omega omega) ≡ realCoordinate omegaSquared
omegaSquareReal = refl

omegaSquareOmega : omegaCoordinate (multiply omega omega) ≡ omegaCoordinate omegaSquared
omegaSquareOmega = refl

omegaCubedReal : realCoordinate (multiply omega omegaSquared) ≡ realCoordinate one
omegaCubedReal = refl

omegaCubedOmega : omegaCoordinate (multiply omega omegaSquared) ≡ omegaCoordinate one
omegaCubedOmega = refl

threePhaseSum : Eisenstein
threePhaseSum = add one (add omega omegaSquared)

threePhaseCancellationReal : realCoordinate threePhaseSum ≡ 0ℚ
threePhaseCancellationReal = refl

threePhaseCancellationOmega : omegaCoordinate threePhaseSum ≡ 0ℚ
threePhaseCancellationOmega = refl

oneHasUnitNorm : norm one ≡ + 1
oneHasUnitNorm = refl

omegaHasUnitNorm : norm omega ≡ + 1
omegaHasUnitNorm = refl

omegaSquaredHasUnitNorm : norm omegaSquared ≡ + 1
omegaSquaredHasUnitNorm = refl

pairOneOmegaCrossIsMinusOne : crossTerm one omega ≡ 0ℚ - (+ 1)
pairOneOmegaCrossIsMinusOne = refl

pairOneOmegaSquaredCrossIsMinusOne :
  crossTerm one omegaSquared ≡ 0ℚ - (+ 1)
pairOneOmegaSquaredCrossIsMinusOne = refl

pairOmegaOmegaSquaredCrossIsMinusOne :
  crossTerm omega omegaSquared ≡ 0ℚ - (+ 1)
pairOmegaOmegaSquaredCrossIsMinusOne = refl

normPolarization :
  (left right : Eisenstein) →
  norm (add left right)
  ≡ norm left + norm right + crossTerm left right
normPolarization (eisenstein a b) (eisenstein c d) =
  ℚRing.solve-∀ a b c d

threePhaseDiagonalMass : ℚ
threePhaseDiagonalMass = norm one + norm omega + norm omegaSquared

threePhasePairMass : ℚ
threePhasePairMass =
  pairContribution one omega
  + pairContribution one omegaSquared
  + pairContribution omega omegaSquared
  where
  pairContribution : Eisenstein → Eisenstein → ℚ
  pairContribution left right = crossTerm left right

threePhaseDiagonalMassIsThree : threePhaseDiagonalMass ≡ + 3
threePhaseDiagonalMassIsThree = refl

threePhasePairMassIsMinusThree :
  threePhasePairMass ≡ 0ℚ - (+ 3)
threePhasePairMassIsMinusThree = refl

threePhaseTotalMassCancels :
  threePhaseDiagonalMass + threePhasePairMass ≡ 0ℚ
threePhaseTotalMassCancels = refl

------------------------------------------------------------------------
-- Host--guest interference at the indexed gluing seam.
------------------------------------------------------------------------

record HostGuestWave : Set where
  constructor hostGuestWave
  field
    hostAmplitude : Eisenstein
    guestAmplitude : Eisenstein

open HostGuestWave public

joinedAmplitude : HostGuestWave → Eisenstein
joinedAmplitude wave = add (hostAmplitude wave) (guestAmplitude wave)

joinedIntensity : HostGuestWave → ℚ
joinedIntensity wave = norm (joinedAmplitude wave)

separateIntensity : HostGuestWave → ℚ
separateIntensity wave =
  norm (hostAmplitude wave) + norm (guestAmplitude wave)

interferenceContribution : HostGuestWave → ℚ
interferenceContribution wave =
  crossTerm (hostAmplitude wave) (guestAmplitude wave)

hostGuestInterferenceIdentity :
  (wave : HostGuestWave) →
  joinedIntensity wave
  ≡ separateIntensity wave + interferenceContribution wave
hostGuestInterferenceIdentity (hostGuestWave host guest) =
  normPolarization host guest

canonicalDestructivePair : HostGuestWave
canonicalDestructivePair = hostGuestWave one omega

canonicalDestructiveCrossIsMinusOne :
  interferenceContribution canonicalDestructivePair ≡ 0ℚ - (+ 1)
canonicalDestructiveCrossIsMinusOne = refl

------------------------------------------------------------------------
-- The pointed square: one vacant state and two occupied orientations.
------------------------------------------------------------------------

data Occupancy : Set where
  vacant occupied : Occupancy

data PhaseOrientation : Set where
  positive negative : PhaseOrientation

data TernaryPoint : Set where
  zeroPoint zetaPoint zetaSquaredPoint : TernaryPoint

contractSquare : Occupancy → PhaseOrientation → TernaryPoint
contractSquare vacant positive = zeroPoint
contractSquare vacant negative = zeroPoint
contractSquare occupied positive = zetaPoint
contractSquare occupied negative = zetaSquaredPoint

vacantOrientationsCollapse :
  contractSquare vacant positive ≡ contractSquare vacant negative
vacantOrientationsCollapse = refl

occupiedOrientationsRemainDistinct :
  contractSquare occupied positive ≡ contractSquare occupied negative → ⊥
occupiedOrientationsRemainDistinct ()

------------------------------------------------------------------------
-- Exact finite cardinality layers.
------------------------------------------------------------------------

localPhaseCount : Nat
localPhaseCount = 3

orientationCount : Nat
orientationCount = 2

localPhaseSymmetryCount : Nat
localPhaseSymmetryCount = localPhaseCount * orientationCount

localPhaseSymmetryCountIsSix : localPhaseSymmetryCount ≡ 6
localPhaseSymmetryCountIsSix = refl

nineAddressFieldCount : Nat
nineAddressFieldCount = Hyper.ternaryLatticeCount 9

sixCoordinateFieldCount : Nat
sixCoordinateFieldCount = Hyper.ternaryLatticeCount 6

nineAddressFieldCountIs19683 : nineAddressFieldCount ≡ 19683
nineAddressFieldCountIs19683 = refl

sixCoordinateFieldCountIs729 : sixCoordinateFieldCount ≡ 729
sixCoordinateFieldCountIs729 = refl

record EisensteinInterferenceBoundary : Set where
  constructor eisensteinInterferenceBoundary
  field
    sixCountsLocalPhaseOrientationSymmetry : Bool
    sixCountsLocalPhaseOrientationSymmetryIsTrue :
      sixCountsLocalPhaseOrientationSymmetry ≡ true
    nineCountsIndependentTernaryAddresses : Bool
    nineCountsIndependentTernaryAddressesIsTrue :
      nineCountsIndependentTernaryAddresses ≡ true
    sixCoordinateReductionDerivedWithoutConstraints : Bool
    sixCoordinateReductionDerivedWithoutConstraintsIsFalse :
      sixCoordinateReductionDerivedWithoutConstraints ≡ false
    interferenceIdentityIsPhysicalQuantumTheory : Bool
    interferenceIdentityIsPhysicalQuantumTheoryIsFalse :
      interferenceIdentityIsPhysicalQuantumTheory ≡ false

canonicalEisensteinInterferenceBoundary : EisensteinInterferenceBoundary
canonicalEisensteinInterferenceBoundary =
  eisensteinInterferenceBoundary true refl true refl false refl false refl
