module DASHI.Physics.Closure.NSTriadKNCherevanPeriodicCutoffAuditExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Pylyp Cherevan.
-- Title: "Log-free estimate for the resonant paraproduct in the 3D
-- Navier--Stokes equations".
-- arXiv DOI: 10.48550/arXiv.2510.06246.
--
-- PURPOSE
-- Audit the assertion that the narrow region transfers from R^3 to T^3 by
-- normalization alone.  At lambda=4, already the endpoint cutoff
-- lambda^-1/2 equals 1/2; every allowed delta>1/2 makes it smaller.  The
-- smallest nonzero Fourier magnitude on the standard 2pi torus is 1.
-- Hence a cutoff below 1 contains only the zero lattice mode, not a continuum
-- family of low outputs.  Periodisation therefore changes the interaction
-- geometry and needs a separate theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _<_)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_<?_)
open import Relation.Nullary.Decidable.Core using (toWitness)

endpointSubunitCutoff smallestNonzeroTorusMagnitude : ℚ
endpointSubunitCutoff = Int.+ 1 / 2
smallestNonzeroTorusMagnitude = Int.+ 1 / 1

cutoffExcludesFirstNonzeroTorusMode :
  endpointSubunitCutoff < smallestNonzeroTorusMagnitude
cutoffExcludesFirstNonzeroTorusMode =
  toWitness
    {a? = endpointSubunitCutoff <? smallestNonzeroTorusMagnitude}
    _

-- A coordinate stores its sign and a predecessor magnitude: positive n and
-- negative n represent +(n+1) and -(n+1), so every nonzero constructor has
-- lattice magnitude at least one.
data LatticeCoordinate : Set where
  zeroCoordinate : LatticeCoordinate
  positiveCoordinate negativeCoordinate : Nat → LatticeCoordinate

record FourierLatticeMode : Set where
  constructor fourier-lattice-mode
  field
    firstCoordinate secondCoordinate thirdCoordinate : LatticeCoordinate

open FourierLatticeMode public

zeroFourierMode : FourierLatticeMode
zeroFourierMode =
  fourier-lattice-mode
    zeroCoordinate zeroCoordinate zeroCoordinate

data FourierMagnitudeClass : Set where
  zeroMagnitude : FourierMagnitudeClass
  atLeastOneMagnitude : FourierMagnitudeClass

-- This is the exact magnitude class needed at a cutoff strictly below one.
-- It deliberately forgets the size of a nonzero lattice coordinate after
-- recording the sharp lower bound |k| >= 1.
latticeMagnitudeClass : FourierLatticeMode → FourierMagnitudeClass
latticeMagnitudeClass
  (fourier-lattice-mode zeroCoordinate zeroCoordinate zeroCoordinate) =
  zeroMagnitude
latticeMagnitudeClass
  (fourier-lattice-mode (positiveCoordinate first) second third) =
  atLeastOneMagnitude
latticeMagnitudeClass
  (fourier-lattice-mode (negativeCoordinate first) second third) =
  atLeastOneMagnitude
latticeMagnitudeClass
  (fourier-lattice-mode zeroCoordinate (positiveCoordinate second) third) =
  atLeastOneMagnitude
latticeMagnitudeClass
  (fourier-lattice-mode zeroCoordinate (negativeCoordinate second) third) =
  atLeastOneMagnitude
latticeMagnitudeClass
  (fourier-lattice-mode zeroCoordinate zeroCoordinate
    (positiveCoordinate third)) =
  atLeastOneMagnitude
latticeMagnitudeClass
  (fourier-lattice-mode zeroCoordinate zeroCoordinate
    (negativeCoordinate third)) =
  atLeastOneMagnitude

-- Since endpointSubunitCutoff=1/2<1, only the zero magnitude class inhabits
-- the endpoint cutoff predicate.
data BelowEndpointCutoffMagnitude : FourierMagnitudeClass → Set where
  zeroBelowEndpointCutoff :
    BelowEndpointCutoffMagnitude zeroMagnitude

BelowEndpointCutoff : FourierLatticeMode → Set
BelowEndpointCutoff mode =
  BelowEndpointCutoffMagnitude (latticeMagnitudeClass mode)

periodicModeBelowEndpointIsZero :
  (mode : FourierLatticeMode) →
  BelowEndpointCutoff mode →
  mode ≡ zeroFourierMode
periodicModeBelowEndpointIsZero
  (fourier-lattice-mode zeroCoordinate zeroCoordinate zeroCoordinate)
  zeroBelowEndpointCutoff = refl
periodicModeBelowEndpointIsZero
  (fourier-lattice-mode (positiveCoordinate first) second third) ()
periodicModeBelowEndpointIsZero
  (fourier-lattice-mode (negativeCoordinate first) second third) ()
periodicModeBelowEndpointIsZero
  (fourier-lattice-mode zeroCoordinate (positiveCoordinate second) third) ()
periodicModeBelowEndpointIsZero
  (fourier-lattice-mode zeroCoordinate (negativeCoordinate second) third) ()
periodicModeBelowEndpointIsZero
  (fourier-lattice-mode zeroCoordinate zeroCoordinate
    (positiveCoordinate third)) ()
periodicModeBelowEndpointIsZero
  (fourier-lattice-mode zeroCoordinate zeroCoordinate
    (negativeCoordinate third)) ()

record PeriodicNarrowOutput (mode : FourierLatticeMode) : Set where
  constructor periodic-narrow-output
  field
    cutoffHypothesis : BelowEndpointCutoff mode
    outputIsZeroMode : mode ≡ zeroFourierMode

periodicEndpointOutput :
  (mode : FourierLatticeMode) →
  (below : BelowEndpointCutoff mode) →
  PeriodicNarrowOutput mode
periodicEndpointOutput mode below =
  periodic-narrow-output
    below
    (periodicModeBelowEndpointIsZero mode below)

data ContinuumNarrowOutput : Set where
  continuumSubunitOutput : ContinuumNarrowOutput

continuumEndpointOutput : ContinuumNarrowOutput
continuumEndpointOutput = continuumSubunitOutput
