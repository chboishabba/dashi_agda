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

open import Agda.Builtin.Equality using (_≡_)
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

data PeriodicNarrowOutput : Set where
  zeroLatticeMode : PeriodicNarrowOutput
  nonzeroLatticeMode : PeriodicNarrowOutput

data ContinuumNarrowOutput : Set where
  continuumSubunitOutput : ContinuumNarrowOutput

periodicEndpointOutput : PeriodicNarrowOutput
periodicEndpointOutput = zeroLatticeMode

continuumEndpointOutput : ContinuumNarrowOutput
continuumEndpointOutput = continuumSubunitOutput
