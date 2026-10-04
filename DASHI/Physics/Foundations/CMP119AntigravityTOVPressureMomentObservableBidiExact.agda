{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityTOVPressureMomentObservableBidiExact where

------------------------------------------------------------------------
-- THE BIDIRECTIONAL EINSTEIN/TOV GEODESIC READOUT
--
-- After the static-spherical Einstein rr constraint has given
--    r² a_r = -[m(r) + r³ p_r(r)]
-- (G=c=1 with the repo's four-pi-absorbed pressure convention),
-- define q=r³p_r and z=r² a_r.
--
-- Forward:  z = -(m+q).
-- Backward: q = -z-m.
--
-- The two exact maps are mutual inverses. This gives a genuinely
-- bidirectional comparison between a selected quantum radial-pressure
-- insertion and the *observable* geodesic response after specifying the
-- Einstein constraint, metric matching, and probe calibration.
--
-- It DOES NOT identify q with active stress rho+p_r+2p_t or make a
-- pressure tensor from an arbitrarily chosen antigravity certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; _<_; -_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; subst₂; sym)
import Data.Rational.Tactic.RingSolver as Ring
import DASHI.Physics.Foundations.GRQFTFiniteRationalTOVSystemExact as TOV
import DASHI.Physics.Foundations.CMP119AntigravityTOVSourceToRadialObservableBidiExact as Radial

scaledGeodesicFromMassPressureMoment : ℚ → ℚ → ℚ
scaledGeodesicFromMassPressureMoment mass radialPressureMoment =
  - (mass + radialPressureMoment)

pressureMomentFromMassGeodesic : ℚ → ℚ → ℚ
pressureMomentFromMassGeodesic mass scaledAcceleration =
  - scaledAcceleration - mass

backwardAfterForward :
  ∀ mass radialPressureMoment →
  pressureMomentFromMassGeodesic mass
    (scaledGeodesicFromMassPressureMoment mass radialPressureMoment)
  ≡ radialPressureMoment
backwardAfterForward mass radialPressureMoment =
  Ring.solve-∀ mass radialPressureMoment

forwardAfterBackward :
  ∀ mass scaledAcceleration →
  scaledGeodesicFromMassPressureMoment mass
    (pressureMomentFromMassGeodesic mass scaledAcceleration)
  ≡ scaledAcceleration
forwardAfterBackward mass scaledAcceleration =
  Ring.solve-∀ mass scaledAcceleration

-- This is computed from an actual pre-existing radial source state;
-- the on-shell Einstein map above is not selected independently.
scaledSourceGeodesic : TOV.RationalRadialState → ℚ
scaledSourceGeodesic s =
  scaledGeodesicFromMassPressureMoment
    (TOV.mass s)
    ((TOV.radius s * TOV.radius s * TOV.radius s)
      * TOV.radialPressure s)

scaledSourceGeodesicIsNegativeEinsteinNumerator :
  ∀ s →
  scaledSourceGeodesic s ≡ - TOV.tovGravityNumerator s
scaledSourceGeodesicIsNegativeEinsteinNumerator s =
  Ring.solve-∀
    (TOV.mass s)
    (TOV.radius s)
    (TOV.radialPressure s)

sourcePressureMomentRecovered :
  ∀ s →
  pressureMomentFromMassGeodesic
    (TOV.mass s)
    (scaledSourceGeodesic s)
  ≡ (TOV.radius s * TOV.radius s * TOV.radius s)
    * TOV.radialPressure s
sourcePressureMomentRecovered s =
  backwardAfterForward
    (TOV.mass s)
    ((TOV.radius s * TOV.radius s * TOV.radius s)
      * TOV.radialPressure s)

-- Source-level readout is exact and reversible algebraically. A physical
-- metric solution and the correct renormalized stress insertion must still
-- establish that the observed scaled acceleration is THIS readout.

------------------------------------------------------------------------
-- The sign also transports IN BOTH DIRECTIONS, with no separately
-- asserted Antigravity boolean or negative active stress certificate.
------------------------------------------------------------------------

negativeEinsteinNumeratorGivesOutwardScaledResponse :
  ∀ mass pressureMoment →
  mass + pressureMoment < 0ℚ →
  0ℚ < scaledGeodesicFromMassPressureMoment mass pressureMoment
negativeEinsteinNumeratorGivesOutwardScaledResponse
    mass pressureMoment negative =
  ℚP.neg-antimono-< negative

outwardScaledResponseForcesNegativeEinsteinNumerator :
  ∀ mass pressureMoment →
  0ℚ < scaledGeodesicFromMassPressureMoment mass pressureMoment →
  mass + pressureMoment < 0ℚ
outwardScaledResponseForcesNegativeEinsteinNumerator
    mass pressureMoment outward =
  subst₂ _<_
    (Ring.solve-∀ mass pressureMoment)
    (Ring.solve-∀ mass pressureMoment)
    (ℚP.neg-antimono-< outward)

-- An initially-resting outward trajectory is controlled by the *source
-- mass-pressure moment* sign. The weak-field pressure-weighted active mass
-- and the Lorentzian trace are DIFFERENT observables.
