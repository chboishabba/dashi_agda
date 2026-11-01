module DASHI.Physics.Closure.NSTriadKNLuoFiniteBoundaryLayerVorticityTiltExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Richard Rotunno.
-- Title: "The Fluid Dynamics of Tornadoes".
-- Annual Review of Fluid Mechanics 45 (2013), 59--84.
-- DOI: 10.1146/annurev-fluid-011212-140639.
--
-- PURPOSE
-- Separate the real-space boundary-layer analogy from the Fourier-direction
-- eigenbundle question.  A rational 3-4-5 rotation about the y axis smoothly
-- tilts horizontal vorticity into a state with nonzero vertical component,
-- while preserving squared magnitude exactly.
--
-- This is a finite algebraic model of smooth vorticity reorientation in
-- physical space.  It contains no sign-monodromy or discontinuity and is not
-- a proof about the wavevector sphere.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V

threeFifths fourFifths : ℚ
threeFifths = Int.+ 3 / 5
fourFifths = Int.+ 4 / 5

physicalTilt : V.Vector3 → V.Vector3
physicalTilt (V.v3 vx vy vz) =
  V.v3
    (threeFifths * vx + fourFifths * vz)
    vy
    ((- fourFifths) * vx + threeFifths * vz)

physicalTiltPreservesMagnitude :
  (vorticity : V.Vector3) →
  V.normSquared (physicalTilt vorticity)
  ≡ V.normSquared vorticity
physicalTiltPreservesMagnitude (V.v3 vx vy vz) =
  solve (vx ∷ vy ∷ vz ∷ [])

horizontalUnitVorticity : V.Vector3
horizontalUnitVorticity = V.v3 1ℚ 0ℚ 0ℚ

tiltedHorizontalVorticity :
  physicalTilt horizontalUnitVorticity
  ≡ V.v3 threeFifths 0ℚ (- fourFifths)
tiltedHorizontalVorticity =
  V.vectorExt (solve []) (solve []) (solve [])

tiltedVerticalComponentNonzeroWitness :
  V.z (physicalTilt horizontalUnitVorticity)
  ≡ - fourFifths
tiltedVerticalComponentNonzeroWitness = solve []

tiltedUnitMagnitude :
  V.normSquared (physicalTilt horizontalUnitVorticity) ≡ 1ℚ
tiltedUnitMagnitude = solve []
