module DASHI.Physics.Closure.NSTriadKNRestrictedEulerVieillefosseCalibrationRound78Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: P. Vieillefosse.
-- Title: "Local interaction between vorticity and shear in a perfect
-- incompressible fluid".
-- Journal de Physique 43 (1982), 837--842.
-- DOI: 10.1051/jphys:01982004306083700.
--
-- Author: Brian J. Cantwell.
-- Title: "Exact solution of a restricted Euler equation for the velocity
-- gradient tensor".
-- Physics of Fluids A 4 (1992), 782--793.
-- DOI: 10.1063/1.858295.
--
-- ROUND78 / RESTRICTED-EULER CALIBRATION, NOT NS AUTHORITY
--
-- For the classical three-dimensional restricted-Euler invariant variables
-- (with the standard Q,R sign convention), the homogeneous system is
--
--   Q' = -3 R,
--   R' = (2/3) Q^2.
--
-- This file proves the exact polynomial first integral
--
--   D(Q,R) = 4 Q^3 + 27 R^2,
--   D' = 0,
--
-- by direct rational algebra, and records that R' is nonnegative.  This is a
-- clean finite algebraic model of genuine local self-amplification and the
-- Vieillefosse invariant surface.  It is deliberately NOT promoted to the
-- full Navier--Stokes B2 theorem: full NS retains nonlocal pressure, convection
-- and viscosity, and Round78 separately proves that one Fourier mode cannot
-- generate its own vortex-stretching scalar.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _+_; _*_; -_; _≤_)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

twoThirds three four twentySeven : ℚ
twoThirds = Int.+ 2 / 3
three = Int.+ 3 / 1
four = Int.+ 4 / 1
twentySeven = Int.+ 27 / 1

twoThirdsNonnegative : 0ℚ ≤ twoThirds
twoThirdsNonnegative = toWitness {a? = 0ℚ ≤? twoThirds} _

restrictedQDerivative : ℚ → ℚ
restrictedQDerivative R = - (three * R)

restrictedRDerivative : ℚ → ℚ
restrictedRDerivative Q = twoThirds * L2.square Q

vieillefosseDiscriminant : ℚ → ℚ → ℚ
vieillefosseDiscriminant Q R =
  four * Q * Q * Q + twentySeven * R * R

-- Formal directional derivative of D along the restricted-Euler (Q,R) field.
vieillefosseDiscriminantDerivative : ℚ → ℚ → ℚ
vieillefosseDiscriminantDerivative Q R =
  (Int.+ 12 / 1) * Q * Q * restrictedQDerivative R
  + (Int.+ 54 / 1) * R * restrictedRDerivative Q

vieillefosseDiscriminantIsFirstIntegral : ∀ Q R →
  vieillefosseDiscriminantDerivative Q R ≡ 0ℚ
vieillefosseDiscriminantIsFirstIntegral Q R =
  solve (Q ∷ R ∷ [])

restrictedRDerivativeNonnegative : ∀ Q →
  0ℚ ≤ restrictedRDerivative Q
restrictedRDerivativeNonnegative Q =
  ℚP.0≤*0≤ twoThirdsNonnegative (L2.squareNonnegative Q)

round78RestrictedEulerVieillefosseInvariantExact : Bool
round78RestrictedEulerVieillefosseInvariantExact = true

round78RestrictedEulerLocalSelfAmplificationModelExists : Bool
round78RestrictedEulerLocalSelfAmplificationModelExists = true

round78RestrictedEulerModelIsFullNSB2Authority : Bool
round78RestrictedEulerModelIsFullNSB2Authority = false

round78RestrictedEulerVieillefosseInvariantExactIsTrue :
  round78RestrictedEulerVieillefosseInvariantExact ≡ true
round78RestrictedEulerVieillefosseInvariantExactIsTrue = refl
