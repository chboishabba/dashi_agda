{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkClosedDeSitterBouncePhaseCurveExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl; sym)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

------------------------------------------------------------------------
-- CLOSED DE-SITTER FRIEDMANN PHASE CURVE WITHOUT A COSH PRIMITIVE
--
-- In units H=1, write u=e^t and uInv=e^-t abstractly, retaining only
-- u*uInv=1.  Then
--
--   a = (u+uInv)/2,
--   v = (u-uInv)/2
--
-- obey v^2 + 1 = a^2, the k=+1 vacuum Friedmann constraint.  At u=uInv=1,
-- a=1 and v=0: the phase curve contains an exact nonzero-radius bounce point.
--
-- This pays the algebraic Friedmann-constraint branch.  Identifying v with the
-- actual time derivative da/dt and proving the acceleration equation requires
-- the exponential/hyperbolic differential authority and remains separate.
------------------------------------------------------------------------

closedScale : ℚ → ℚ → ℚ
closedScale u uInv = (u + uInv) / (Int.+ 2 / 1)

closedVelocity : ℚ → ℚ → ℚ
closedVelocity u uInv = (u - uInv) / (Int.+ 2 / 1)

phaseCurveDifference :
  (u uInv : ℚ) →
  closedScale u uInv * closedScale u uInv
  - closedVelocity u uInv * closedVelocity u uInv
  ≡ u * uInv
phaseCurveDifference u uInv = solve (u ∷ uInv ∷ [])

closedFriedmannConstraint :
  (u uInv : ℚ) →
  u * uInv ≡ 1ℚ →
  closedVelocity u uInv * closedVelocity u uInv + 1ℚ
  ≡ closedScale u uInv * closedScale u uInv
closedFriedmannConstraint u uInv inversePair
  rewrite sym inversePair = solve (u ∷ uInv ∷ [])

bounceU : ℚ
bounceU = 1ℚ

bounceUInv : ℚ
bounceUInv = 1ℚ

bouncePointHasZeroVelocity :
  closedVelocity bounceU bounceUInv ≡ 0ℚ
bouncePointHasZeroVelocity = solve []

bouncePointHasUnitScale :
  closedScale bounceU bounceUInv ≡ 1ℚ
bouncePointHasUnitScale = solve []

bouncePointSatisfiesClosedFriedmannConstraint :
  closedVelocity bounceU bounceUInv * closedVelocity bounceU bounceUInv + 1ℚ
  ≡ closedScale bounceU bounceUInv * closedScale bounceU bounceUInv
bouncePointSatisfiesClosedFriedmannConstraint = solve []

phaseCurveConstraintOwned : Bool
phaseCurveConstraintOwned = true

nonzeroRadiusBouncePointOwned : Bool
nonzeroRadiusBouncePointOwned = true

timeDerivativeIdentificationStillRequired : Bool
timeDerivativeIdentificationStillRequired = true

closedDeSitterContinuumSolutionFullyDerivedInternally : Bool
closedDeSitterContinuumSolutionFullyDerivedInternally = false

historySectorSelectsThisBounceDynamically : Bool
historySectorSelectsThisBounceDynamically = false
