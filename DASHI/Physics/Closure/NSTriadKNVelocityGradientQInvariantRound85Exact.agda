module DASHI.Physics.Closure.NSTriadKNVelocityGradientQInvariantRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: J. C. R. Hunt; A. A. Wray; P. Moin.
-- Title: "Eddies, streams, and convergence zones in turbulent flows".
-- Center for Turbulence Research, Proceedings of the 1988 Summer Program.
-- NASA NTRS: 19890015184. DOI: not assigned in the cited report record.
--
-- Authors: Perry L. Chong; Andrew E. Perry; Brian J. Cantwell.
-- Title: "A general classification of three-dimensional flow fields".
-- Physics of Fluids A 2 (1990), 765--777.
-- DOI: 10.1063/1.857730.
--
-- Authors: Jinhee Jeong; Fazle Hussain.
-- Title: "On the identification of a vortex".
-- Journal of Fluid Mechanics 285 (1995), 69--94.
-- DOI: 10.1017/S0022112095000462.
--
-- ROUND85 / EXACT VELOCITY-GRADIENT Q IDENTITY
--
-- For a real 3x3 velocity-gradient matrix A, let
--
--   S = (A + A^T)/2,
--   omega = curl u
--         = (A32-A23, A13-A31, A21-A12).
--
-- Direct algebra gives
--
--   tr(A^2) = S:S - |omega|^2/2.
--
-- Therefore, in the incompressible convention used by Round78,
--
--   Q = |omega|^2/4 - S:S/2
--     = - tr(A^2)/2,
--
-- and the pressure Poisson source is exactly
--
--   -Delta p = tr(A^2) = -2Q.
--
-- This closes the coefficient normalization at the tensor-algebra level.  A
-- separate same-object Fourier theorem identifies the literal Galerkin
-- pressure source with the divergence of the actual advective output fibre.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (trans)

record Gradient3 : Set where
  constructor gradient3
  field
    a11 a12 a13
    a21 a22 a23
    a31 a32 a33 : ℚ

open Gradient3 public

half quarter : ℚ
half = Int.+ 1 / 2
quarter = Int.+ 1 / 4

square : ℚ → ℚ
square value = value * value

traceSquare : Gradient3 → ℚ
traceSquare A =
    square (a11 A) + square (a22 A) + square (a33 A)
  + (a12 A * a21 A + a21 A * a12 A)
  + (a13 A * a31 A + a31 A * a13 A)
  + (a23 A * a32 A + a32 A * a23 A)

s11 s22 s33 s12 s13 s23 : Gradient3 → ℚ
s11 A = a11 A
s22 A = a22 A
s33 A = a33 A
s12 A = half * (a12 A + a21 A)
s13 A = half * (a13 A + a31 A)
s23 A = half * (a23 A + a32 A)

strainFrobeniusSquared : Gradient3 → ℚ
strainFrobeniusSquared A =
    square (s11 A) + square (s22 A) + square (s33 A)
  + (square (s12 A) + square (s12 A))
  + (square (s13 A) + square (s13 A))
  + (square (s23 A) + square (s23 A))

omega1 omega2 omega3 : Gradient3 → ℚ
omega1 A = a32 A - a23 A
omega2 A = a13 A - a31 A
omega3 A = a21 A - a12 A

vorticitySquared : Gradient3 → ℚ
vorticitySquared A =
  square (omega1 A) + square (omega2 A) + square (omega3 A)

qCriterion : Gradient3 → ℚ
qCriterion A =
  quarter * vorticitySquared A - half * strainFrobeniusSquared A

pressurePoissonSource : Gradient3 → ℚ
pressurePoissonSource = traceSquare

traceSquareEqualsStrainMinusHalfVorticity :
  (A : Gradient3) →
  traceSquare A
  ≡ strainFrobeniusSquared A - half * vorticitySquared A
traceSquareEqualsStrainMinusHalfVorticity
    (gradient3 a11 a12 a13 a21 a22 a23 a31 a32 a33) =
  solve
    (a11 ∷ a12 ∷ a13 ∷ a21 ∷ a22 ∷ a23 ∷ a31 ∷ a32 ∷ a33 ∷ [])

qCriterionEqualsNegativeHalfTraceSquare :
  (A : Gradient3) →
  qCriterion A ≡ - (half * traceSquare A)
qCriterionEqualsNegativeHalfTraceSquare
    (gradient3 a11 a12 a13 a21 a22 a23 a31 a32 a33) =
  solve
    (a11 ∷ a12 ∷ a13 ∷ a21 ∷ a22 ∷ a23 ∷ a31 ∷ a32 ∷ a33 ∷ [])

pressurePoissonSourceEqualsNegativeTwoQ :
  (A : Gradient3) →
  pressurePoissonSource A
  ≡ - ((Int.+ 2 / 1) * qCriterion A)
pressurePoissonSourceEqualsNegativeTwoQ
    (gradient3 a11 a12 a13 a21 a22 a23 a31 a32 a33) =
  solve
    (a11 ∷ a12 ∷ a13 ∷ a21 ∷ a22 ∷ a23 ∷ a31 ∷ a32 ∷ a33 ∷ [])

-- Round78 stores Sigma = 2 S:S and Omega = |omega|^2.  The source therefore
-- has the exact repository form (Sigma-Omega)/2.
strainIntensity : Gradient3 → ℚ
strainIntensity A = (Int.+ 2 / 1) * strainFrobeniusSquared A

enstrophy : Gradient3 → ℚ
enstrophy = vorticitySquared

pressureSourceMatchesRound78SigmaOmega :
  (A : Gradient3) →
  pressurePoissonSource A
  ≡ half * (strainIntensity A - enstrophy A)
pressureSourceMatchesRound78SigmaOmega A =
  trans
    (traceSquareEqualsStrainMinusHalfVorticity A)
    (solve (strainFrobeniusSquared A ∷ vorticitySquared A ∷ []))

round85VelocityGradientQInvariantExact : Bool
round85VelocityGradientQInvariantExact = true

round85PressureSourceEqualsNegativeTwoQExact : Bool
round85PressureSourceEqualsNegativeTwoQExact = true

round85PressureSourceMatchesRound78SigmaOmegaExact : Bool
round85PressureSourceMatchesRound78SigmaOmegaExact = true

round85PressureSourceEqualsNegativeTwoQExactIsTrue :
  round85PressureSourceEqualsNegativeTwoQExact ≡ true
round85PressureSourceEqualsNegativeTwoQExactIsTrue = refl
