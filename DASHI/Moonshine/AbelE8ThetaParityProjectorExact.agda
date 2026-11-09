module DASHI.Moonshine.AbelE8ThetaParityProjectorExact where

------------------------------------------------------------------------
-- ALL-INDEX FINITE COEFFICIENT ALGEBRA (WITHOUT MODULAR ASSUMPTIONS)
--
-- For an E8 shell index n:
--   I₀ = integer vectors with sum of doubled coordinates ≡ 0 mod 4,
--   I₂ = integer vectors with sum ≡ 2 mod 4,
--   H₀ = half-integer vectors with sum ≡ 0 mod 4,
--   H₂ = half-integer vectors with sum ≡ 2 mod 4.
--
-- The classical signed theta4 coefficient is I₀ - I₂.
-- theta3 coeff is I₀+I₂, theta2 coeff is H₀+H₂.
-- If H₀=H₂, the theta identity follows:
--   2*(I₀+H₀) = theta3 + theta4 + theta2.
--
-- We avoid subtraction in ℕ by moving theta4-negative to LHS.
-- This algebraic statement is proved for ALL n, not just n=0..8.
--
-- The original E8 half-family sign-changing involution and original
-- Bishop theta-series analytic convergence remain independent inputs.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl; cong; sym)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)

record E8ShellParityCounts : Set where
  constructor e8-shell-parity-counts
  field
    integerResidueZero : Nat
    integerResidueTwo : Nat
    halfResidueZero : Nat
    halfResidueTwo : Nat
    halfParityCancellation : halfResidueZero ≡ halfResidueTwo

open E8ShellParityCounts public

e8ThetaCoefficient :
  E8ShellParityCounts → Nat
e8ThetaCoefficient C =
  integerResidueZero C + halfResidueZero C

thetaThreeEighthPowerCoefficient :
  E8ShellParityCounts → Nat
thetaThreeEighthPowerCoefficient C =
  integerResidueZero C + integerResidueTwo C

thetaFourEighthPowerPositiveCoefficient :
  E8ShellParityCounts → Nat
thetaFourEighthPowerPositiveCoefficient C = integerResidueZero C

thetaFourEighthPowerNegativeCoefficient :
  E8ShellParityCounts → Nat
thetaFourEighthPowerNegativeCoefficient C = integerResidueTwo C

thetaTwoEighthPowerCoefficient :
  E8ShellParityCounts → Nat
thetaTwoEighthPowerCoefficient C =
  halfResidueZero C + halfResidueTwo C

thetaParityProjectorArithmetic :
  (integerZero integerTwo half : Nat) →
  2 * (integerZero + half) + integerTwo
  ≡
  (integerZero + integerTwo) + integerZero + (half + half)
thetaParityProjectorArithmetic =
  solve 3
    (λ integerZero integerTwo half →
       con 2 :* (integerZero :+ half) :+ integerTwo
       :=
       (integerZero :+ integerTwo) :+ integerZero
       :+ (half :+ half))
    refl

e8ThetaSignedJacobiProjector :
  (C : E8ShellParityCounts) →
  2 * e8ThetaCoefficient C
    + thetaFourEighthPowerNegativeCoefficient C
  ≡
  thetaThreeEighthPowerCoefficient C
    + thetaFourEighthPowerPositiveCoefficient C
    + thetaTwoEighthPowerCoefficient C
e8ThetaSignedJacobiProjector C
  rewrite sym (halfParityCancellation C) =
    thetaParityProjectorArithmetic
      (integerResidueZero C)
      (integerResidueTwo C)
      (halfResidueZero C)

-- Pointwise theorem for the whole coefficient sequence. Its mathematical
-- input is an *actual* cancellation proof for each source shell n, not a
-- finite enumeration or a new free-standing equality of theta functions.
e8ThetaSignedJacobiProjectorAllN :
  (shells : Nat → E8ShellParityCounts) →
  (n : Nat) →
  2 * e8ThetaCoefficient (shells n)
    + thetaFourEighthPowerNegativeCoefficient (shells n)
  ≡
  thetaThreeEighthPowerCoefficient (shells n)
    + thetaFourEighthPowerPositiveCoefficient (shells n)
    + thetaTwoEighthPowerCoefficient (shells n)
e8ThetaSignedJacobiProjectorAllN shells n =
  e8ThetaSignedJacobiProjector (shells n)
