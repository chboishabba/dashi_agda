module DASHI.Physics.Gravity.KSW668F8ThreeModeWeightedNormalEnergyReynoldsExact where

------------------------------------------------------------------------
-- XL: exact SAME-CARRIER 3-mode positive-shell direct sum adapter.
--
-- Reuse mathematical donor: PolynomialC3S3OrbitSamplingProjectionExact
-- and TernaryPermutationS3LawsExact. Only the abstract REYNOLDS
-- relabeling pattern transfers; their 27-trit objects do not.
--
-- Each original effective radial dimension (d=3,7,11) has its OWN
-- positive shell-volume mass W_d,j. Normal/warp/SAT semidiscrete
-- expressions have the same mode-INDEPENDENT form; apply one proof
-- three times and sum weighted by the actual masses.
--
-- Rotating weights AND fields together preserves the symbolic sum;
-- rotating fields alone is NOT a physical symmetry, as the previous
-- F8C3S3ModeReynoldsRadialObstructionExact owner proves at r=0.
--
-- This is exact rational equality, not an Agda order proof of
-- positivity, coupled radial energy stability, or physical FIO.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Gravity.KSW668F8C3S3ModeReynoldsRadialObstructionExact as Modes
import DASHI.Physics.Gravity.KSW668F8MovingWarpEnergyCancellationDefectExact as Warp

open Modes using (Triple; triple; rotate; map3)

weightedSum3 : Triple ℚ → Triple ℚ → ℚ
weightedSum3 (triple w0 w2 w4) (triple x0 x2 x4) =
  w0 * x0 + w2 * x2 + w4 * x4

-- The only legitimate S3/C3 'symmetry' of the MODE-DEPENDENT
-- inner product is simultaneous relabeling of radial masses.
originalWeightedSumSimultaneousC3 :
  (w0 w2 w4 x0 x2 x4 : ℚ) →
  weightedSum3
    (rotate (triple w0 w2 w4))
    (rotate (triple x0 x2 x4))
    ≡ weightedSum3 (triple w0 w2 w4) (triple x0 x2 x4)
originalWeightedSumSimultaneousC3 w0 w2 w4 x0 x2 x4
  = solve []

-- Sum any preverified per-mode energy/source ledger without
-- falsely setting the three radial masses equal.
originalThreeModeLedgerDistribution :
  (w0 w2 w4 e0 e2 e4 f0 f2 f4 : ℚ) →
  weightedSum3 (triple w0 w2 w4)
    (triple (e0 + f0) (e2 + f2) (e4 + f4))
  ≡ weightedSum3 (triple w0 w2 w4)
      (triple e0 e2 e4)
    + weightedSum3 (triple w0 w2 w4)
      (triple f0 f2 f4)
originalThreeModeLedgerDistribution
  w0 w2 w4 e0 e2 e4 f0 f2 f4 = solve []

-- For each physical shell, the exact normal+warp defect is the
-- same function with separately measured C/J values.
modeNormalDefect :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
modeNormalDefect v cp cm jp jm =
  Warp.uncancelledDiscreteWarpDefect v cp cm jp jm

originalThreeModeNormalWarpResidual :
  (v : ℚ) →
  (weights : Triple ℚ) →
  (cP cM jP jM : Triple ℚ) → ℚ
originalThreeModeNormalWarpResidual v
  (triple w0 w2 w4)
  (triple cp0 cp2 cp4)
  (triple cm0 cm2 cm4)
  (triple jp0 jp2 jp4)
  (triple jm0 jm2 jm4) =
    w0 * modeNormalDefect v cp0 cm0 jp0 jm0
    + w2 * modeNormalDefect v cp2 cm2 jp2 jm2
    + w4 * modeNormalDefect v cp4 cm4 jp4 jm4

originalThreeModeNormalWarpResidualC3Relabel :
  (v w0 w2 w4 cp0 cp2 cp4 cm0 cm2 cm4
     jp0 jp2 jp4 jm0 jm2 jm4 : ℚ) →
  originalThreeModeNormalWarpResidual v
    (triple w0 w2 w4)
    (triple cp0 cp2 cp4)
    (triple cm0 cm2 cm4)
    (triple jp0 jp2 jp4)
    (triple jm0 jm2 jm4)
  ≡ originalThreeModeNormalWarpResidual v
      (rotate (triple w0 w2 w4))
      (rotate (triple cp0 cp2 cp4))
      (rotate (triple cm0 cm2 cm4))
      (rotate (triple jp0 jp2 jp4))
      (rotate (triple jm0 jm2 jm4))
originalThreeModeNormalWarpResidualC3Relabel
  v w0 w2 w4 cp0 cp2 cp4 cm0 cm2 cm4 jp0 jp2 jp4 jm0 jm2 jm4
  = solve []

-- The certified right-hand side of the all-mode bound is
-- (12/b) sum_{mode,shell} W_dj E_mode,j. The order step uses
-- W_dj>0 and each per-mode |R_mode|<=12 E_mode/b;
-- this source owner only proves algebraic combination.
reconstructedNormalEnergyBoundRightHandSide :
  ℚ → Triple ℚ → Triple ℚ → ℚ
reconstructedNormalEnergyBoundRightHandSide invb masses energies =
  ((+ 12) / 1) * invb * weightedSum3 masses energies

-- YM S^3 signed-permutation cubature cannot prove a pointwise
-- anisotropic energy is positive by *averaging* it. Even the
-- quadratic q0²-q1² changes sign on rational unit vectors.
ymS3AnisotropicPositiveWitness :
  (((+ 1) / 1) * ((+ 1) / 1)
     + - (((+ 0) / 1) * ((+ 0) / 1)))
    ≡ (+ 1) / 1
ymS3AnisotropicPositiveWitness = solve []

ymS3AnisotropicNegativeWitness :
  (((+ 0) / 1) * ((+ 0) / 1)
     + - (((+ 1) / 1) * ((+ 1) / 1)))
    ≡ - ((+ 1) / 1)
ymS3AnisotropicNegativeWitness = solve []
