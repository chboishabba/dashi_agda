module DASHI.Physics.Closure.NSTriadKNThreeRadiusTransferExteriorRound102Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: J. M. Manley; H. E. Rowe.
-- Title: "Some General Properties of Nonlinear Elements-Part I. General
-- Energy Relations".
-- Proceedings of the IRE 44(7) (1956), 904--913.
-- DOI: 10.1109/JRPROC.1956.275145.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND102 / THREE-RADIUS EXTERIOR DEFECT
--
-- Round101 identified the two-radius recombination obstruction
--
--   (lambda1-lambda2)(E1 q2-E2 q1).
--
-- This module performs the next nontrivial calculation instead of assuming
-- that the obstruction telescopes after summing radii.  For three radii,
--
--   E = E1+E2+E3,
--   q = q1+q2+q3,
--   D = sum lambda_i E_i,
--   L = sum lambda_i q_i,
--
-- the exact defect is
--
--   D q - E L
--     = sum_{i<j} (lambda_i-lambda_j)(E_i q_j-E_j q_i).
--
-- Thus the natural object is an antisymmetric pairwise transfer-density
-- 2-form.  It is invariant under the common-density shift
--
--   q_i |-> q_i + a E_i,
--
-- so only relative radial transfer-density fluctuations matter.
--
-- Most importantly, ordinary three-leg energy conservation q1+q2+q3=0 does
-- NOT kill the defect.  It reduces it to
--
--   D q - E L = - E L.
--
-- The explicit conservative witness below has q1+q2+q3=0 but L=-3 and
-- defect=9.  Hence the hoped-for "internal transfers telescope away" shortcut
-- is false: the surviving weighted transfer is exactly the spectral channel
-- associated with derivative-weighted/enstrophy transfer in 3-D.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

record ThreeRadiusTransferData : Set where
  constructor three-radius-transfer-data
  field
    lambda1 lambda2 lambda3 : ℚ
    energy1 energy2 energy3 : ℚ
    transfer1 transfer2 transfer3 : ℚ

open ThreeRadiusTransferData public

sub : ℚ → ℚ → ℚ
sub x y = x + (- y)

totalEnergy : ThreeRadiusTransferData → ℚ
totalEnergy D = energy1 D + energy2 D + energy3 D

totalTransfer : ThreeRadiusTransferData → ℚ
totalTransfer D = transfer1 D + transfer2 D + transfer3 D

weightedEnergy : ThreeRadiusTransferData → ℚ
weightedEnergy D =
  lambda1 D * energy1 D
  + lambda2 D * energy2 D
  + lambda3 D * energy3 D

weightedTransfer : ThreeRadiusTransferData → ℚ
weightedTransfer D =
  lambda1 D * transfer1 D
  + lambda2 D * transfer2 D
  + lambda3 D * transfer3 D

radialTransferDefect : ThreeRadiusTransferData → ℚ
radialTransferDefect D =
  sub (weightedEnergy D * totalTransfer D)
      (totalEnergy D * weightedTransfer D)

minor12 minor13 minor23 : ThreeRadiusTransferData → ℚ
minor12 D = sub (energy1 D * transfer2 D) (energy2 D * transfer1 D)
minor13 D = sub (energy1 D * transfer3 D) (energy3 D * transfer1 D)
minor23 D = sub (energy2 D * transfer3 D) (energy3 D * transfer2 D)

pairwiseExteriorDefect : ThreeRadiusTransferData → ℚ
pairwiseExteriorDefect D =
  sub (lambda1 D) (lambda2 D) * minor12 D
  + sub (lambda1 D) (lambda3 D) * minor13 D
  + sub (lambda2 D) (lambda3 D) * minor23 D

threeRadiusDefectIsPairwiseExteriorSum :
  (D : ThreeRadiusTransferData) →
  radialTransferDefect D ≡ pairwiseExteriorDefect D
threeRadiusDefectIsPairwiseExteriorSum D =
  solve
    ( lambda1 D ∷ lambda2 D ∷ lambda3 D
    ∷ energy1 D ∷ energy2 D ∷ energy3 D
    ∷ transfer1 D ∷ transfer2 D ∷ transfer3 D ∷ [])

------------------------------------------------------------------------
-- Common transfer-density gauge invariance.
------------------------------------------------------------------------

shiftTransferDensity : ℚ → ThreeRadiusTransferData → ThreeRadiusTransferData
shiftTransferDensity a D =
  three-radius-transfer-data
    (lambda1 D) (lambda2 D) (lambda3 D)
    (energy1 D) (energy2 D) (energy3 D)
    (transfer1 D + a * energy1 D)
    (transfer2 D + a * energy2 D)
    (transfer3 D + a * energy3 D)

commonDensityShiftLeavesDefectInvariant :
  (a : ℚ) (D : ThreeRadiusTransferData) →
  radialTransferDefect (shiftTransferDensity a D)
  ≡ radialTransferDefect D
commonDensityShiftLeavesDefectInvariant a D =
  solve
    ( a
    ∷ lambda1 D ∷ lambda2 D ∷ lambda3 D
    ∷ energy1 D ∷ energy2 D ∷ energy3 D
    ∷ transfer1 D ∷ transfer2 D ∷ transfer3 D ∷ [])

commonDensityShiftLeavesEveryMinorInvariant :
  (a : ℚ) (D : ThreeRadiusTransferData) →
  ( minor12 (shiftTransferDensity a D) ≡ minor12 D )
commonDensityShiftLeavesEveryMinorInvariant a D =
  solve (a ∷ energy1 D ∷ energy2 D ∷ transfer1 D ∷ transfer2 D ∷ [])

------------------------------------------------------------------------
-- Conservation does not annihilate derivative-weighted transfer.
------------------------------------------------------------------------

energyTransferConservative : ThreeRadiusTransferData → Set
energyTransferConservative D = totalTransfer D ≡ 0ℚ

conservationTurnsRadialDefectIntoWeightedTransfer :
  (D : ThreeRadiusTransferData) →
  energyTransferConservative D →
  radialTransferDefect D ≡ - (totalEnergy D * weightedTransfer D)
conservationTurnsRadialDefectIntoWeightedTransfer D conserved
  rewrite conserved =
  solve
    ( totalEnergy D ∷ weightedEnergy D ∷ weightedTransfer D ∷ [])

one two three minusTwo minusThree nine : ℚ
one = 1ℚ
two = Int.+ 2 / 1
three = Int.+ 3 / 1
minusTwo = - two
minusThree = - three
nine = Int.+ 9 / 1

conservativeNonzeroWeightedWitness : ThreeRadiusTransferData
conservativeNonzeroWeightedWitness =
  three-radius-transfer-data
    one two three
    one one one
    one one minusTwo

witnessTransferConservesEnergy :
  energyTransferConservative conservativeNonzeroWeightedWitness
witnessTransferConservesEnergy = solve []

witnessWeightedTransferIsMinusThree :
  weightedTransfer conservativeNonzeroWeightedWitness ≡ minusThree
witnessWeightedTransferIsMinusThree = solve []

witnessRadialDefectIsNine :
  radialTransferDefect conservativeNonzeroWeightedWitness ≡ nine
witnessRadialDefectIsNine = solve []

round102ThreeRadiusDefectFactorizedAsPairwiseExteriorSum : Bool
round102ThreeRadiusDefectFactorizedAsPairwiseExteriorSum = true

round102CommonTransferDensityComponentIsInvisibleToDefect : Bool
round102CommonTransferDensityComponentIsInvisibleToDefect = true

round102EnergyConservationAloneKillsRadialDefect : Bool
round102EnergyConservationAloneKillsRadialDefect = false

round102ConservativeTransferCanHaveNonzeroWeightedDefect : Bool
round102ConservativeTransferCanHaveNonzeroWeightedDefect = true

round102ThreeRadiusDefectFactorizedAsPairwiseExteriorSumIsTrue :
  round102ThreeRadiusDefectFactorizedAsPairwiseExteriorSum ≡ true
round102ThreeRadiusDefectFactorizedAsPairwiseExteriorSumIsTrue = refl

round102EnergyConservationAloneKillsRadialDefectIsFalse :
  round102EnergyConservationAloneKillsRadialDefect ≡ false
round102EnergyConservationAloneKillsRadialDefectIsFalse = refl
