module DASHI.Physics.Closure.NSTriadKNPeriodicFourierStrainL2Round34Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman; Andrew J. Majda.
-- Title: "Geometric Constraints on Potentially Singular Solutions for the
-- 3-D Euler Equations".
-- DOI: 10.1080/03605309608821197.
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations".
-- DOI: 10.1007/BF01240221.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Sum the exact Round-34 single-mode strain identity over an arbitrary finite
-- Fourier family.  Every sample carries the actual inverse-square datum and
-- transversality of its vorticity coefficient.  The result is
--
--   sum_k ||S_k omega_k||_F^2
--      = 1/2 sum_k |omega_k|^2.
--
-- There is no cutoff-dependent constant.  This is the finite Fourier L2
-- boundedness/isometry-scale part of the periodic strain package.  It does not
-- construct the physical-space principal-value kernel or its increment bound,
-- which remain necessary for directional HH-good depletion.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNPeriodicFourierStrainMultiplierRound34Exact as Strain

record TransverseStrainSample : Set where
  constructor transverse-strain-sample
  field
    modeData : V.ProjectionMode
    omega : V.Vector3
    transverse : V.dot (V.mode modeData) omega ≡ 0ℚ

open TransverseStrainSample public

sampleStrainMass : TransverseStrainSample → ℚ
sampleStrainMass sample =
  Strain.frobeniusSquared
    (Strain.fourierStrain (modeData sample) (omega sample))

sampleVorticityMass : TransverseStrainSample → ℚ
sampleVorticityMass sample =
  V.normSquared (omega sample)

sampleStrainMassExact :
  ∀ sample →
  sampleStrainMass sample
  ≡ Strain.half * sampleVorticityMass sample
sampleStrainMassExact sample =
  Strain.fourierStrainFrobeniusTransverseExact
    (modeData sample) (omega sample) (transverse sample)

sumStrainMass : List TransverseStrainSample → ℚ
sumStrainMass [] = 0ℚ
sumStrainMass (sample ∷ rest) =
  sampleStrainMass sample + sumStrainMass rest

sumVorticityMass : List TransverseStrainSample → ℚ
sumVorticityMass [] = 0ℚ
sumVorticityMass (sample ∷ rest) =
  sampleVorticityMass sample + sumVorticityMass rest

finitePeriodicStrainL2Exact :
  ∀ samples →
  sumStrainMass samples
  ≡ Strain.half * sumVorticityMass samples
finitePeriodicStrainL2Exact [] =
  ℚRing.solve []
finitePeriodicStrainL2Exact (sample ∷ rest) =
  trans
    (cong
      (λ tail → sampleStrainMass sample + tail)
      (finitePeriodicStrainL2Exact rest))
    (trans
      (cong
        (λ head → head + Strain.half * sumVorticityMass rest)
        (sampleStrainMassExact sample))
      (ℚRing.solve-∀
        (sampleVorticityMass sample)
        (sumVorticityMass rest)))

record FinitePeriodicStrainL2Certificate : Set where
  constructor finite-periodic-strain-l2-certificate
  field
    samples : List TransverseStrainSample
    exactHalfMass :
      sumStrainMass samples
      ≡ Strain.half * sumVorticityMass samples

open FinitePeriodicStrainL2Certificate public

canonicalFinitePeriodicStrainL2Certificate :
  (samples : List TransverseStrainSample) →
  FinitePeriodicStrainL2Certificate
canonicalFinitePeriodicStrainL2Certificate samples =
  finite-periodic-strain-l2-certificate
    samples
    (finitePeriodicStrainL2Exact samples)

periodicFourierStrainL2Closed : Bool
periodicFourierStrainL2Closed = true

periodicStrainKernelIncrementBoundConstructed : Bool
periodicStrainKernelIncrementBoundConstructed = false

periodicFourierStrainL2ClosedIsTrue :
  periodicFourierStrainL2Closed ≡ true
periodicFourierStrainL2ClosedIsTrue = refl

periodicStrainKernelIncrementBoundConstructedIsFalse :
  periodicStrainKernelIncrementBoundConstructed ≡ false
periodicStrainKernelIncrementBoundConstructedIsFalse = refl
