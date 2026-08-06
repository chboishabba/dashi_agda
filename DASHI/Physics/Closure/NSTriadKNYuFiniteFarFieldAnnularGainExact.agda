module DASHI.Physics.Closure.NSTriadKNYuFiniteFarFieldAnnularGainExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier--Stokes Equations".
-- arXiv DOI: 10.48550/arXiv.2606.27560.
--
-- Littlewood--Paley reference:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Identify the exact common dyadic arithmetic in Yu's far-field annular
-- decomposition and the repository's high--high to low estimate.  An annulus
-- separated by m dyadic steps carries the coefficient 2^(-3m/2).  Squaring
-- it gives 2^(-3m), whose finite prefixes are bounded by 8/7.
--
-- The imported theorem already proves both the calibration and the geometric
-- sum.  This module exposes the source-faithful aliases so the same exact
-- result is reused rather than copied.  The weighted continuum far-field
-- closure remains a separate producer because Yu's unweighted estimate still
-- carries a scale loss.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighHighLowBernsteinGainExact as HH

squaredFarFieldAnnularGain : Nat → ℚ
squaredFarFieldAnnularGain = HH.squaredBernsteinGapGain

farFieldCubicScale : Nat → ℚ
farFieldCubicScale = HH.cubicInputGapScale

farFieldAnnularCalibration :
  (annulus : Nat) →
  squaredFarFieldAnnularGain annulus
    * farFieldCubicScale annulus
  ≡ 1ℚ
farFieldAnnularCalibration = HH.squaredBernsteinGapCalibration

squaredFarFieldPrefix : Nat → ℚ
squaredFarFieldPrefix = HH.squaredBernsteinGainPrefix

squaredFarFieldPrefixBound :
  (cutoff : Nat) →
  squaredFarFieldPrefix cutoff ≤ HH.eightSevenths
squaredFarFieldPrefixBound = HH.squaredBernsteinGainPrefixBound
