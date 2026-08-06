module DASHI.Physics.Closure.NSTriadKNLuoGalerkinUniformLimitContinuationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Rupert L. Frank; Fedor Sukochev; Dmitriy Zanin.
-- Title: "Endpoint Schatten Class Properties of Commutators".
-- Advances in Mathematics 450 (2024), article 109738.
-- DOI: 10.1016/j.aim.2024.109738.
-- arXiv DOI: 10.48550/arXiv.2405.10652.
--
-- Classical PDE references:
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- PURPOSE
-- Formalise the exact order-theoretic last step in the proposed Galerkin
-- strategy.  A family of finite truncations obeys one uniform terminal bound.
-- If the physical limit is lower-semicontinuous along a selected convergent
-- Galerkin subsequence, then the same bound holds at the limit.
--
-- The module does not manufacture compactness or convergence.  It removes all
-- ambiguity about what the analytic Galerkin limit must provide.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)
import Data.Rational.Properties as ℚₚ

record GalerkinUniformLimitData : Set where
  constructor galerkin-uniform-limit-data
  field
    approximationSquared : Nat → ℚ
    physicalLimitSquared uniformTerminalBound : ℚ

    uniformApproximationBound :
      (cutoff : Nat) →
      approximationSquared cutoff ≤ uniformTerminalBound

    selectedCutoff : Nat

    lowerSemicontinuityAtSelectedCutoff :
      physicalLimitSquared
      ≤ approximationSquared selectedCutoff

open GalerkinUniformLimitData public

galerkinUniformBoundPassesToLimit :
  (dataSet : GalerkinUniformLimitData) →
  physicalLimitSquared dataSet
  ≤ uniformTerminalBound dataSet
galerkinUniformBoundPassesToLimit dataSet =
  ℚₚ.≤-trans
    (lowerSemicontinuityAtSelectedCutoff dataSet)
    (uniformApproximationBound dataSet (selectedCutoff dataSet))

record GalerkinContinuationLimitData : Set where
  constructor galerkin-continuation-limit-data
  field
    limitData : GalerkinUniformLimitData
    continuationThreshold : ℚ

    uniformBoundBelowThreshold :
      uniformTerminalBound limitData ≤ continuationThreshold

open GalerkinContinuationLimitData public

physicalLimitBelowContinuationThreshold :
  (dataSet : GalerkinContinuationLimitData) →
  physicalLimitSquared (limitData dataSet)
  ≤ continuationThreshold dataSet
physicalLimitBelowContinuationThreshold dataSet =
  ℚₚ.≤-trans
    (galerkinUniformBoundPassesToLimit (limitData dataSet))
    (uniformBoundBelowThreshold dataSet)
