module DASHI.Physics.Closure.NSTriadKNYuFiniteRelativeFilterScaleExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier--Stokes Equations".
-- arXiv DOI: 10.48550/arXiv.2606.27560.
--
-- PURPOSE
-- Formalise the algebra behind the paper's fixed-relative-filter statement.
-- If
--
--   ell = sigma r,
--
-- then simultaneous physical scaling r -> mu r and ell -> mu ell leaves
-- sigma unchanged.  Consequently the fifth-power relative loss sigma^(-5)
-- is independent of the physical scale.  This is the scale geometry relevant
-- to comparable shells: the ratio is fixed even as the dyadic radius tends
-- to zero.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

record RelativeFilterGeometry : Set where
  constructor relative-filter-geometry
  field
    physicalRadius filterLength relativeRatio commonScale : ℚ
    filterIsRelativeRadius :
      filterLength ≡ relativeRatio * physicalRadius

open RelativeFilterGeometry public

scaledRadius : RelativeFilterGeometry → ℚ
scaledRadius geometry =
  commonScale geometry * physicalRadius geometry

scaledFilterLength : RelativeFilterGeometry → ℚ
scaledFilterLength geometry =
  commonScale geometry * filterLength geometry

commonScalingPreservesRelativeFilter :
  (geometry : RelativeFilterGeometry) →
  scaledFilterLength geometry
  ≡ relativeRatio geometry * scaledRadius geometry
commonScalingPreservesRelativeFilter geometry
  rewrite filterIsRelativeRadius geometry =
  solve
    ( commonScale geometry
    ∷ relativeRatio geometry
    ∷ physicalRadius geometry
    ∷ [])

fifthPower : ℚ → ℚ
fifthPower value =
  value * value * value * value * value

record InverseRelativeFilter : Set where
  constructor inverse-relative-filter
  field
    geometry : RelativeFilterGeometry
    inverseRatio : ℚ
    ratioInverseIdentity :
      relativeRatio geometry * inverseRatio ≡ 1ℚ

open InverseRelativeFilter public

relativeFilterLoss : InverseRelativeFilter → ℚ
relativeFilterLoss witness = fifthPower (inverseRatio witness)

-- The loss has no physical-radius argument: once the ratio and its inverse are
-- fixed, common parabolic rescaling cannot create an additional dyadic power.
relativeFilterLossIsScaleIndependent :
  (witness : InverseRelativeFilter) →
  relativeFilterLoss witness ≡ fifthPower (inverseRatio witness)
relativeFilterLossIsScaleIndependent witness = solve (inverseRatio witness ∷ [])
