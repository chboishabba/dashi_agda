{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSMillerAnisotropicA3BridgeExact where

-- Evan Miller (2021), Proc. AMS Series B 8, 60-74,
-- DOI 10.1090/bproc/74, Theorem 1.6 / Theorem 2.1.
-- SOURCE-BOUNDED ADAPTER: the published conditional criterion pertains to
-- unforced 3D whole-space mild Navier-Stokes with viscosity normalized to 1,
-- a SAME-SOLUTION unit direction field v with suitable spatial Lipschitz
-- regularity, and finite L^4_t L^2_x expenditure of v cross vorticity.
-- Both gradient and projection predicates are pinned to the same selected
-- trajectory/time horizon; a gradient estimate from a different solution
-- cannot inhabit the selected source's direction hypothesis.
-- These are externally fixed physical predicates, NOT convenient placeholders
-- that the bridge is entitled to inhabit. A canonical A3 handoff requires
-- an additional explicit physical/semantic implication.
-- This file does not infer any of the critical bounds from basic energy.

import DASHI.Physics.Closure.NSCanonicalA3ContinuationResidualExact as A3

record MillerPhysicalPremises
    (PhysicalSource Direction : Set)
    (selectedSource : PhysicalSource)
    (selectedDirection : Direction)
    (MildUnforcedR3 : PhysicalSource → Set)
    (UnitSpatialDirection : Direction → Set)
    (SameSolutionDirection : PhysicalSource → Direction → Set)
    (SpatialGradientBoundedUntilTime : PhysicalSource → Direction → Set)
    (CriticalProjectedVorticityFinite :
      PhysicalSource → Direction → Set) : Set where
  field
    mildUnforcedSolution : MildUnforcedR3 selectedSource
    unitDirection : UnitSpatialDirection selectedDirection
    directionBelongsToSolution :
      SameSolutionDirection selectedSource selectedDirection
    gradientBound : SpatialGradientBoundedUntilTime selectedSource selectedDirection
    projectedVorticityBound :
      CriticalProjectedVorticityFinite selectedSource selectedDirection

-- The SOURCE theorem and the CANONICAL consumer are independent statements:
-- neither arbitrary historical Round equality nor a generic energy estimate
-- identifies their source objects, domain or continuation semantics.
millerPremisesToCanonicalA3 :
  {PhysicalSource Direction : Set} →
  (selectedSource : PhysicalSource) →
  (selectedDirection : Direction) →
  (MildUnforcedR3 : PhysicalSource → Set) →
  (UnitSpatialDirection : Direction → Set) →
  (SameSolutionDirection : PhysicalSource → Direction → Set) →
  (SpatialGradientBoundedUntilTime : PhysicalSource → Direction → Set) →
  (CriticalProjectedVorticityFinite :
    PhysicalSource → Direction → Set) →
  (MillerConclusion : PhysicalSource → Set) →
  (CanonicalA3Continuation : PhysicalSource → Set) →
  (publishedMillerImplication :
    MillerPhysicalPremises
      PhysicalSource Direction selectedSource selectedDirection
      MildUnforcedR3 UnitSpatialDirection SameSolutionDirection
      SpatialGradientBoundedUntilTime CriticalProjectedVorticityFinite
    → MillerConclusion selectedSource) →
  (sameSourceA3Transfer :
    MillerConclusion selectedSource →
    CanonicalA3Continuation selectedSource) →
  MillerPhysicalPremises
    PhysicalSource Direction selectedSource selectedDirection
    MildUnforcedR3 UnitSpatialDirection SameSolutionDirection
    SpatialGradientBoundedUntilTime CriticalProjectedVorticityFinite →
  A3.CanonicalA3ContinuationResidual
    PhysicalSource selectedSource CanonicalA3Continuation
millerPremisesToCanonicalA3
  selectedSource selectedDirection
  MildUnforcedR3 UnitSpatialDirection SameSolutionDirection
  SpatialGradientBoundedUntilTime CriticalProjectedVorticityFinite
  MillerConclusion CanonicalA3Continuation
  publishedMillerImplication sameSourceA3Transfer premises =
  record
    { continuationCriterionLiteralNS =
        sameSourceA3Transfer (publishedMillerImplication premises)
    }
