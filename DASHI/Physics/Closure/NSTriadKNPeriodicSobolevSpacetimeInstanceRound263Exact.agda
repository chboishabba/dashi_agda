module DASHI.Physics.Closure.NSTriadKNPeriodicSobolevSpacetimeInstanceRound263Exact where

------------------------------------------------------------------------
-- ROUND263 / LEAF A: PERIODIC SOBOLEV, HOLDER, AND MONOTONE INTEGRATION
--
-- BIDI BACKWARD NEED
-- R249/R251 consume only:
--   ||H u x u||_2^2 <= ||H u||_6^2 ||u||_3^2,
--   ||u||_3^2 <= C_(1/2) ||u||_{H^(1/2)}^2,
--   ||H u||_6^2 <= C_1 ||u||_{H^1}^2,
-- plus monotonicity of time integration under a critical barrier.
--
-- FORWARD MATHEMATICS
-- On T^3 these are the standard Holder inequality and Sobolev embeddings
-- H^(1/2)(T^3) -> L^3(T^3), H^1(T^3) -> L^6(T^3). R247 supplies the
-- repo-specific normalized-curl H^1 isometry, so no multiplier theorem for H
-- is required. Pointwise domination then integrates monotonically.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNStandardPeriodicSobolevW1Round249Exact as R249
import DASHI.Physics.Closure.NSTriadKNStandardSpacetimeW1AndFirstHitW3Round251Exact as R251

record PeriodicSobolevSpacetimeInstance
    (Time : Set)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (mixedMass criticalSize dissipationDensity : Nat → Time → ℚ)
    : Set₁ where
  field
    periodicPointwise :
      R249.StandardPeriodicW1Authority
        Time mixedMass criticalSize dissipationDensity

    monotoneSpacetime :
      R251.StandardSpacetimeW1Authority
        Time integrateTo mixedMass criticalSize dissipationDensity
        periodicPointwise

open PeriodicSobolevSpacetimeInstance public

round263LeafAStandardPeriodicAnalysisInstantiated : Bool
round263LeafAStandardPeriodicAnalysisInstantiated = true

round263NormalizedCurlHOneGeometryReusedNotReproved : Bool
round263NormalizedCurlHOneGeometryReusedNotReproved = true

round263ContinuumAnalysisKernelDerivedInFiniteAgda : Bool
round263ContinuumAnalysisKernelDerivedInFiniteAgda = false

round263PackageAClosedByLeafAAlone : Bool
round263PackageAClosedByLeafAAlone = false

round263LeafAStandardPeriodicAnalysisInstantiatedIsTrue :
  round263LeafAStandardPeriodicAnalysisInstantiated ≡ true
round263LeafAStandardPeriodicAnalysisInstantiatedIsTrue = refl
