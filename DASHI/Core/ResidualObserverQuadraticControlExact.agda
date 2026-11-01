module DASHI.Core.ResidualObserverQuadraticControlExact where

------------------------------------------------------------------------
-- RESIDUAL OBSERVER CONTROL WITH CERTIFIED QUADRATIC DEPENDENCY GEOMETRY
--
-- PRIMARY CALIBRATION
--
-- Nikhil Bansal and Haotian Jiang,
-- "Decoupling via Affine Spectral-Independence: Beck-Fiala and Komlos Bounds
-- Beyond Banaszczyk", STOC 2026.
-- DOI: 10.1145/3798129.3800762.
-- arXiv:2508.03961; DOI: 10.48550/arXiv.2508.03961.
--
-- DASHI CONTRIBUTION
--
-- `ResidualObserverDependencyExact` deliberately begins with finite dependency
-- codes and Nat-valued coupling scores.  The mathematics/linear-algebra lane
-- now owns a stronger theorem surface: affine spectral-independence expressed
-- as certified quadratic domination.
--
-- This module connects the two without conflating them.  An action-indexed
-- family may provide a genuine quadratic ASI certificate.  Selection by its
-- domination factor is allowed only among proof-bearing admissible transitions
-- that preserve a required post-state capability.
--
-- No covariance or SDP is constructed here.  Those are supplied by a concrete
-- domain bridge using existing finite matrix / covariance / LDL machinery.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Core.ResidualObserverDependencyExact as Residual
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Mathematics.LinearAlgebra.AffineSpectralIndependenceQuadraticExact as ASI

CertifiedQuadraticDependency :
  Set → Set → Set → Set₁
CertifiedQuadraticDependency State Action Vector =
  State → Action → ASI.AffineSpectralIndependenceQuadraticCertificate Vector

NoWorseAffineSpectralFactor :
  ∀ {State Action Vector : Set} →
  CertifiedQuadraticDependency State Action Vector →
  State → Action → Action → Set
NoWorseAffineSpectralFactor dependency state preferred alternative =
  ASI.dominationFactor (dependency state preferred)
  ≤ ASI.dominationFactor (dependency state alternative)

noWorseAffineSpectralFactorRefl :
  ∀ {State Action Vector : Set}
    (dependency : CertifiedQuadraticDependency State Action Vector)
    state action →
  NoWorseAffineSpectralFactor dependency state action action
noWorseAffineSpectralFactorRefl dependency state action = ℚP.≤-refl

noWorseAffineSpectralFactorTrans :
  ∀ {State Action Vector : Set}
    {dependency : CertifiedQuadraticDependency State Action Vector}
    {state : State} {a b c : Action} →
  NoWorseAffineSpectralFactor dependency state a b →
  NoWorseAffineSpectralFactor dependency state b c →
  NoWorseAffineSpectralFactor dependency state a c
noWorseAffineSpectralFactorTrans = ℚP.≤-trans

record LeastAffineSpectralCapabilityPreservingChoice
    {State Action Vector : Set}
    (system : Dependency.DependentActionSystem State Action)
    (dependency : CertifiedQuadraticDependency State Action Vector)
    (capability : Residual.StateCapability State)
    (state : State) : Set₁ where
  field
    chosenAction : Action
    chosenAdmissible :
      Dependency.AdmissibleAction system state chosenAction
    chosenPreservesCapability :
      capability (Dependency.after chosenAdmissible)
    leastCertifiedFactor :
      ∀ (alternative : Action) →
      (alternativeAdmissible :
        Dependency.AdmissibleAction system state alternative) →
      capability (Dependency.after alternativeAdmissible) →
      NoWorseAffineSpectralFactor
        dependency state chosenAction alternative

open LeastAffineSpectralCapabilityPreservingChoice public

------------------------------------------------------------------------
-- Boundary:
--
-- A smaller certified domination factor is only a comparison inside this
-- supplied certificate family.  It is not automatically a better biological,
-- ontological, or discrepancy-theoretic action.  Admissibility and the chosen
-- capability are independent proof obligations, and a concrete Bansal--Jiang
-- instantiation must additionally justify the covariance/probe/SDP semantics.
------------------------------------------------------------------------
