module DASHI.Core.FutureLanguageQuadraticControlExact where

------------------------------------------------------------------------
-- FUTURE-LANGUAGE-PRESERVING QUADRATIC CONTROL
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
-- `FutureObservationLanguageQuotientExact` already owns consumer-visible future
-- trace semantics.  `ResidualObserverQuadraticControlExact` already requires a
-- post-state capability before minimizing a certified affine-spectral factor.
-- This file identifies one canonical capability constructor: preservation of a
-- specific future observation trace.
--
-- Thus a repair/control action may be compared by certified residual coupling
-- only inside the subset whose post-state still admits the required consumer
-- trace.  No domain-specific meaning of the trace is asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)

import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.ResidualObserverDependencyExact as Residual
import DASHI.Core.ResidualObserverQuadraticControlExact as QuadraticControl
import DASHI.Core.TypedDependencyCore as Dependency

RequiredFutureObservation :
  ∀ {State Action Observation : Set} →
  (system : Dependency.DependentActionSystem State Action) →
  (project : State → Observation) →
  List Action →
  Observation →
  Residual.StateCapability State
RequiredFutureObservation system project actions observation state =
  Future.FutureObservation system project state actions observation

FutureLanguageCertifiedQuadraticChoice :
  ∀ {State Action Observation Vector : Set} →
  (system : Dependency.DependentActionSystem State Action) →
  (project : State → Observation) →
  (dependency :
    QuadraticControl.CertifiedQuadraticDependency State Action Vector) →
  (requiredActions : List Action) →
  (requiredObservation : Observation) →
  State →
  Set₁
FutureLanguageCertifiedQuadraticChoice
    system project dependency requiredActions requiredObservation state =
  QuadraticControl.LeastAffineSpectralCapabilityPreservingChoice
    system
    dependency
    (RequiredFutureObservation
      system project requiredActions requiredObservation)
    state

record FutureLanguageQuadraticControlBoundary : Set₁ where
  field
    State Action Observation Vector : Set
    system : Dependency.DependentActionSystem State Action
    project : State → Observation
    dependency :
      QuadraticControl.CertifiedQuadraticDependency State Action Vector
    requiredActions : List Action
    requiredObservation : Observation

    -- Deliberately separate obligations: the trace is consumer-supplied and
    -- the quadratic certificates are domain-supplied.  This module only joins
    -- them at the action-selection boundary.
    consumerTraceSemanticsSuppliedExternally : Set
    covarianceSemanticsSuppliedExternally : Set
