module DASHI.Governance.MinimalSufficientObservationGovernanceExact where

------------------------------------------------------------------------
-- SOURCE / CROSS-POLLINATION CALIBRATION
--
-- Author: David Blackwell.
-- Title: "Equivalent Comparisons of Experiments".
-- Venue: The Annals of Mathematical Statistics 24(2):265--272 (1953).
-- DOI: 10.1214/aoms/1177729032.
--
-- Authors: Patrick Cousot; Radhia Cousot.
-- Title: "Abstract interpretation: a unified lattice model for static analysis
-- of programs by construction or approximation of fixpoints".
-- Venue: POPL 1977:238--252.
-- DOI: 10.1145/512950.512973.
--
-- These sources motivate information comparison / abstraction vocabulary.
-- The universal property below already exists constructively in DASHI's
-- FutureObservationLanguageQuotientExact; this module exposes its governance
-- interpretation: a presented canonical future quotient is a coarsest safe
-- summary among SECTIONED future-language-safe projections, in the precise
-- factorization direction proved below.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Governance.DevelopmentalInfluenceSourceAtlas as Sources

record MinimalFutureSafeObservation
    {State Action Observation : Set}
    (system : Dependency.DependentActionSystem State Action)
    (project : State → Observation) : Set₁ where
  constructor minimalFutureSafeObservation
  field
    presentation : Future.FutureEquivalencePresentation system project

    factorsFromEverySectionedSafeProjection :
      ∀ {Coarse : Set}
        {coarsen : State → Coarse} →
      Future.FutureLanguageSafeProjection system project coarsen →
      Future.SectionedProjection coarsen →
      Future.FactorizationThroughFutureQuotient presentation

open MinimalFutureSafeObservation public

canonicalPresentationIsMinimalFutureSafe :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation} →
  (presentation : Future.FutureEquivalencePresentation system project) →
  MinimalFutureSafeObservation system project
canonicalPresentationIsMinimalFutureSafe presentation =
  minimalFutureSafeObservation presentation
    (λ safe sectioned →
      Future.sectionedSafeProjectionFactors presentation safe sectioned)

------------------------------------------------------------------------
-- Meaning of the factorization direction.
--
-- For any sectioned safe representation q : State -> Coarse there exists
-- factor : Coarse -> CanonicalCode such that
--
--     classOf = factor ∘ q.
--
-- Thus q may retain MORE distinctions than necessary, but it cannot safely
-- collapse a distinction that canonical future equivalence still needs.
------------------------------------------------------------------------

record MinimalObservationBoundary : Set where
  constructor minimalObservationBoundary
  field
    canonicalFutureCodeFactorsThroughEverySectionedSafeProjection : Bool
    everySafeProjectionMustEqualCanonicalCode : Bool
    safeProjectionMayRetainExtraDistinctions : Bool
    minimalityIsRelativeToDeclaredActionObservationLanguage : Bool
    canonicalCodeMeansUniversalOntologicalIdentity : Bool
    sectionRequirementIsExplicit : Bool

canonicalMinimalObservationBoundary : MinimalObservationBoundary
canonicalMinimalObservationBoundary =
  minimalObservationBoundary true false true true false true

record MinimalObservationSourceReceipt : Set where
  constructor minimalObservationSourceReceipt
  field
    sources : List Sources.ScholarlySource
    boundary : MinimalObservationBoundary

canonicalMinimalObservationSourceReceipt : MinimalObservationSourceReceipt
canonicalMinimalObservationSourceReceipt =
  minimalObservationSourceReceipt
    (Sources.blackwellExperimentComparison
      ∷ Sources.cousotAbstractInterpretation
      ∷ [])
    canonicalMinimalObservationBoundary
