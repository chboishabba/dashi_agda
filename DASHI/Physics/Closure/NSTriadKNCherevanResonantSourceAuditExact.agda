module DASHI.Physics.Closure.NSTriadKNCherevanResonantSourceAuditExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Pylyp Cherevan.
-- Title: "Log-free estimate for the resonant paraproduct in the 3D
-- Navier--Stokes equations".
-- arXiv:2510.06246v1 (3 October 2025).
-- arXiv DOI: 10.48550/arXiv.2510.06246.
--
-- PURPOSE
-- Record the theorem surface of the supplied preprint without importing any
-- of its analytic claims as axioms.  The source uses the same letter N/lambda
-- for several mathematically distinct roles:
--
-- * the output dyad in the definition of R_N;
-- * the high input dyad in the later high--high analysis;
-- * a sub-unit cutoff |xi+eta| <= lambda^{-delta}.
--
-- It also states a pointwise-in-time theorem while its proposed mechanism is
-- spacetime and evolutionary.  These are genuine bridge obligations, not
-- notational variants.  The finite no-confusion theorems below keep those
-- lanes separate before any continuum theorem can be promoted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

_≢_ : ∀ {A : Set} → A → A → Set
left ≢ right = left ≡ right → ⊥

data FrequencyIndexRole : Set where
  projectedOutputDyad : FrequencyIndexRole
  highInputDyad : FrequencyIndexRole
  subunitNarrowCutoff : FrequencyIndexRole

paperMainDefinitionRole : FrequencyIndexRole
paperMainDefinitionRole = projectedOutputDyad

paperNarrowAnalysisRole : FrequencyIndexRole
paperNarrowAnalysisRole = highInputDyad

paperNarrowCutoffRole : FrequencyIndexRole
paperNarrowCutoffRole = subunitNarrowCutoff

outputRoleIsNotInputRole :
  paperMainDefinitionRole ≢ paperNarrowAnalysisRole
outputRoleIsNotInputRole ()

outputRoleIsNotSubunitCutoffRole :
  paperMainDefinitionRole ≢ paperNarrowCutoffRole
outputRoleIsNotSubunitCutoffRole ()

data EstimateLane : Set where
  pointwiseSpatialLane : EstimateLane
  spacetimeEvolutionLane : EstimateLane

paperTheoremLane : EstimateLane
paperTheoremLane = pointwiseSpatialLane

paperMechanismLane : EstimateLane
paperMechanismLane = spacetimeEvolutionLane

pointwiseClaimIsNotSpacetimeEstimate :
  paperTheoremLane ≢ paperMechanismLane
pointwiseClaimIsNotSpacetimeEstimate ()

record PointwiseFromSpacetimeBridge : Set₁ where
  field
    pointwiseStatement : Set
    spacetimeStatement : Set
    transfer : spacetimeStatement → pointwiseStatement

-- No bridge is manufactured.  Any later use of an evolutionary estimate to
-- prove the stated pointwise theorem must provide an inhabitant of the record
-- above, with all trace/maximal-function hypotheses visible.
