module DASHI.Crypto.MLKEMProtectedLabelUncertaintyEdgeExact where

------------------------------------------------------------------------
-- ML-KEM: PROTECTED-LABEL SEARCH EDGE UNCERTAINTY PRICING
--
-- Primary cryptographic source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- This module connects the new harmonic/singular-budget obstruction to the
-- pre-existing ProtectedLabelSearchGeometry object itself.  It is the first
-- theorem in this lane whose conclusion mentions the actual edge-update cost
-- selected by a search representation.
--
-- It remains a conditional lower bound: the concrete ML-KEM edge producer must
-- prove that its update implementation charges at least the surviving output
-- residues touched by the move.  No universal runtime model is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; _+_; _*_)

import DASHI.Crypto.ProtectedLabelSearchGeometryExact as Search
import DASHI.Crypto.MLKEMUncertaintyTransitionCostBridgeExact as Bridge

------------------------------------------------------------------------
-- A proof-bearing ML-KEM interpretation of one protected-label search edge.
------------------------------------------------------------------------

record UncertaintyPricedSearchEdge
    (geometry : Search.ProtectedLabelSearchGeometry)
    (public : Search.Public geometry) : Set₁ where
  constructor uncertainty-priced-search-edge
  field
    step : Search.SearchStep geometry public

    -- Same-object support data for the candidate difference represented by
    -- this edge.  changedSupport counts changed source coefficient positions;
    -- survivingSupport counts nonzero output residues after the public map.
    changedSupport : Nat
    survivingSupport : Nat
    singularBudget : Nat

    -- Harmonic + local-matrix theorem instantiated on this exact move.
    singularBudgetUncertainty128 :
      128 ≤ changedSupport * (survivingSupport + singularBudget)

    -- Architecture-specific work premise.  The existing geometry exposes the
    -- concrete edgeUpdateCost; this field is the only additional bridge needed
    -- to turn support into transition work.
    updateCostCoversSurvivingResidues :
      survivingSupport ≤ Search.stepCost step

open UncertaintyPricedSearchEdge public

searchEdgeUncertaintyObstruction128 :
  ∀ {geometry public} →
  (priced : UncertaintyPricedSearchEdge geometry public) →
  128 ≤
    changedSupport priced *
    (Search.stepCost (step priced) + singularBudget priced)
searchEdgeUncertaintyObstruction128 priced =
  Bridge.uncertaintyToTransitionWork
    (changedSupport priced)
    (survivingSupport priced)
    (singularBudget priced)
    (Search.stepCost (step priced))
    (singularBudgetUncertainty128 priced)
    (updateCostCoversSurvivingResidues priced)

------------------------------------------------------------------------
-- Full-rank search edge: sigma = 0 is represented without needing arithmetic
-- simplification through +0 in the generic theorem.
------------------------------------------------------------------------

record FullRankUncertaintyPricedSearchEdge
    (geometry : Search.ProtectedLabelSearchGeometry)
    (public : Search.Public geometry) : Set₁ where
  constructor full-rank-uncertainty-priced-search-edge
  field
    step : Search.SearchStep geometry public
    changedSupport : Nat
    survivingSupport : Nat
    fullRankUncertainty128 :
      128 ≤ changedSupport * survivingSupport
    updateCostCoversSurvivingResidues :
      survivingSupport ≤ Search.stepCost step

open FullRankUncertaintyPricedSearchEdge public

fullRankSearchEdgeUncertaintyObstruction128 :
  ∀ {geometry public} →
  (priced : FullRankUncertaintyPricedSearchEdge geometry public) →
  128 ≤ changedSupport priced * Search.stepCost (step priced)
fullRankSearchEdgeUncertaintyObstruction128 priced =
  Bridge.fullRankUncertaintyToTransitionWork
    (changedSupport priced)
    (survivingSupport priced)
    (Search.stepCost (step priced))
    (fullRankUncertainty128 priced)
    (updateCostCoversSurvivingResidues priced)

------------------------------------------------------------------------
-- Search-radius specialization.
--
-- If the representation promises that this edge changes at most radius source
-- positions, the update geometry must satisfy the complementary product.
------------------------------------------------------------------------

boundedRadiusSearchEdgeObstruction128 :
  ∀ {geometry public} →
  (priced : UncertaintyPricedSearchEdge geometry public) →
  (radius : Nat) →
  changedSupport priced ≤ radius →
  128 ≤ radius * (Search.stepCost (step priced) + singularBudget priced)
boundedRadiusSearchEdgeObstruction128 priced radius withinRadius =
  Bridge.boundedRadiusTransitionObstruction
    (changedSupport priced)
    radius
    (Search.stepCost (step priced))
    (singularBudget priced)
    withinRadius
    (searchEdgeUncertaintyObstruction128 priced)

------------------------------------------------------------------------
-- CLAIM BOUNDARY
--
-- What is now proved conditionally:
--
--   every same-object ML-KEM search edge whose verifier work covers its
--   surviving output support obeys the sharp 128 locality/work product, with
--   singular residues appearing as an explicit defect budget.
--
-- What is NOT yet proved:
--
--   * every conceivable implementation's edge cost dominates residue support;
--   * a lower bound on the number of candidate edges required for recovery;
--   * a total ML-KEM attack runtime lower bound;
--   * computational hardness from support uncertainty alone.
--
-- The highest-alpha next producer is now concrete and implementation-facing:
-- instantiate updateCostCoversSurvivingResidues for the repository's actual
-- incremental residual verifier/update primitive.
------------------------------------------------------------------------
