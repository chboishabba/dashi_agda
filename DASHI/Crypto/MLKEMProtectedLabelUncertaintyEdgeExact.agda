module DASHI.Crypto.MLKEMProtectedLabelUncertaintyEdgeExact where

------------------------------------------------------------------------
-- ML-KEM: PROTECTED-LABEL SEARCH EDGE UNCERTAINTY PRICING
--
-- Primary cryptographic source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Finite-field uncertainty source used by the upstream support theorem:
-- Martino Borello; Patrick Sole,
-- "The uncertainty principle over finite fields",
-- Discrete Mathematics 345 (2022), 112670.
-- DOI: 10.1016/j.disc.2021.112670.
--
-- This module connects the harmonic/singular-budget obstruction to the
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
-- CLAIM BOUNDARY / CURRENT STATUS
--
-- What is proved conditionally:
--
--   every same-object ML-KEM search edge whose charged update work covers its
--   surviving output support obeys the 128 locality/work product, with singular
--   residues appearing as an explicit defect budget.
--
-- Round 17 now provides a concrete producer for one important verifier class:
-- an explicitly materialised exact residual state.  The residual-touch theorem
-- proves changed cells are touched, and the path theorem aggregates that exact
-- resource along a traversal.  Thus the implementation-facing bridge is no
-- longer wholly abstract.
--
-- What is NOT yet proved:
--
--   * the FIPS-specific support/singularity certificate for every actual edge;
--   * the same domination theorem for lazy/compressed/symbolic verifier states;
--   * a lower bound on the number of candidate edges required for recovery;
--   * a generic total ML-KEM attack runtime lower bound;
--   * computational hardness from support uncertainty alone.
--
-- The parallel sufficient-state/readout-capacity and CBD average-success lanes
-- now handle the first representation-independent information seam.  The next
-- source-facing closure is to instantiate both sides on one concrete verifier.
------------------------------------------------------------------------
