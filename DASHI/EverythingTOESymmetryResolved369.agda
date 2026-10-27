module DASHI.EverythingTOESymmetryResolved369 where

------------------------------------------------------------------------
-- Focused TOE aggregate: generic symmetry-resolved fibre calculus plus the
-- existing SSP/369 representation-reduction and physics instances.
------------------------------------------------------------------------

import DASHI.Core.SymmetryResolvedFibreExact
import DASHI.EverythingSSPRepresentationReductionRound9
import DASHI.Physics.Closure.TOESymmetryResolved369BridgeExact

-- Reuse the existing exact finite GR/quantum proof-term regression.
-- It contains a terminal physical non-promotion theorem.
-- Do not replace this import with DASHI.Unifier placeholder axioms.
import DASHI.Unified.GRQuantumProofTermRegression

-- Reuse exact current YM/RH non-promotion proofs.
-- The bridge imports theorem-bearing owners only.
-- It does not identify YM with RH and does not promote either lane to TOE.
import DASHI.Unified.YMRHNonPromotionTOEBridgeExact
