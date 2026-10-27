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
import DASHI.Unified.GRQuantumProofTermRegression

-- Exact complexity non-promotion and simulation-preservation gates.
import DASHI.Unified.ResidualWidthNonPromotionTOEExact
