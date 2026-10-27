module DASHI.EverythingTOESymmetryResolved369 where

------------------------------------------------------------------------
-- Focused TOE aggregate: generic symmetry-resolved fibre calculus plus the
-- existing SSP/369 representation-reduction and physics instances.
------------------------------------------------------------------------

import DASHI.Core.SymmetryResolvedFibreExact
import DASHI.EverythingSSPRepresentationReductionRound9
import DASHI.Physics.Closure.TOESymmetryResolved369BridgeExact

-- Exact Yang-Mills finite plaquette and non-promotion convergence.
import DASHI.Physics.YangMills.YangMillsPlaquetteTOEBridgeExact
import DASHI.Physics.YangMills.YangMillsPlaquetteTOEBridgeValidation


-- Normalized Balaban RG, regular-E, Casimir, stress, A/B/C, and non-promotion TOE surface.
import DASHI.Physics.YangMills.YangMillsTOEConvergenceRound559Exact
import DASHI.Physics.YangMills.YangMillsTOEConvergenceRound559Validation
