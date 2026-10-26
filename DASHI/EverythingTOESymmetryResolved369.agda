module DASHI.EverythingTOESymmetryResolved369 where

------------------------------------------------------------------------
-- Focused TOE aggregate: generic symmetry-resolved fibre calculus plus the
-- existing SSP/369 representation-reduction and physics instances.
------------------------------------------------------------------------

import DASHI.Core.SymmetryResolvedFibreExact
import DASHI.EverythingSSPRepresentationReductionRound9
import DASHI.Physics.Closure.TOESymmetryResolved369BridgeExact

-- Reuse the existing TOE parents. Do not replace their carriers.
import DASHI.Unifier
import DASHI.Unified.PNFHyperfabric
import DASHI.Unified.Physics

-- Existing exact finite source obligations. These imports do not claim
-- a wild exterior equivalence, Euclidean meridian bound, or physical W.
-- Alexander/Hatcher are the topology roots. The stage/ribbon sources
-- belong to the existing hyperfabric PR. PL surface donors belong to
-- the separate exotic-topology PR; they are not copied here.
import DASHI.Unified.HornStageClearanceC3SourceCutExact
import DASHI.Mathematics.Topology.HatcherRibbonPeripheralBoundaryExact
