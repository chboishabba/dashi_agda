module DASHI.Architecture.SemiconductorBuiltEnvironmentCrossPollinationExact where

open import DASHI.Core.Prelude
import DASHI.Architecture.SpatialRealisationExact as Spatial

------------------------------------------------------------------------
-- SEMICONDUCTOR / BUILT-ENVIRONMENT CROSS-POLLINATION
--
-- Verilog/SystemVerilog and BIM are not identified.  They occupy analogous
-- design-description-to-realisation pipelines at different semantic levels.
-- The reusable mathematics is spatial allocation, routing, capacity, staged
-- refinement, signoff/admissibility, and revision under downstream feedback.
------------------------------------------------------------------------

data ChipRepresentation : Set where
  rtl netlist floorplan placementRouting maskGeometry fabricatedChip :
    ChipRepresentation

data BuiltRepresentation : Set where
  brief coordinatedModel technicalModel construction asBuilt :
    BuiltRepresentation

nextChip : ChipRepresentation → ChipRepresentation
nextChip rtl = netlist
nextChip netlist = floorplan
nextChip floorplan = placementRouting
nextChip placementRouting = maskGeometry
nextChip maskGeometry = fabricatedChip
nextChip fabricatedChip = fabricatedChip

nextBuilt : BuiltRepresentation → BuiltRepresentation
nextBuilt brief = coordinatedModel
nextBuilt coordinatedModel = technicalModel
nextBuilt technicalModel = construction
nextBuilt construction = asBuilt
nextBuilt asBuilt = asBuilt

data Domain : Set where
  town building fab wafer chip : Domain

-- Nested realised carriers: a city can contain a fab; the fab provides the
-- execution environment for wafer fabrication; the process fabricates chips.

data Contains : Domain → Domain → Set where
  townContainsBuilding : Contains town building
  townContainsFab      : Contains town fab
  fabContainsWafer     : Contains fab wafer
  waferProducesChip    : Contains wafer chip

record DesignExecutionSystem : Set₁ where
  field
    Intent      : Set
    Model       : Set
    Constraint  : Set
    Plan        : Set
    Execution   : Set
    Observation : Set

    represent : Intent → Model
    schedule  : Model → Plan
    execute   : Plan → Execution
    observe   : Execution → Observation

open DesignExecutionSystem public

------------------------------------------------------------------------
-- Representation correctness, execution correctness and outcome success are
-- deliberately separate proof obligations.
------------------------------------------------------------------------

record RealisationReceipt (system : DesignExecutionSystem) : Set₁ where
  field
    representationCorrect : Set
    executionCorrect      : Set
    outcomeSuccessful     : Set

open RealisationReceipt public

data RepresentationCorrectnessImpliesOutcomeSuccessPermission : Set where

representationCorrectnessDoesNotAutoPromoteToOutcomeSuccess :
  RepresentationCorrectnessImpliesOutcomeSuccessPermission → ⊥
representationCorrectnessDoesNotAutoPromoteToOutcomeSuccess ()

------------------------------------------------------------------------
-- Cross-domain theorem owner: any concrete chip, building or town spatial
-- system can reuse the generic local-vs-global routability distinction.
------------------------------------------------------------------------

localPlacementCannotAutoCloseGlobalRouting :
  Spatial.LocalValidityImpliesGlobalRoutabilityPermission → ⊥
localPlacementCannotAutoCloseGlobalRouting =
  Spatial.localValidityDoesNotAutoPromoteToGlobalRoutability
