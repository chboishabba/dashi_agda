module DASHI.Biology.Physical.BiologicalSourcePhysicalTissueSimulationExact where

-- The physical-to-observer theorem needed to connect selected chemistry,
-- ionic transport and the existing nonperiodic 54-bond morphology model.
-- A physical source must PROVIDE the one-step simulation; this theorem
-- transports it to ALL intervention histories without extensionality.

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.Physical.BiologicalHistoryFutureQuotientExact as Bio
import DASHI.Biology.Physical.BiologicalAllNeighbourTissueDynamicsExact as Tissue
import DASHI.Biology.Physical.BiologicalCoupledTissueCubeExact as Agreement
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Physics.Electromagnetism.PoissonNernstPlanckElectrodiffusionExact as PNP

record SourcePhysicalTissueSimulation : Set₁ where
  field
    PhysicalState : Set
    selectedPNP : PNP.ElectrodiffusionApplicationReceipt
    assaySource : String
    specimenIdentity : String
    observationProtocol : String
    physicalStep : Bio.Intervention → PhysicalState → PhysicalState
    pnState : PhysicalState →
      PNP.CoupledState (PNP.fluxLaw selectedPNP)
    pnStep : Bio.Intervention →
      PNP.CoupledState (PNP.fluxLaw selectedPNP) →
      PNP.CoupledState (PNP.fluxLaw selectedPNP)
    -- Forces the selected micro-state and the selected PNP reaction /
    -- ionic transport carrier to follow the SAME step and timeline.
    physicalPNPStepCommutes :
      (action : Bio.Intervention) (state : PhysicalState) →
      pnState (physicalStep action state)
        ≡ pnStep action (pnState state)
    tissueReadout : PhysicalState → Bio.TissueField
    -- This is the crucial NOT-YET-PAID PHYSICAL source obligation.
    physicalOneStep :
      (action : Bio.Intervention)
      (state : PhysicalState)
      (p : Cube.Ternary27Point) →
      tissueReadout (physicalStep action state) p
        ≡ Tissue.fullFineStep action (tissueReadout state) p

open SourcePhysicalTissueSimulation public

physicalTrace :
  (model : SourcePhysicalTissueSimulation) →
  List Bio.Intervention → PhysicalState model → PhysicalState model
physicalTrace model [] state = state
physicalTrace model (action ∷ rest) state =
  physicalTrace model rest (physicalStep model action state)

physicalOneStepCoarse :
  (model : SourcePhysicalTissueSimulation)
  (action : Bio.Intervention)
  (state : PhysicalState model)
  (p : Cube.Ternary27Point) →
  Bio.project (tissueReadout model (physicalStep model action state) p)
    ≡ Tissue.fullCoarseStep action
        (Bio.spatialProject (tissueReadout model state)) p
physicalOneStepCoarse model action state p =
  trans
    (cong Bio.project (physicalOneStep model action state p))
    (Agreement.atEveryVoxel
      (Tissue.fullAgreementPreserved action
        (tissueReadout model state)
        (Bio.spatialProject (tissueReadout model state))
        (Agreement.initialFieldAgreement (tissueReadout model state))) p)

-- Generalized induction with arbitrary starting coarse field.
physicalAllControlledHistories :
  (model : SourcePhysicalTissueSimulation)
  (actions : List Bio.Intervention)
  (state : PhysicalState model)
  (coarse : Bio.CoarseTissueField) →
  Agreement.FieldsAgree (tissueReadout model state) coarse →
  Agreement.FieldsAgree
    (tissueReadout model (physicalTrace model actions state))
    (Tissue.fullCoarseRun actions coarse)
physicalAllControlledHistories model [] state coarse initial = initial
physicalAllControlledHistories model (action ∷ rest) state coarse initial =
  physicalAllControlledHistories model rest
    (physicalStep model action state)
    (Tissue.fullCoarseStep action coarse)
    (Agreement.fieldsAgree λ p →
      trans
        (cong Bio.project (physicalOneStep model action state p))
        (Agreement.atEveryVoxel
          (Tissue.fullAgreementPreserved action
            (tissueReadout model state) coarse initial) p))

-- No choice, function extensionality, or hidden measured-law axiom.
physicalHistoryProjectsToAll54Bonds :
  (model : SourcePhysicalTissueSimulation)
  (actions : List Bio.Intervention)
  (state : PhysicalState model) →
  Agreement.FieldsAgree
    (tissueReadout model (physicalTrace model actions state))
    (Tissue.fullCoarseRun actions
      (Bio.spatialProject (tissueReadout model state)))
physicalHistoryProjectsToAll54Bonds model actions state =
  physicalAllControlledHistories model actions state
    (Bio.spatialProject (tissueReadout model state))
    (Agreement.initialFieldAgreement (tissueReadout model state))

------------------------------------------------------------------------
-- Exact same-object PNP transport through arbitrary controlled histories,
-- rather than a PNP receipt merely sitting beside a tissue model.
------------------------------------------------------------------------

pnTrace :
  (model : SourcePhysicalTissueSimulation) →
  List Bio.Intervention →
  PNP.CoupledState (PNP.fluxLaw (selectedPNP model)) →
  PNP.CoupledState (PNP.fluxLaw (selectedPNP model))
pnTrace model [] state = state
pnTrace model (action ∷ rest) state =
  pnTrace model rest (pnStep model action state)

physicalAndPNPRemainTheSameStateHistory :
  (model : SourcePhysicalTissueSimulation)
  (actions : List Bio.Intervention)
  (state : PhysicalState model) →
  pnState model (physicalTrace model actions state)
    ≡ pnTrace model actions (pnState model state)
physicalAndPNPRemainTheSameStateHistory model [] state = refl
physicalAndPNPRemainTheSameStateHistory model (action ∷ rest) state =
  trans
    (physicalAndPNPRemainTheSameStateHistory model rest
      (physicalStep model action state))
    (cong (pnTrace model rest)
      (physicalPNPStepCommutes model action state))

------------------------------------------------------------------------
-- Highest-alpha same-source consumer: the physical trajectory carries
-- BOTH the original PNP electrodiffusion history and the original 54-bond
-- coarse tissue history. These are NOT separate witness histories.
--
-- This consumes the existing selected physicalOneStep and
-- physicalPNPStepCommutes fields. They remain unpaid original physical
-- source obligations; this composition does not inhabit either field.
------------------------------------------------------------------------

physicalPNPAndTissueSameHistory :
  (model : SourcePhysicalTissueSimulation)
  (actions : List Bio.Intervention)
  (state : PhysicalState model) →
  (pnState model (physicalTrace model actions state)
    ≡ pnTrace model actions (pnState model state))
  ×
  Agreement.FieldsAgree
    (tissueReadout model (physicalTrace model actions state))
    (Tissue.fullCoarseRun actions
      (Bio.spatialProject (tissueReadout model state)))
physicalPNPAndTissueSameHistory model actions state =
  physicalAndPNPRemainTheSameStateHistory model actions state
  , physicalHistoryProjectsToAll54Bonds model actions state

-- A native-voxel specialization avoids treating a Vec 27 storage chart
-- as the semantic geometry. All original 3×3×3 positions are quantified.
physicalPNPAndTissueAtOriginalVoxel :
  (model : SourcePhysicalTissueSimulation)
  (actions : List Bio.Intervention)
  (state : PhysicalState model)
  (voxel : Cube.Ternary27Point) →
  (pnState model (physicalTrace model actions state)
    ≡ pnTrace model actions (pnState model state))
  ×
  (Bio.project
    (tissueReadout model (physicalTrace model actions state) voxel)
    ≡
    Tissue.fullCoarseRun actions
      (Bio.spatialProject (tissueReadout model state)) voxel)
physicalPNPAndTissueAtOriginalVoxel model actions state voxel =
  physicalAndPNPRemainTheSameStateHistory model actions state
  , Agreement.atEveryVoxel
      (physicalHistoryProjectsToAll54Bonds model actions state) voxel
