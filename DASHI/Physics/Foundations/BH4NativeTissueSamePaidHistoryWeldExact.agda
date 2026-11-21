module DASHI.Physics.Foundations.BH4NativeTissueSamePaidHistoryWeldExact where

-- 2026-11-21: PHYSICAL-SOURCE/GEOMETRY WELD-FORWARD.
--
-- Existing SourcePhysicalTissueSimulation already proves ALL native 54-bond
-- spatial future histories if a physicalOneStep witness is supplied.
-- Existing BH4PNPSameSourcePaidEnergyExact already proves BOTH actual BH4
-- and PNP history plus a source-paid ordered energy inequality.
--
-- Compose those two existing strong consumers on ONE AND THE SAME STATE,
-- same selected PNP receipt and source owner, not independent carriers.
-- This module does not fill in source-paid 29x12 BH4 kinetics, membrane
-- currents, cell type, observation or actual empirical energy values.
-- The ONLY physically new input is the same-original readout/one-step
-- observational simulation plus the explicitly selected intervention map.
-- Five distinct tissue interventions CANNOT be assumed injectable into
-- Bool; any encoding requires a source-calibrated action meaning.

open import DASHI.Core.Prelude

import DASHI.Biology.BH4PNPSamePhysicalHistoryBridgeExact as BH4
import DASHI.Biology.BH4PNPSameSourcePaidEnergyExact as Paid
import DASHI.Biology.BH4PNPOrderedEnergyHistoryExact as E
import DASHI.Biology.Physical.BiologicalHistoryFutureQuotientExact as Bio
import DASHI.Biology.Physical.BiologicalAllNeighbourTissueDynamicsExact as Tissue
import DASHI.Biology.Physical.BiologicalCoupledTissueCubeExact as Agreement
import DASHI.Biology.Physical.BiologicalSourcePhysicalTissueSimulationExact as Physical
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Biology.Physical.BiologicalFullCubeIncidenceExact as Grid

------------------------------------------------------------------------
-- W2/W7 selected original source. PhysicalState, the PNP receipt,
-- chemical readout and energy are sourced by M, not copied or refitted.
------------------------------------------------------------------------

record BH4NativeTissueReadoutWeld
  (M : Paid.SameSourcePaidEnergyModel) : Set₁ where
  field
    originalActionToBH4 : Bio.Intervention → Bool
    originalTissueReadout :
      BH4.PhysicalState (Paid.source M) → Bio.TissueField

    physicalTissueOneStep :
      (action : Bio.Intervention)
      (x : BH4.PhysicalState (Paid.source M))
      (voxel : Cube.Ternary27Point) →
      originalTissueReadout
        (BH4.physicalStep (Paid.source M) (originalActionToBH4 action) x)
        voxel
      ≡ Tissue.fullFineStep action (originalTissueReadout x) voxel

open BH4NativeTissueReadoutWeld

-- This is an actual record INSTANCE of the EXISTING physical tissue
-- consumer, not a second physical state or extra energy source.
toExistingTissuePhysicalSimulation :
  (M : Paid.SameSourcePaidEnergyModel) →
  BH4NativeTissueReadoutWeld M →
  Physical.SourcePhysicalTissueSimulation
toExistingTissuePhysicalSimulation M W = record
  { PhysicalState = BH4.PhysicalState (Paid.source M)
  ; selectedPNP = BH4.selectedPNP (Paid.source M)
  ; assaySource = BH4.selectedPhysicalSource (Paid.source M)
  ; specimenIdentity = BH4.selectedSpecimen (Paid.source M)
  ; observationProtocol = BH4.selectedMeasurementTime (Paid.source M)
  ; physicalStep =
      λ action x →
        BH4.physicalStep (Paid.source M)
          (originalActionToBH4 W action) x
  ; pnState = BH4.pnState (Paid.source M)
  ; pnStep =
      λ action pn →
        BH4.pnStep (Paid.source M)
          (originalActionToBH4 W action) pn
  ; physicalPNPStepCommutes =
      λ action x →
        BH4.pnStepCommutes (Paid.source M)
          (originalActionToBH4 W action) x
  ; tissueReadout = originalTissueReadout W
  ; physicalOneStep = physicalTissueOneStep W
  }

-- A real control history is translated once, explicitly; no assumed
-- identification of two different intervention alphabets.
toBH4History :
  ∀ {M : Paid.SameSourcePaidEnergyModel} →
  BH4NativeTissueReadoutWeld M →
  List Bio.Intervention → List Bool
toBH4History W [] = []
toBH4History W (action ∷ rest) =
  originalActionToBH4 W action ∷ toBH4History W rest

-- Both consumers advance precisely the SAME original BH4 physical state.
-- This theorem is true by induction on the actual selected action list;
-- the source still must pay what each action means in the original specimen.
theTwoPhysicalRunsAreTheSame :
  (M : Paid.SameSourcePaidEnergyModel)
  (W : BH4NativeTissueReadoutWeld M)
  (actions : List Bio.Intervention)
  (x : BH4.PhysicalState (Paid.source M)) →
  Physical.physicalTrace (toExistingTissuePhysicalSimulation M W) actions x
    ≡ BH4.physicalRun (Paid.source M) (toBH4History W actions) x
theTwoPhysicalRunsAreTheSame M W [] x = refl
theTwoPhysicalRunsAreTheSame M W (action ∷ rest) x =
  theTwoPhysicalRunsAreTheSame M W rest
    (BH4.physicalStep (Paid.source M)
      (originalActionToBH4 W action) x)

-- W2: chemistry + PNP + tissue on the ORIGINAL ONE STATE/HISTORY.
-- This is a constructive transport of the existing conditional theorem.
bh4PNPTissueAndNative54BondsSameHistory :
  (M : Paid.SameSourcePaidEnergyModel)
  (W : BH4NativeTissueReadoutWeld M)
  (actions : List Bio.Intervention)
  (x : BH4.PhysicalState (Paid.source M)) →
  Agreement.FieldsAgree
    (originalTissueReadout W
      (BH4.physicalRun (Paid.source M) (toBH4History W actions) x))
    (Tissue.fullCoarseRun actions
      (Bio.spatialProject (originalTissueReadout W x)))
bh4PNPTissueAndNative54BondsSameHistory M W actions x =
  subst
    (λ state →
      Agreement.FieldsAgree
        (originalTissueReadout W state)
        (Tissue.fullCoarseRun actions
          (Bio.spatialProject (originalTissueReadout W x))))
    (theTwoPhysicalRunsAreTheSame M W actions x)
    (Physical.physicalHistoryProjectsToAll54Bonds
      (toExistingTissuePhysicalSimulation M W) actions x)

-- Reuse (not recreate) the BH4 / PNP / one-state ordered-energy proof.
-- The ONLY difference is converting the selected tissue control history
-- into the existing source's explicit list of Bool interventions.
bh4PNPAndSignedEnergySameSelectedTissueHistory :
  (M : Paid.SameSourcePaidEnergyModel)
  (W : BH4NativeTissueReadoutWeld M)
  (actions : List Bio.Intervention)
  (x : BH4.PhysicalState (Paid.source M)) →
  (BH4.bh4Quantitative (Paid.source M)
     (BH4.physicalRun (Paid.source M) (toBH4History W actions) x)
   ≡ BH4.bh4Run (Paid.source M) (toBH4History W actions)
       (BH4.bh4Quantitative (Paid.source M) x))
  ×
  ((BH4.pnState (Paid.source M)
     (BH4.physicalRun (Paid.source M) (toBH4History W actions) x)
   ≡ BH4.pnRun (Paid.source M) (toBH4History W actions)
       (BH4.pnState (Paid.source M) x))
  ×
   E.OrderedEnergyCarrier._⊑_ (Paid.orderedEnergy M)
     (Paid.energyOf M
       (BH4.physicalRun (Paid.source M) (toBH4History W actions) x))
     (Paid.energyOf M x))
bh4PNPAndSignedEnergySameSelectedTissueHistory M W actions x =
  Paid.allSameSourceBH4PNPWithPaidEnergy
    M (toBH4History W actions) x

-- Strongest existing one-source composition: BH4 reaction/transport
-- observers, native 54-bond organization and signed energy ALL share
-- the SAME selected original history. Neither the 29x12 source nor
-- physicalTissueOneStep is automatically inhabited by this theorem.
allOriginalBH4PNPTissueGeometryAndPaidEnergy :
  (M : Paid.SameSourcePaidEnergyModel)
  (W : BH4NativeTissueReadoutWeld M)
  (actions : List Bio.Intervention)
  (x : BH4.PhysicalState (Paid.source M)) →
  Agreement.FieldsAgree
    (originalTissueReadout W
      (BH4.physicalRun (Paid.source M) (toBH4History W actions) x))
    (Tissue.fullCoarseRun actions
      (Bio.spatialProject (originalTissueReadout W x)))
  ×
  ((BH4.bh4Quantitative (Paid.source M)
     (BH4.physicalRun (Paid.source M) (toBH4History W actions) x)
   ≡ BH4.bh4Run (Paid.source M) (toBH4History W actions)
       (BH4.bh4Quantitative (Paid.source M) x))
  ×
  ((BH4.pnState (Paid.source M)
     (BH4.physicalRun (Paid.source M) (toBH4History W actions) x)
   ≡ BH4.pnRun (Paid.source M) (toBH4History W actions)
       (BH4.pnState (Paid.source M) x))
  ×
   E.OrderedEnergyCarrier._⊑_ (Paid.orderedEnergy M)
     (Paid.energyOf M
       (BH4.physicalRun (Paid.source M) (toBH4History W actions) x))
     (Paid.energyOf M x)))
allOriginalBH4PNPTissueGeometryAndPaidEnergy M W actions x =
  bh4PNPTissueAndNative54BondsSameHistory M W actions x ,
  bh4PNPAndSignedEnergySameSelectedTissueHistory M W actions x

-- Original native bond endpoint observation after the ONE PAID history,
-- rather than a nominal 54 element chart.
everyOriginalBondReadoutAtSameBH4History :
  (M : Paid.SameSourcePaidEnergyModel)
  (W : BH4NativeTissueReadoutWeld M)
  (actions : List Bio.Intervention)
  (x : BH4.PhysicalState (Paid.source M))
  (bond : Grid.PositiveBond) →
  Grid.fineJunctionPair
    (originalTissueReadout W
      (BH4.physicalRun (Paid.source M) (toBH4History W actions) x)) bond
  ≡ Grid.coarseJunctionPair
    (Tissue.fullCoarseRun actions
      (Bio.spatialProject (originalTissueReadout W x))) bond
everyOriginalBondReadoutAtSameBH4History M W actions x bond =
  Grid.allBondJunctionReadingsSurviveProjection
    (originalTissueReadout W
      (BH4.physicalRun (Paid.source M) (toBH4History W actions) x)) bond
  -- NB: projection at initial state must be replaced with the
  -- selected fine-to-coarse history's agreement in the next weld.
