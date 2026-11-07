module DASHI.Biology.BH4PNPSamePhysicalHistoryBridgeExact where

-- Genuine same-physical-carrier BH4 chemical / PNP electrodiffusion
-- projection. Source-specific transitions and their compatibility
-- must be supplied; no Kitzerow clinical hypothesis is presumed.
-- This lives on the BH4 stacked branch, independently of the
-- unmerged 54-bond developmental future-quotient branch.

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.BH4SystemStateExact as BH4
import DASHI.Biology.BH4SpatialConnectivityCirculationExact as Spatial
import DASHI.Biology.BH4CompartmentKineticStateExact as Kinetics
import DASHI.Biology.BH4OpenMetabolicNetworkAdapterExact as Metabolic
import DASHI.Physics.Electromagnetism.PoissonNernstPlanckElectrodiffusionExact as PNP

record SameSourceBH4PNPModel : Set₁ where
  field
    PhysicalState : Set
    selectedPhysicalSource : String
    selectedSpecimen : String
    selectedCompartment : BH4.Compartment
    selectedMeasurementTime : String
    selectedPNP : PNP.ElectrodiffusionApplicationReceipt
    selectedMetabolicNetwork : Metabolic.BH4OpenMetabolicNetworkAdapter
    circulation : Spatial.ContextIndexedCirculation
    sameElectrodiffusiveLaw :
      Spatial.selectedPNP circulation ≡ selectedPNP
    locationOf : PhysicalState → Spatial.Location circulation
    localCompartment : PhysicalState → BH4.Compartment
    originalCompartmentAgreement :
      (x : PhysicalState) →
      localCompartment x
        ≡ Spatial.compartmentAt circulation (locationOf x)
    -- Physical transport from x to its successor must be reachable
    -- by original-source permitted directed connections; a location
    -- string or a nonzero global pool does not pay the route.
    bh4Quantitative : PhysicalState → Kinetics.BH4QuantitativeState
    pnState : PhysicalState →
      PNP.CoupledState (PNP.fluxLaw selectedPNP)
    physicalStep : Bool → PhysicalState → PhysicalState
    permittedStepRoute :
      (action : Bool) (state : PhysicalState) →
      Spatial.FlowPath (Spatial.PermittedFlow circulation)
        (locationOf state) (locationOf (physicalStep action state))
    bh4Step : Bool → Kinetics.BH4QuantitativeState →
      Kinetics.BH4QuantitativeState
    pnStep : Bool →
      PNP.CoupledState (PNP.fluxLaw selectedPNP) →
      PNP.CoupledState (PNP.fluxLaw selectedPNP)
    bh4StepCommutes :
      (action : Bool) (x : PhysicalState) →
      bh4Quantitative (physicalStep action x)
        ≡ bh4Step action (bh4Quantitative x)
    pnStepCommutes :
      (action : Bool) (x : PhysicalState) →
      pnState (physicalStep action x)
        ≡ pnStep action (pnState x)
    -- Source agreement that the quantitative state refers to the
    -- original BH4 system, not an unrelated identifier or compartment.
    bh4SystemAt : PhysicalState → BH4.BH4SystemState
    sameBH4State :
      (x : PhysicalState) →
      Kinetics.systemState (bh4Quantitative x) ≡ bh4SystemAt x

open SameSourceBH4PNPModel public

physicalRun :
  (model : SameSourceBH4PNPModel) →
  List Bool → PhysicalState model → PhysicalState model
physicalRun model [] x = x
physicalRun model (action ∷ rest) x =
  physicalRun model rest (physicalStep model action x)

bh4Run :
  (model : SameSourceBH4PNPModel) →
  List Bool → Kinetics.BH4QuantitativeState →
  Kinetics.BH4QuantitativeState
bh4Run model [] x = x
bh4Run model (action ∷ rest) x =
  bh4Run model rest (bh4Step model action x)

pnRun :
  (model : SameSourceBH4PNPModel) →
  List Bool →
  PNP.CoupledState (PNP.fluxLaw (selectedPNP model)) →
  PNP.CoupledState (PNP.fluxLaw (selectedPNP model))
pnRun model [] x = x
pnRun model (action ∷ rest) x =
  pnRun model rest (pnStep model action x)

allBH4ControlledHistoriesSamePhysicalSource :
  (model : SameSourceBH4PNPModel)
  (actions : List Bool)
  (x : PhysicalState model) →
  bh4Quantitative model (physicalRun model actions x)
    ≡ bh4Run model actions (bh4Quantitative model x)
allBH4ControlledHistoriesSamePhysicalSource model [] x = refl
allBH4ControlledHistoriesSamePhysicalSource model (action ∷ rest) x =
  trans
    (allBH4ControlledHistoriesSamePhysicalSource model rest
      (physicalStep model action x))
    (cong (bh4Run model rest)
      (bh4StepCommutes model action x))

allPNPControlledHistoriesSamePhysicalSource :
  (model : SameSourceBH4PNPModel)
  (actions : List Bool)
  (x : PhysicalState model) →
  pnState model (physicalRun model actions x)
    ≡ pnRun model actions (pnState model x)
allPNPControlledHistoriesSamePhysicalSource model [] x = refl
allPNPControlledHistoriesSamePhysicalSource model (action ∷ rest) x =
  trans
    (allPNPControlledHistoriesSamePhysicalSource model rest
      (physicalStep model action x))
    (cong (pnRun model rest)
      (pnStepCommutes model action x))

allHistoriesRemainOnOriginalBH4System :
  (model : SameSourceBH4PNPModel)
  (actions : List Bool)
  (x : PhysicalState model) →
  Kinetics.systemState
    (bh4Quantitative model (physicalRun model actions x))
    ≡ bh4SystemAt model (physicalRun model actions x)
allHistoriesRemainOnOriginalBH4System model actions x =
  sameBH4State model (physicalRun model actions x)

------------------------------------------------------------------------
-- Source-selected reachability of the entire physical trajectory.
-- No inverse circulation is inferred from the allowed forward paths.
------------------------------------------------------------------------

concatenatePermittedRoutes :
  ∀ {Location : Set} {Flow : Location → Location → Set}
    {a b c : Location} →
  Spatial.FlowPath Flow a b →
  Spatial.FlowPath Flow b c →
  Spatial.FlowPath Flow a c
concatenatePermittedRoutes (Spatial.here x) second = second
concatenatePermittedRoutes (Spatial.thenFlow first remaining) second =
  Spatial.thenFlow first (concatenatePermittedRoutes remaining second)

physicalTrajectoryHasSourcePermittedRoute :
  (model : SameSourceBH4PNPModel)
  (actions : List Bool)
  (x : PhysicalState model) →
  Spatial.FlowPath (Spatial.PermittedFlow (circulation model))
    (locationOf model x)
    (locationOf model (physicalRun model actions x))
physicalTrajectoryHasSourcePermittedRoute model [] x =
  Spatial.here (locationOf model x)
physicalTrajectoryHasSourcePermittedRoute model (action ∷ rest) x =
  concatenatePermittedRoutes
    (permittedStepRoute model action x)
    (physicalTrajectoryHasSourcePermittedRoute model rest
      (physicalStep model action x))
