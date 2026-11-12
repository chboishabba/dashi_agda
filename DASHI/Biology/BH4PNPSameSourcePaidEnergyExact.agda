module DASHI.Biology.BH4PNPSameSourcePaidEnergyExact where

-- Same-object P0.06 -> P1 conditional bridge.
-- Unlike a disconnected abstract energy history, every receipt uses
-- the identical physical transition already selected for both the
-- BH4 chemical and PNP electrodiffusion observers.
-- No original physical-rate/detailed-balance inhabitant is asserted.
--
-- Original 369 geometry, BH4/PNP physical carriers and observational
-- interfaces remain the repository's prior work. This is glue only.

open import DASHI.Core.Prelude

import DASHI.Biology.BH4PNPSamePhysicalHistoryBridgeExact as Same
import DASHI.Biology.BH4PNPOrderedEnergyHistoryExact as Ledger
import DASHI.Energy.Core as EC
import DASHI.Biology.BH4SpatialConnectivityCirculationExact as Spatial

record SameSourcePaidEnergyModel : Set₂ where
  field
    source : Same.SameSourceBH4PNPModel
    orderedEnergy : Ledger.OrderedEnergyCarrier

  open Ledger.OrderedEnergyCarrier orderedEnergy
    using (Energy; _⊑_; orderReflexive; orderTransitive)

  field
    energyOf : Same.PhysicalState source → Energy

    -- Physically meaningful one-step receipts must be supplied from
    -- original PNP/SG/reaction/free-energy data, not fabricated here.
    exactPhysicalEnergyStep :
      (action : Bool) (x : Same.PhysicalState source) →
      Ledger.EnergyLaws.EnergyStep orderedEnergy
        (energyOf x)
        (energyOf (Same.physicalStep source action x))

    -- Nonzero residual and exterior work are allowed, but must be
    -- paid by the certified loss for that SAME physical step.
    physicalResidualAndExteriorWorkPaid :
      (action : Bool) (x : Same.PhysicalState source) →
      Ledger.EnergyLaws.EnergyStep.credit
        (exactPhysicalEnergyStep action x)
      ⊑ Ledger.EnergyLaws.EnergyStep.loss
        (exactPhysicalEnergyStep action x)

open SameSourcePaidEnergyModel public

onePhysicalStepPaidEnergy :
  (M : SameSourcePaidEnergyModel)
  (action : Bool)
  (x : Same.PhysicalState (source M)) →
  Ledger.OrderedEnergyCarrier._⊑_ (orderedEnergy M)
    (energyOf M (Same.physicalStep (source M) action x))
    (energyOf M x)
onePhysicalStepPaidEnergy M action x =
  Ledger.EnergyLaws.creditPaidByLoss (orderedEnergy M)
    (exactPhysicalEnergyStep M action x)
    (physicalResidualAndExteriorWorkPaid M action x)

allSameSourceControlledHistoriesEnergyNonincreasing :
  (M : SameSourcePaidEnergyModel)
  (actions : List Bool)
  (x : Same.PhysicalState (source M)) →
  Ledger.OrderedEnergyCarrier._⊑_ (orderedEnergy M)
    (energyOf M (Same.physicalRun (source M) actions x))
    (energyOf M x)
allSameSourceControlledHistoriesEnergyNonincreasing M [] x =
  Ledger.OrderedEnergyCarrier.orderReflexive
    (orderedEnergy M) (energyOf M x)
allSameSourceControlledHistoriesEnergyNonincreasing
  M (action ∷ rest) x =
  Ledger.OrderedEnergyCarrier.orderTransitive (orderedEnergy M)
    (allSameSourceControlledHistoriesEnergyNonincreasing M rest
      (Same.physicalStep (source M) action x))
    (onePhysicalStepPaidEnergy M action x)

-- A single physical history carries both original observer
-- commuting squares and a paid-energy inequality, not three
-- independently constructed trajectories.
allSameSourceBH4PNPWithPaidEnergy :
  (M : SameSourcePaidEnergyModel)
  (actions : List Bool)
  (x : Same.PhysicalState (source M)) →
  (Same.bh4Quantitative (source M)
     (Same.physicalRun (source M) actions x)
   ≡ Same.bh4Run (source M) actions
       (Same.bh4Quantitative (source M) x))
  ×
  ((Same.pnState (source M)
      (Same.physicalRun (source M) actions x)
    ≡ Same.pnRun (source M) actions
        (Same.pnState (source M) x))
  ×
   Ledger.OrderedEnergyCarrier._⊑_ (orderedEnergy M)
     (energyOf M (Same.physicalRun (source M) actions x))
     (energyOf M x))
allSameSourceBH4PNPWithPaidEnergy M actions x =
  Same.allBH4ControlledHistoriesSamePhysicalSource
    (source M) actions x
  , (Same.allPNPControlledHistoriesSamePhysicalSource
       (source M) actions x
  , allSameSourceControlledHistoriesEnergyNonincreasing
      M actions x)

------------------------------------------------------------------------
-- Reuse the existing Energy.Core preorder and state-energy interface.
-- No second independent physical observation or energy state is built.
------------------------------------------------------------------------

toExistingEnergyPreorder :
  (O : Ledger.OrderedEnergyCarrier) →
  EC.Preorder (Ledger.OrderedEnergyCarrier.Energy O)
toExistingEnergyPreorder O =
  record
    { _≤_ = Ledger.OrderedEnergyCarrier._⊑_ O
    ; refl = Ledger.OrderedEnergyCarrier.orderReflexive O
    ; trans = Ledger.OrderedEnergyCarrier.orderTransitive O
    }

sameSourceEnergySpace :
  (M : SameSourcePaidEnergyModel) →
  EC.EnergySpace
    (Same.PhysicalState (source M))
    (Ledger.OrderedEnergyCarrier.Energy (orderedEnergy M))
sameSourceEnergySpace M =
  record
    { P = toExistingEnergyPreorder (orderedEnergy M)
    ; energy = energyOf M
    }

allSameSourceHistoriesDescendInExistingEnergySpace :
  (M : SameSourcePaidEnergyModel)
  (actions : List Bool)
  (x : Same.PhysicalState (source M)) →
  EC.Preorder._≤_
    (EC.EnergySpace.P (sameSourceEnergySpace M))
    (EC.EnergySpace.energy (sameSourceEnergySpace M)
      (Same.physicalRun (source M) actions x))
    (EC.EnergySpace.energy (sameSourceEnergySpace M) x)
allSameSourceHistoriesDescendInExistingEnergySpace M actions x =
  allSameSourceControlledHistoriesEnergyNonincreasing M actions x


------------------------------------------------------------------------
-- Four-way same-original-history weld: chemistry, PNP, permitted
-- circulation route, and paid energy all use the one physicalRun.
-- The route is the pre-existing source-permitted forward FlowPath;
-- no reverse path, permeability or empirical circulation is inferred.
------------------------------------------------------------------------

allSameSourceBH4PNPRouteAndPaidEnergy :
  (M : SameSourcePaidEnergyModel)
  (actions : List Bool)
  (x : Same.PhysicalState (source M)) →
  (Same.bh4Quantitative (source M)
     (Same.physicalRun (source M) actions x)
   ≡ Same.bh4Run (source M) actions
       (Same.bh4Quantitative (source M) x))
  ×
  ((Same.pnState (source M)
      (Same.physicalRun (source M) actions x)
    ≡ Same.pnRun (source M) actions
        (Same.pnState (source M) x))
  ×
  ((Spatial.FlowPath
      (Spatial.PermittedFlow
        (Same.circulation (source M)))
      (Same.locationOf (source M) x)
      (Same.locationOf (source M)
        (Same.physicalRun (source M) actions x)))
  ×
   Ledger.OrderedEnergyCarrier._⊑_ (orderedEnergy M)
     (energyOf M (Same.physicalRun (source M) actions x))
     (energyOf M x)))
allSameSourceBH4PNPRouteAndPaidEnergy M actions x =
  Same.allBH4ControlledHistoriesSamePhysicalSource
    (source M) actions x
  , (Same.allPNPControlledHistoriesSamePhysicalSource
       (source M) actions x
  , (Same.physicalTrajectoryHasSourcePermittedRoute
       (source M) actions x
  , allSameSourceControlledHistoriesEnergyNonincreasing
      M actions x))
