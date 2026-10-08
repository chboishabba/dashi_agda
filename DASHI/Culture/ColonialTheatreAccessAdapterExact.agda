module DASHI.Culture.ColonialTheatreAccessAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.HistoryQualifiedSelectionTopologyExact as History

------------------------------------------------------------------------
-- COLONIAL THEATRE ACCESS ADAPTER
--
-- The generic HistoryQualifiedSelectionTopologyExact owner already establishes
-- that nominal node existence does not imply history-qualified accessibility.
-- This module instantiates that grammar for a theatre/access assay while
-- retaining the firewall against treating the finite witness as a historical
-- claim about any named venue or person.
------------------------------------------------------------------------

data TheatreParticipant : Set where
  restrictedParticipant : TheatreParticipant
  admittedParticipant : TheatreParticipant

data TheatreHistory : Set where
  restrictedHistory : TheatreHistory
  admittedHistory : TheatreHistory

data VenueNode : Set where
  theatreNode : VenueNode

data OpponentHistory : Set where
  noOpponentHistory : OpponentHistory

data TheatreOutcome : Set where
  observedPerformance : TheatreOutcome

data TheatreTopology : Set where
  sameTheatreTopology : TheatreTopology

data TheatreFrontier : Set where
  sameTheatreFrontier : TheatreFrontier

historyOfParticipant : TheatreParticipant → TheatreHistory
historyOfParticipant restrictedParticipant = restrictedHistory
historyOfParticipant admittedParticipant = admittedHistory

TheatreAccess : VenueNode → TheatreHistory → Set
TheatreAccess theatreNode restrictedHistory = ⊥
TheatreAccess theatreNode admittedHistory = ⊤

theatreInteraction : TheatreParticipant → OpponentHistory → TheatreOutcome
theatreInteraction _ _ = observedPerformance

theatreFrontier : TheatreTopology → TheatreFrontier
theatreFrontier _ = sameTheatreFrontier

historyQualifiedTheatreAccess : History.HistoryQualifiedSelectionSystem
historyQualifiedTheatreAccess =
  record
    { Participant = TheatreParticipant
    ; History = TheatreHistory
    ; Node = VenueNode
    ; OpponentHistory = OpponentHistory
    ; Outcome = TheatreOutcome
    ; Topology = TheatreTopology
    ; FrontierCode = TheatreFrontier
    ; historyOf = historyOfParticipant
    ; canAccess = TheatreAccess
    ; interact = theatreInteraction
    ; frontier = theatreFrontier
    ; reading = "synthetic colonial-theatre access adapter over history-qualified selection"
    }

admittedParticipantCanAccess :
  History.QualifiedEntry historyQualifiedTheatreAccess theatreNode admittedParticipant
admittedParticipantCanAccess = History.qualified-entry tt

restrictedParticipantCannotAccess :
  History.QualifiedEntry historyQualifiedTheatreAccess theatreNode restrictedParticipant → ⊥
restrictedParticipantCannotAccess (History.qualified-entry impossible) = impossible

------------------------------------------------------------------------
-- Same nominal production does not determine situated venue access.
------------------------------------------------------------------------

data TheatreAccessState : Set where
  sameProductionRestricted : TheatreAccessState
  sameProductionAdmitted : TheatreAccessState

data ProductionSurface : Set where
  sameProduction : ProductionSurface

data VenueAccessClass : Set where
  venueRestricted : VenueAccessClass
  venueAdmitted : VenueAccessClass

productionSurface : TheatreAccessState → ProductionSurface
productionSurface _ = sameProduction

venueAccessClass : TheatreAccessState → VenueAccessClass
venueAccessClass sameProductionRestricted = venueRestricted
venueAccessClass sameProductionAdmitted = venueAdmitted

venueAccessDiffers :
  venueAccessClass sameProductionRestricted
  ≡ venueAccessClass sameProductionAdmitted → ⊥
venueAccessDiffers ()

sameProductionCannotRecoverVenueAccess :
  INF.FactorsThrough productionSurface venueAccessClass → ⊥
sameProductionCannotRecoverVenueAccess =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameProductionRestricted
      sameProductionAdmitted
      refl
      venueAccessDiffers)

record ColonialTheatreAccessBoundary : Set where
  constructor colonial-theatre-access-boundary
  field
    sameProductionMeansSameAccess : Bool
    sameProductionMeansSameAccessIsFalse : sameProductionMeansSameAccess ≡ false
    theatreExistsMeansEveryoneCanEnter : Bool
    theatreExistsMeansEveryoneCanEnterIsFalse :
      theatreExistsMeansEveryoneCanEnter ≡ false
    finiteAccessStateIsNamedHistoricalVenueClaim : Bool
    finiteAccessStateIsNamedHistoricalVenueClaimIsFalse :
      finiteAccessStateIsNamedHistoricalVenueClaim ≡ false

canonicalColonialTheatreAccessBoundary : ColonialTheatreAccessBoundary
canonicalColonialTheatreAccessBoundary =
  colonial-theatre-access-boundary false refl false refl false refl
