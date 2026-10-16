module DASHI.Governance.OccupyRealizedControlAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.OccupyConsensusEvidenceAtlasExact as Consensus
import DASHI.Governance.OccupyPseudonymousNetworkFeaturesExact as Network
import DASHI.Governance.BoloBoloOWSSpokesPrimaryLocatorAtlasExact as Spokes
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID

------------------------------------------------------------------------
-- OCCUPY / SPOKES REALISED-CONTROL ACQUISITION SURFACE
--
-- The acquisition question is not whether actors used horizontal/leaderless
-- language.  It is whether recoverable primary records can show how sensing,
-- framing, facilitation, delegation, blocking/advancement, reportback,
-- correction and reopening actually circulated through the process.
------------------------------------------------------------------------

data ControlCoordinateKind : Set where
  issueSurfacing : ControlCoordinateKind
  agendaFraming : ControlCoordinateKind
  facilitationRole : ControlCoordinateKind
  roleRotation : ControlCoordinateKind
  delegatedAuthority : ControlCoordinateKind
  blockOrAdvance : ControlCoordinateKind
  reportbackPath : ControlCoordinateKind
  repeatedInfluence : ControlCoordinateKind
  correctionHandling : ControlCoordinateKind
  reopeningOrAppeal : ControlCoordinateKind

record RealizedControlCoordinate : Set where
  constructor realized-control-coordinate
  field
    kind : ControlCoordinateKind
    sourceReference : String
    meetingReference : String
    pseudonymousActorReference : String
    observationReference : String
    codingRuleReference : String
    missingnessReference : String

open RealizedControlCoordinate public

canonicalControlCoordinateKinds : List ControlCoordinateKind
canonicalControlCoordinateKinds =
  issueSurfacing
  ∷ agendaFraming
  ∷ facilitationRole
  ∷ roleRotation
  ∷ delegatedAuthority
  ∷ blockOrAdvance
  ∷ reportbackPath
  ∷ repeatedInfluence
  ∷ correctionHandling
  ∷ reopeningOrAppeal
  ∷ []

------------------------------------------------------------------------
-- Existing evidence/source anchors.
------------------------------------------------------------------------

consensusEvidenceAnchor : Consensus.OccupyConsensusEvidenceBoundary
consensusEvidenceAnchor = Consensus.canonicalOccupyConsensusEvidenceBoundary

networkEvidenceAnchor : Network.NetworkFeatureBoundary
networkEvidenceAnchor = Network.canonicalNetworkFeatureBoundary

spokesLocatorBoundaryAnchor : Spokes.SpokesPrimaryLocatorBoundary
spokesLocatorBoundaryAnchor = Spokes.canonicalSpokesPrimaryLocatorBoundary

posiwidBoundaryAnchor : POSIWID.OperationalDescriptionBoundary
posiwidBoundaryAnchor = POSIWID.canonicalOperationalDescriptionBoundary

------------------------------------------------------------------------
-- Acquisition boundary.
------------------------------------------------------------------------

record RealizedControlAcquisitionBoundary : Set where
  constructor realized-control-acquisition-boundary
  field
    issueSurfacingObserved : Bool
    agendaFramingObserved : Bool
    facilitationObserved : Bool
    roleRotationObserved : Bool
    delegationObserved : Bool
    blockAdvanceObserved : Bool
    reportbackObserved : Bool
    repeatedInfluenceObserved : Bool
    correctionHandlingObserved : Bool
    reopeningAppealObserved : Bool

    horizontalLabelProvesHorizontalRealizedControl : Bool
    roleRotationProvesEqualInfluence : Bool
    pseudonymRecurrenceProvesRealWorldIdentity : Bool
    repeatedInfluenceProvesDomination : Bool
    realizedInfluenceProvesLegitimacy : Bool
    realizedInfluenceProvesIllegitimacy : Bool
    primaryLocatorPaysMinuteContent : Bool
    secondaryEvidenceMayReplacePrimaryMinutes : Bool

open RealizedControlAcquisitionBoundary public

canonicalRealizedControlAcquisitionBoundary : RealizedControlAcquisitionBoundary
canonicalRealizedControlAcquisitionBoundary =
  realized-control-acquisition-boundary
    true true true true true true true true true true
    false false false false false false false false

canonicalOccupyRealizedControlAcquisitionReceipt : GenericReceipt.GenericReceipt
canonicalOccupyRealizedControlAcquisitionReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "Occupy / Spokes realised-control acquisition surface"
    "DASHI.Governance.OccupyRealizedControlAcquisitionExact"
    "canonicalRealizedControlAcquisitionBoundary"
    "defines a primary-record coding surface for issue surfacing, framing, facilitation, role rotation, delegation, block/advance events, reportback, repeated influence, correction handling and reopening/appeal while reusing existing pseudonymous network, consensus evidence and Spokes locator owners"
    "horizontal self-description does not prove horizontal realised control; repeated influence does not by itself prove domination, legitimacy or illegitimacy; pseudonym recurrence does not establish real-world identity; locator identity and secondary evidence do not pay primary minute content"
    "agda -i . DASHI/Governance/DeliberativeViableNonDominationLoopRegression.agda"
