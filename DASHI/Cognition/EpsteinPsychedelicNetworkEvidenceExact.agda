module DASHI.Cognition.EpsteinPsychedelicNetworkEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Governance.EvidenceGradedGenealogyCore as Genealogy
import DASHI.Cognition.EpsteinPsychedelicSourceAtlasExact as Sources

------------------------------------------------------------------------
-- CASE-SPECIFIC NETWORK EDGES OVER THE EXISTING GENEALOGY CALCULUS.
--
-- We reuse EvidenceGrade and PathwayRelation but keep the released-document
-- references as exact case-local identifiers.  No parallel evidence ladder is
-- introduced.
------------------------------------------------------------------------

data NetworkNode : Set where
  jeffreyEpstein : NetworkNode
  ginoYu : NetworkNode
  joschaBach : NetworkNode
  rickDoblin : NetworkNode
  maps : NetworkNode
  cubaConsciousnessEvent : NetworkNode
  psychedelicResearchMilieu : NetworkNode
  ibogaineResearch : NetworkNode
  scopolamineInformation : NetworkNode
  trumpetPlants : NetworkNode

record NetworkEdge : Set where
  constructor network-edge
  field
    source : NetworkNode
    target : NetworkNode
    relation : Genealogy.PathwayRelation
    grade : Genealogy.EvidenceGrade
    sourceDocuments : List Sources.SourceIdentity
    boundedClaim : String
open NetworkEdge public

yuToEpsteinCorrespondence : NetworkEdge
yuToEpsteinCorrespondence = network-edge
  ginoYu jeffreyEpstein
  Genealogy.personnelInstitutionalContinuity
  Genealogy.gradeA
  (Sources.yuExperientialProposal20161017 ∷ Sources.yuUpdateCuba20170216 ∷ Sources.yuNetworkReport20171113 ∷ [])
  "Direct correspondence documents an ongoing Yu-Epstein relationship around altered-state/consciousness research planning."

epsteinFundingCubaEvent : NetworkEdge
epsteinFundingCubaEvent = network-edge
  jeffreyEpstein cubaConsciousnessEvent
  Genealogy.fundingOrganisationalLink
  Genealogy.gradeA
  (Sources.yuUpdateCuba20170216 ∷ [])
  "Yu requested a USD 25,000 transfer for the Cuba event and Epstein replied affirmatively in the preserved thread; payment execution remains a separate receipt if needed."

yuToPsychedelicMilieu : NetworkEdge
yuToPsychedelicMilieu = network-edge
  ginoYu psychedelicResearchMilieu
  Genealogy.directDocumentedTransfer
  Genealogy.gradeA
  (Sources.yuExperientialProposal20161017 ∷ Sources.cubaConferenceAbstractPacket ∷ [])
  "Yu's event/conference materials explicitly include ayahuasca and ibogaine/iboga within the altered-state programme."

bachToDoblinProposal : NetworkEdge
bachToDoblinProposal = network-edge
  joschaBach rickDoblin
  Genealogy.recommendationExposure
  Genealogy.gradeC
  (Sources.bachForbiddenResearch20160710 ∷ [])
  "Bach named Rick Doblin as a potentially interesting invitee in a brainstorm sent to Epstein; proposal is not attendance, acquaintance or funding."

mapsToIbogaineProgramme : NetworkEdge
mapsToIbogaineProgramme = network-edge
  maps ibogaineResearch
  Genealogy.directDocumentedTransfer
  Genealogy.gradeA
  (Sources.mapsHistoricalIbogaineProgramme ∷ [])
  "MAPS' own published history records observational ibogaine studies."

epsteinToScopolamineInformation : NetworkEdge
epsteinToScopolamineInformation = network-edge
  jeffreyEpstein scopolamineInformation
  Genealogy.recommendationExposure
  Genealogy.gradeA
  (Sources.verglasScopolamineForward20150127 ∷ [])
  "A scopolamine item was forwarded directly to Epstein; this is documented information exposure only."

epsteinToTrumpetPlants : NetworkEdge
epsteinToTrumpetPlants = network-edge
  jeffreyEpstein trumpetPlants
  Genealogy.personnelInstitutionalContinuity
  Genealogy.gradeA
  (Sources.epsteinTrumpetPlants20140303 ∷ [])
  "Epstein directly referred to 'my trumpet plants at nursery'; botanical identity and purpose remain open."

------------------------------------------------------------------------
-- PROMOTION FIREWALLS.
------------------------------------------------------------------------

data DocumentedInterestEstablishesAdministration : Set where
data ProposedInviteEstablishesMeeting : Set where
data NetworkPathEstablishesDirectFunding : Set where
data SameMilieuEstablishesCoordination : Set where
data TrumpetPlantReferenceEstablishesScopolamineUse : Set where

documentedInterestDoesNotEstablishAdministration :
  DocumentedInterestEstablishesAdministration → ⊥
documentedInterestDoesNotEstablishAdministration ()

proposedInviteDoesNotEstablishMeeting : ProposedInviteEstablishesMeeting → ⊥
proposedInviteDoesNotEstablishMeeting ()

networkPathDoesNotEstablishDirectFunding : NetworkPathEstablishesDirectFunding → ⊥
networkPathDoesNotEstablishDirectFunding ()

sameMilieuDoesNotEstablishCoordination : SameMilieuEstablishesCoordination → ⊥
sameMilieuDoesNotEstablishCoordination ()

trumpetReferenceDoesNotEstablishScopolamineUse :
  TrumpetPlantReferenceEstablishesScopolamineUse → ⊥
trumpetReferenceDoesNotEstablishScopolamineUse ()

-- Re-export the generic universal-network firewall as the exact donor theorem.
oneStrongEdgeDoesNotEstablishUniversalNetwork :
  Genealogy.OneStrongEdgeEstablishesUniversalNetwork → ⊥
oneStrongEdgeDoesNotEstablishUniversalNetwork =
  Genealogy.oneStrongEdgeDoesNotEstablishUniversalNetwork

record EpsteinPsychedelicNetworkBoundary : Set where
  constructor epstein-psychedelic-network-boundary
  field
    directCorrespondenceIsStrongEdge : Bool
    explicitFundingRequestIsStrongEdge : Bool
    proposedInviteIsStrongHistoricalEdge : Bool
    corpusAdjacencyCreatesCoordination : Bool
    networkPathCreatesDirectEpsteinMAPSFunding : Bool
    documentedInterestCreatesAdministrationClaim : Bool

canonicalEpsteinPsychedelicNetworkBoundary : EpsteinPsychedelicNetworkBoundary
canonicalEpsteinPsychedelicNetworkBoundary =
  epstein-psychedelic-network-boundary true true false false false false
