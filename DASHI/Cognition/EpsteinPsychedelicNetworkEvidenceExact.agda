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
-- references as exact case-local identifiers. No parallel evidence ladder is
-- introduced.
------------------------------------------------------------------------

data NetworkNode : Set where
  jeffreyEpstein : NetworkNode
  ginoYu : NetworkNode
  robertKuhn : NetworkNode
  joschaBach : NetworkNode
  rickDoblin : NetworkNode
  maps : NetworkNode
  cubaConsciousnessEvent : NetworkNode
  psychedelicResearchMilieu : NetworkNode
  mindBodyResearchCommunity : NetworkNode
  specialAbilitySearch : NetworkNode
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
  (Sources.yuExperientialProposal20161017 ∷ Sources.yuUpdateCuba20170216 ∷
   Sources.yuBenefactorBrokerage20170221 ∷ Sources.yuPsychedelicAwakeningReport20171125 ∷ [])
  "Direct correspondence documents an ongoing Yu-Epstein relationship around altered-state/consciousness research planning, funding and introductions."

epsteinFundingCubaEvent : NetworkEdge
epsteinFundingCubaEvent = network-edge
  jeffreyEpstein cubaConsciousnessEvent
  Genealogy.fundingOrganisationalLink
  Genealogy.gradeA
  (Sources.yuUpdateCuba20170216 ∷ Sources.yuBenefactorBrokerage20170221 ∷
   Sources.epsteinCubaSent25k20170315 ∷ Sources.yuPsychedelicAwakeningReport20171125 ∷ [])
  "The primary correspondence progresses from a USD 25,000 request/approval and explicit sponsor identification to Epstein's later statement that he had sent USD 25,000 and Yu's later report that the event depended on Epstein sponsorship; bank settlement remains a distinct stronger receipt."

record BrokerageAttributionReceipt : Set where
  constructor brokerage-attribution-receipt
  field
    attributedBroker : NetworkNode
    attributingSource : NetworkNode
    targetEvent : NetworkNode
    sourceDocument : Sources.SourceIdentity
    fundTransferFacilitationAttributed : Bool
    relationshipBringingAttributed : Bool
    completedThirdPartyIntroductionPaid : Bool
open BrokerageAttributionReceipt public

yuAttributesEpsteinBrokerage : BrokerageAttributionReceipt
yuAttributesEpsteinBrokerage = brokerage-attribution-receipt
  jeffreyEpstein ginoYu cubaConsciousnessEvent
  Sources.yuBenefactorBrokerage20170221
  true true false

record IntroductionReceipt : Set where
  constructor introduction-receipt
  field
    requester : NetworkNode
    broker : NetworkNode
    introducedParty : NetworkNode
    requestSource : Sources.SourceIdentity
    completionSource : Sources.SourceIdentity
    requested : Bool
    performed : Bool
    acknowledgedByIntroducedParty : Bool
    psychedelicPurposeEstablished : Bool
    wrongdoingEstablished : Bool
open IntroductionReceipt public

kuhnIntroductionReceipt : IntroductionReceipt
kuhnIntroductionReceipt = introduction-receipt
  jeffreyEpstein ginoYu robertKuhn
  Sources.epsteinRequestsKuhnIntroduction20160818
  Sources.kuhnAcknowledgesYuIntroduction20160821
  true true true false false

record ConveningProposalReceipt : Set where
  constructor convening-proposal-receipt
  field
    proposer : NetworkNode
    proposedWith : NetworkNode
    targetCommunity : NetworkNode
    sourceDocument : Sources.SourceIdentity
    epsteinLocationProposed : Bool
    combinedConnectionsProposed : Bool
    communityBuildingExplicit : Bool
    completedAsProposed : Bool
open ConveningProposalReceipt public

jointCommunityConveningProposal : ConveningProposalReceipt
jointCommunityConveningProposal = convening-proposal-receipt
  ginoYu jeffreyEpstein mindBodyResearchCommunity
  Sources.yuJointCommunityConveningProposal20160908
  true true true false

yuToPsychedelicMilieu : NetworkEdge
yuToPsychedelicMilieu = network-edge
  ginoYu psychedelicResearchMilieu
  Genealogy.directDocumentedTransfer
  Genealogy.gradeA
  (Sources.yuExperientialProposal20161017 ∷ Sources.cubaConferenceAbstractPacket ∷
   Sources.yuPsychedelicAwakeningReport20171125 ∷ [])
  "Yu's event/conference materials explicitly include ayahuasca and ibogaine/iboga; his later report to Epstein explicitly describes 'psychedelic awakening' groups and an attached account of recent psilocybin use."

epsteinFundingSpecialAbilitySearch : NetworkEdge
epsteinFundingSpecialAbilitySearch = network-edge
  jeffreyEpstein specialAbilitySearch
  Genealogy.fundingOrganisationalLink
  Genealogy.gradeA
  (Sources.epsteinSpecialAbilityFunding20180308 ∷ [])
  "Epstein directly instructed his accountant to send Yu USD 25,000 from his foundation so Yu could find people with 'special ability'; execution of the bank transfer remains separately verifiable."

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
  "MAPS' own records describe a Rick Doblin-initiated ibogaine outcome-study effort and completed observational ibogaine studies; this is an independently sourced institutional link, not an Epstein-to-MAPS edge."

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
data BrokerageAttributionEstablishesCompletedIntroduction : Set where
data TransferStatementEstablishesBankSettlement : Set where
data ObservedIntroductionEstablishesPsychedelicPurpose : Set where
data ConveningProposalEstablishesCompletedEvent : Set where

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

brokerageAttributionDoesNotEstablishCompletedIntroduction :
  BrokerageAttributionEstablishesCompletedIntroduction → ⊥
brokerageAttributionDoesNotEstablishCompletedIntroduction ()

transferStatementDoesNotEstablishBankSettlement :
  TransferStatementEstablishesBankSettlement → ⊥
transferStatementDoesNotEstablishBankSettlement ()

observedIntroductionDoesNotEstablishPsychedelicPurpose :
  ObservedIntroductionEstablishesPsychedelicPurpose → ⊥
observedIntroductionDoesNotEstablishPsychedelicPurpose ()

conveningProposalDoesNotEstablishCompletedEvent :
  ConveningProposalEstablishesCompletedEvent → ⊥
conveningProposalDoesNotEstablishCompletedEvent ()

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
    senderStatementOfTransferIsFundingEvidence : Bool
    explicitBrokerageAttributionRecorded : Bool
    observedBrokeredIntroductionRecorded : Bool
    jointConveningProposalRecorded : Bool
    proposedInviteIsStrongHistoricalEdge : Bool
    corpusAdjacencyCreatesCoordination : Bool
    networkPathCreatesDirectEpsteinMAPSFunding : Bool
    documentedInterestCreatesAdministrationClaim : Bool
    transferStatementCreatesBankSettlement : Bool

canonicalEpsteinPsychedelicNetworkBoundary : EpsteinPsychedelicNetworkBoundary
canonicalEpsteinPsychedelicNetworkBoundary =
  epstein-psychedelic-network-boundary
    true true true true true true false false false false false
