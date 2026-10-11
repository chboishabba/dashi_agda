module DASHI.Cognition.EpsteinPsychedelicSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- EPSTEIN / PSYCHEDELIC-CONSCIOUSNESS PRIMARY-SOURCE ATLAS
--
-- Case-specific source identity only. Presence in the released corpus does not
-- establish truth of every statement in a document, participation in a proposed
-- event, administration of a substance, or a direct Epstein -> MAPS payment.
------------------------------------------------------------------------

data SourceRole : Set where
  directCorrespondence : SourceRole
  forwardedProposal : SourceRole
  fundingCorrespondence : SourceRole
  conferencePacket : SourceRole
  plantLogisticsCorrespondence : SourceRole
  forwardedMediaItem : SourceRole
  institutionalHistory : SourceRole

data SourceIdentity : Set where
  bachForbiddenResearch20160710 : SourceIdentity
  yuExperientialProposal20161017 : SourceIdentity
  yuUpdateCuba20170216 : SourceIdentity
  yuNetworkReport20171113 : SourceIdentity
  cubaConferenceAbstractPacket : SourceIdentity
  epsteinTrumpetPlants20140303 : SourceIdentity
  verglasScopolamineForward20150127 : SourceIdentity
  mapsHistoricalIbogaineProgramme : SourceIdentity

sourceRole : SourceIdentity → SourceRole
sourceRole bachForbiddenResearch20160710 = directCorrespondence
sourceRole yuExperientialProposal20161017 = forwardedProposal
sourceRole yuUpdateCuba20170216 = fundingCorrespondence
sourceRole yuNetworkReport20171113 = directCorrespondence
sourceRole cubaConferenceAbstractPacket = conferencePacket
sourceRole epsteinTrumpetPlants20140303 = plantLogisticsCorrespondence
sourceRole verglasScopolamineForward20150127 = forwardedMediaItem
sourceRole mapsHistoricalIbogaineProgramme = institutionalHistory

sourceReference : SourceIdentity → String
sourceReference bachForbiddenResearch20160710 = "EFTA02458524"
sourceReference yuExperientialProposal20161017 = "EFTA00814480"
sourceReference yuUpdateCuba20170216 = "EFTA01054265"
sourceReference yuNetworkReport20171113 = "EFTA00957006"
sourceReference cubaConferenceAbstractPacket = "EFTA00797045"
sourceReference epsteinTrumpetPlants20140303 = "EFTA00984429"
sourceReference verglasScopolamineForward20150127 = "EFTA00865569"
sourceReference mapsHistoricalIbogaineProgramme = "MAPS institutional history / PubMed PMID 24830183"

boundedSourceClaim : SourceIdentity → String
boundedSourceClaim bachForbiddenResearch20160710 =
  "Joscha Bach emailed Jeffrey Epstein a Forbidden Research brainstorm discussing psychedelic research and listing Rick Doblin among proposed invitees."
boundedSourceClaim yuExperientialProposal20161017 =
  "Gino Yu forwarded Jeffrey Epstein planning for an experiential transformation event explicitly mentioning ayahuasca and ibogaine and described existing funding plus a search for additional sponsorship."
boundedSourceClaim yuUpdateCuba20170216 =
  "Gino Yu sent Epstein an ayahuasca-experience attachment, described building a global research subject network, and asked whether USD 25,000 could be transferred for the Cuba event."
boundedSourceClaim yuNetworkReport20171113 =
  "Gino Yu reported further altered-state / protocol-development work to Epstein and sought Epstein's input; this source belongs to the same correspondence lineage."
boundedSourceClaim cubaConferenceAbstractPacket =
  "A released conference abstract packet in the Epstein corpus contains material explicitly discussing ayahuasca, mescaline, ibogaine / iboga, wellness and retreat settings; packet presence is not itself proof that Epstein selected or endorsed each abstract."
boundedSourceClaim epsteinTrumpetPlants20140303 =
  "Jeffrey Epstein emailed Ann Rodriguez asking about his 'trumpet plants at nursery'; the species and intended use are not identified by the email."
boundedSourceClaim verglasScopolamineForward20150127 =
  "Antoine Verglas forwarded material to Epstein whose subject explicitly identified scopolamine and its coercive/amnesic reputation; receipt does not establish use or administration."
boundedSourceClaim mapsHistoricalIbogaineProgramme =
  "MAPS' published institutional history describes observational ibogaine studies among its broader psychedelic research programme; this is a MAPS<->ibogaine bridge, not an Epstein funding receipt."

record EpsteinPsychedelicSourceBoundary : Set where
  constructor epstein-psychedelic-source-boundary
  field
    corpusPresenceImpliesParticipation : Bool
    proposedInviteImpliesAttendance : Bool
    sourceMentionsMAPSImpliesEpsteinFundedMAPS : Bool
    documentedInterestImpliesAdministration : Bool
    trumpetPlantEmailIdentifiesBrugmansia : Bool
    fundingOneEventImpliesFundingAllNetworkActivity : Bool
    sourceAttributionRetained : Bool

canonicalEpsteinPsychedelicSourceBoundary : EpsteinPsychedelicSourceBoundary
canonicalEpsteinPsychedelicSourceBoundary =
  epstein-psychedelic-source-boundary false false false false false false true

rickDoblinName : String
rickDoblinName = "Rick Doblin"

ibogaineKeyword : String
ibogaineKeyword = "ibogaine"

scopolamineKeyword : String
scopolamineKeyword = "scopolamine"
