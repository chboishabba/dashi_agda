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
  fundingExecutionStatement : SourceRole
  conferencePacket : SourceRole
  plantLogisticsCorrespondence : SourceRole
  forwardedMediaItem : SourceRole
  institutionalHistory : SourceRole

data SourceIdentity : Set where
  bachForbiddenResearch20160710 : SourceIdentity
  yuExperientialProposal20161017 : SourceIdentity
  yuUpdateCuba20170216 : SourceIdentity
  yuBenefactorBrokerage20170221 : SourceIdentity
  epsteinCubaSent25k20170315 : SourceIdentity
  yuPsychedelicAwakeningReport20171125 : SourceIdentity
  epsteinSpecialAbilityFunding20180308 : SourceIdentity
  cubaConferenceAbstractPacket : SourceIdentity
  epsteinTrumpetPlants20140303 : SourceIdentity
  verglasScopolamineForward20150127 : SourceIdentity
  mapsHistoricalIbogaineProgramme : SourceIdentity

sourceRole : SourceIdentity → SourceRole
sourceRole bachForbiddenResearch20160710 = directCorrespondence
sourceRole yuExperientialProposal20161017 = forwardedProposal
sourceRole yuUpdateCuba20170216 = fundingCorrespondence
sourceRole yuBenefactorBrokerage20170221 = fundingCorrespondence
sourceRole epsteinCubaSent25k20170315 = fundingExecutionStatement
sourceRole yuPsychedelicAwakeningReport20171125 = directCorrespondence
sourceRole epsteinSpecialAbilityFunding20180308 = fundingCorrespondence
sourceRole cubaConferenceAbstractPacket = conferencePacket
sourceRole epsteinTrumpetPlants20140303 = plantLogisticsCorrespondence
sourceRole verglasScopolamineForward20150127 = forwardedMediaItem
sourceRole mapsHistoricalIbogaineProgramme = institutionalHistory

sourceReference : SourceIdentity → String
sourceReference bachForbiddenResearch20160710 = "EFTA02458524"
sourceReference yuExperientialProposal20161017 = "EFTA00814480"
sourceReference yuUpdateCuba20170216 = "EFTA01054265"
sourceReference yuBenefactorBrokerage20170221 = "EFTA00692098"
sourceReference epsteinCubaSent25k20170315 = "EFTA01052096 / EFTA02656417 copies"
sourceReference yuPsychedelicAwakeningReport20171125 = "EFTA00984125-EFTA00984126 / EFTA02581361 copy"
sourceReference epsteinSpecialAbilityFunding20180308 = "EFTA00862301"
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
boundedSourceClaim yuBenefactorBrokerage20170221 =
  "Yu cc'd Epstein to the Cuba organisers, called Epstein his benefactor, said Epstein could arrange the conference fund transfer, and explicitly described Epstein as well connected and able to bring significant relationships."
boundedSourceClaim epsteinCubaSent25k20170315 =
  "A preserved March 2017 correspondence copy quotes Epstein saying he had sent USD 25,000 for Cuba; this is a sender statement of transfer, while bank-level settlement remains a distinct stronger receipt."
boundedSourceClaim yuPsychedelicAwakeningReport20171125 =
  "Yu reported to Epstein on the sponsored Cuba event, talks to groups he called 'psychedelic awakening', work with two subjects, the prior USD 100,000 offer, travel to see Epstein and introductions to others; the attached correspondent also describes recent psilocybin use."
boundedSourceClaim epsteinSpecialAbilityFunding20180308 =
  "Epstein instructed Richard Kahn to send Yu USD 25,000 from his foundation so Yu could find people with 'special ability'; the instruction is direct funding/procurement evidence while final bank settlement remains separately verifiable."
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
    transferStatementEqualsBankSettlement : Bool
    fundingInstructionEqualsCompletedPayment : Bool
    sourceAttributionRetained : Bool

canonicalEpsteinPsychedelicSourceBoundary : EpsteinPsychedelicSourceBoundary
canonicalEpsteinPsychedelicSourceBoundary =
  epstein-psychedelic-source-boundary false false false false false false false false true

rickDoblinName : String
rickDoblinName = "Rick Doblin"

ibogaineKeyword : String
ibogaineKeyword = "ibogaine"

scopolamineKeyword : String
scopolamineKeyword = "scopolamine"
