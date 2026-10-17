module DASHI.Cognition.TrumpMarALagoBannonBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.TrumpEpsteinPoliticalRelationshipExact as TrumpEpstein
import DASHI.Cognition.BannonCambridgeAnalyticaInfluenceInfrastructureExact as Cambridge
import DASHI.Cognition.BannonCambridgeAnalyticaSystemicLeverageBridgeExact as CambridgeSystemic

------------------------------------------------------------------------
-- TRUMP / MAR-A-LAGO / BANNON BRIDGE
--
-- This owner strengthens the Trump-world acquisition lane with separately typed
-- infrastructures:
--   (1) Mar-a-Lago as an Epstein/Maxwell recruitment and records locus;
--   (2) Steve Bannon as a later political/media brokerage bridge to Epstein;
--   (3) Bannon's earlier Cambridge-Analytica/SCL/Mercer influence infrastructure.
-- The historical Bannon continuity is acquisition-relevant but does not prove
-- that Cambridge Analytica techniques were used in later Epstein media work.
-- The 2022 classified-documents search remains a distinct investigation absent
-- a document paying an Epstein-search purpose or seized-Epstein-material edge.
------------------------------------------------------------------------

data BridgeKind : Set where
  giuffreEmploymentAtMarALago : BridgeKind
  maxwellRecruitmentAtMarALago : BridgeKind
  maxwellTrialSubpoenaToMarALago : BridgeKind
  marALagoEmploymentRecordProduction : BridgeKind
  reinhartPriorEpsteinEmployeeRepresentation : BridgeKind
  classifiedDocumentsSearch : BridgeKind
  bannonCambridgeAnalyticaInfluenceInfrastructure : BridgeKind
  bannonSustainedCorrespondence : BridgeKind
  bannonEpsteinMediaRehabilitation : BridgeKind
  epsteinBannonPoliticalMessaging : BridgeKind
  bannonFarRightInternationalStrategy : BridgeKind

record BridgeReceipt : Set where
  constructor bridge-receipt
  field
    kind : BridgeKind
    sourceDescription : String
    relationshipOrInstitutionalEdgePaid : Bool
    directPrimaryOrOfficialRecord : Bool
    wrongdoingEstablishedByThisReceipt : Bool
    sameObjectWithOtherInvestigationEstablished : Bool
open BridgeReceipt public

giuffreEmploymentReceipt : BridgeReceipt
giuffreEmploymentReceipt = bridge-receipt
  giuffreEmploymentAtMarALago
  "DOJ-hosted Giuffre v Maxwell filings record that Giuffre obtained Mar-a-Lago employment records showing she worked there in 2000 while under 18."
  true true false false

maxwellRecruitmentReceipt : BridgeReceipt
maxwellRecruitmentReceipt = bridge-receipt
  maxwellRecruitmentAtMarALago
  "Giuffre's sentencing statement in United States v Maxwell states that Maxwell approached her at Mar-a-Lago in summer 2000 and procured her for Epstein; the statement is a victim account presented to the sentencing court."
  true true false false

marALagoSubpoenaReceipt : BridgeReceipt
marALagoSubpoenaReceipt = bridge-receipt
  maxwellTrialSubpoenaToMarALago
  "DOJ EFTA court subpoena dated October 5, 2021 commanded the Mar-a-Lago Club to appear in United States v Maxwell and produce specified employment records."
  true true false false

employmentRecordProductionReceipt : BridgeReceipt
employmentRecordProductionReceipt = bridge-receipt
  marALagoEmploymentRecordProduction
  "Giuffre v Maxwell discovery records expressly sought all documents concerning Giuffre's Mar-a-Lago employment/association and identified Mar-a-Lago among employers whose records were requested."
  true true false false

reinhartReceipt : BridgeReceipt
reinhartReceipt = bridge-receipt
  reinhartPriorEpsteinEmployeeRepresentation
  "Public reporting documents that magistrate judge Bruce Reinhart, before joining the bench, represented some Epstein employees; this historical legal-services relationship does not make the 2022 search an Epstein investigation."
  true false false false

classifiedSearchReceipt : BridgeReceipt
classifiedSearchReceipt = bridge-receipt
  classifiedDocumentsSearch
  "The August 2022 Mar-a-Lago search concerned presidential/classified records and obstruction-related offences; available warrants/FOIA records do not establish an Epstein-search purpose."
  true true false false

bannonCambridgeAnalyticaReceipt : BridgeReceipt
bannonCambridgeAnalyticaReceipt = bridge-receipt
  bannonCambridgeAnalyticaInfluenceInfrastructure
  "UK Parliament, FTC and FEC records establish Bannon's Cambridge Analytica leadership/infrastructure context, deceptive Facebook-data harvesting for voter profiling/targeting, substantial Trump-campaign vendor payments and cross-Atlantic brokerage; election-outcome causation and illegal common-vendor coordination remain unestablished by the current receipt set."
  true true false false

bannonCorrespondenceReceipt : BridgeReceipt
bannonCorrespondenceReceipt = bridge-receipt
  bannonSustainedCorrespondence
  "House-released/DOJ-era reporting documents sustained 2018-2019 Epstein-Bannon correspondence; Guardian's 2026 visualization reports nearly 1,500 emails between them or their assistants."
  true false false false

bannonMediaRehabReceipt : BridgeReceipt
bannonMediaRehabReceipt = bridge-receipt
  bannonEpsteinMediaRehabilitation
  "Released texts and video show Bannon advising Epstein on media presentation and filming extensive interview material reportedly intended for a documentary about Epstein."
  true false false false

bannonPoliticalMessagingReceipt : BridgeReceipt
bannonPoliticalMessagingReceipt = bridge-receipt
  epsteinBannonPoliticalMessaging
  "Released 2018 messages show Epstein advising Bannon during a pro-Trump media campaign while Bannon simultaneously advised Epstein on media/legal reputation strategy."
  true false false false

bannonInternationalStrategyReceipt : BridgeReceipt
bannonInternationalStrategyReceipt = bridge-receipt
  bannonFarRightInternationalStrategy
  "2026 reporting on released files describes Bannon seeking Epstein support/funding in relation to European right-populist political efforts; exact completed funding edges remain separately receipt-dependent."
  true false false false

------------------------------------------------------------------------
-- Bannon historical influence cross-pollination.
------------------------------------------------------------------------

bannonHistoricalInfluenceBoundary : Cambridge.BannonInfluenceInfrastructureBoundary
bannonHistoricalInfluenceBoundary = Cambridge.canonicalBannonInfluenceInfrastructureBoundary

bannonSystemicInfluenceBoundary : CambridgeSystemic.CambridgeAnalyticaSystemicBoundary
bannonSystemicInfluenceBoundary = CambridgeSystemic.canonicalCambridgeAnalyticaSystemicBoundary

bannonTargetedInfluenceCapabilityPaid :
  Cambridge.targetedPoliticalInfluenceCapabilityPaid
    Cambridge.canonicalBannonInfluenceInfrastructureBoundary ≡ true
bannonTargetedInfluenceCapabilityPaid = refl

bannonElectionOutcomeCausationStillUnpaid :
  Cambridge.trumpVictoryCausedByCambridgeAnalytica
    Cambridge.canonicalBannonInfluenceInfrastructureBoundary ≡ false
bannonElectionOutcomeCausationStillUnpaid = refl

bannonLaterEpsteinTechniqueReuseStillUnpaid :
  Cambridge.laterEpsteinMediaWorkProvesTechniqueReuse
    Cambridge.canonicalBannonInfluenceInfrastructureBoundary ≡ false
bannonLaterEpsteinTechniqueReuseStillUnpaid = refl

bannonThirdOrderSystemicAcquisitionStillOpen :
  CambridgeSystemic.laterEpsteinTechniqueReuseResolved
    CambridgeSystemic.canonicalCambridgeAnalyticaSystemicBoundary ≡ false
bannonThirdOrderSystemicAcquisitionStillOpen = refl

------------------------------------------------------------------------
-- Participation/status refinement.
------------------------------------------------------------------------

record TrumpParticipationLatticeBoundary : Set where
  constructor trump-participation-lattice-boundary
  field
    socialParticipationEstablished : Bool
    networkAccessParticipationEstablished : Bool
    marALagoRecruitmentLocusEstablished : Bool
    bannonHistoricalInfluenceInfrastructureEstablished : Bool
    knowledgeOfEpsteinCrimesResolved : Bool
    facilitationOfEpsteinCrimesEstablished : Bool
    criminalParticipationEstablishedByCurrentReceiptSet : Bool
open TrumpParticipationLatticeBoundary public

canonicalTrumpParticipationLatticeBoundary : TrumpParticipationLatticeBoundary
canonicalTrumpParticipationLatticeBoundary =
  trump-participation-lattice-boundary true true true true false false false

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data RecruitmentLocusImpliesOwnerKnowledge : Set where
data PriorRepresentationImpliesSearchPurpose : Set where
data SamePropertyImpliesSameInvestigation : Set where
data BannonBridgeImpliesTrumpDirection : Set where
data BannonEpsteinContactImpliesCriminalParticipation : Set where
data VictimAccountImpliesEveryAdjacentActorKnowledge : Set where
data PriorInfluenceInfrastructureImpliesLaterTechniqueReuse : Set where

recruitmentLocusDoesNotCreateOwnerKnowledge : RecruitmentLocusImpliesOwnerKnowledge → ⊥
recruitmentLocusDoesNotCreateOwnerKnowledge ()

priorRepresentationDoesNotCreateSearchPurpose : PriorRepresentationImpliesSearchPurpose → ⊥
priorRepresentationDoesNotCreateSearchPurpose ()

samePropertyDoesNotCreateSameInvestigation : SamePropertyImpliesSameInvestigation → ⊥
samePropertyDoesNotCreateSameInvestigation ()

bannonBridgeDoesNotCreateTrumpDirection : BannonBridgeImpliesTrumpDirection → ⊥
bannonBridgeDoesNotCreateTrumpDirection ()

bannonContactDoesNotCreateCriminalParticipation : BannonEpsteinContactImpliesCriminalParticipation → ⊥
bannonContactDoesNotCreateCriminalParticipation ()

victimAccountDoesNotCreateAdjacentKnowledge : VictimAccountImpliesEveryAdjacentActorKnowledge → ⊥
victimAccountDoesNotCreateAdjacentKnowledge ()

priorInfluenceInfrastructureDoesNotCreateLaterTechniqueReuse :
  PriorInfluenceInfrastructureImpliesLaterTechniqueReuse → ⊥
priorInfluenceInfrastructureDoesNotCreateLaterTechniqueReuse ()
