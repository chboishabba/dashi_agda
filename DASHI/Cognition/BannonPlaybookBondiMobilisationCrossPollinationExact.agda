module DASHI.Cognition.BannonPlaybookBondiMobilisationCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PsychologicalInfluenceInfrastructureCrossPollinationExact as Psych
import DASHI.Cognition.BannonCambridgeAnalyticaInfluenceInfrastructureExact as CA
import DASHI.Cognition.TrumpMarALagoBannonBridgeExact as Bannon
import DASHI.Cognition.TurningPointEpsteinNarrativePressureExact as TPUSA
import DASHI.Governance.HansonHerzogEmancipatoryGrammarCrossPollinationExact as Herzog
import DASHI.Law.JarrettPostBondiConstitutionalSourceReceiptsExact as Jarrett

------------------------------------------------------------------------
-- BANNON PLAYBOOK / BONDI MOBILISATION CROSS-POLLINATION
--
-- The event state and the mobilisation operator are independent coordinates.
-- A real event can be exploited strategically; a strategically exploited event
-- need not have been staged. Conversely, evidence that a political actor has a
-- public influence playbook does not establish authorship of an underlying
-- event.
------------------------------------------------------------------------

data EventStatus : Set where
  independentlyEstablishedEvent : EventStatus
  contestedUnderlyingEvent : EventStatus
  stagedEventEstablished : EventStatus

data MobilisationStage : Set where
  selectEvent : MobilisationStage
  frameThreat : MobilisationStage
  identifyEnemyOrOutGroup : MobilisationStage
  saturateAttention : MobilisationStage
  delegitimiseCounterMedia : MobilisationStage
  demandExceptionalResponse : MobilisationStage
  institutionaliseResponse : MobilisationStage
  retainNewCapacity : MobilisationStage
  suppressOrRaiseCounterNarratives : MobilisationStage

data PlaybookSurface : Set where
  bannonFloodZone : PlaybookSurface
  bannonOppositionMedia : PlaybookSurface
  bannonAdministrativeDeconstruction : PlaybookSurface
  cambridgeAnalyticaTargeting : PlaybookSurface
  bondiPostAttackMobilisation : PlaybookSurface
  tpusaEpsteinNarrativePressure : PlaybookSurface

record PublicPlaybookReceipt : Set where
  constructor public-playbook-receipt
  field
    surface : PlaybookSurface
    source : String
    boundedFinding : String
    publicDoctrinePaid : Bool
    covertCoordinationPaid : Bool
open PublicPlaybookReceipt public

bannonFloodZoneReceipt : PublicPlaybookReceipt
bannonFloodZoneReceipt = public-playbook-receipt
  bannonFloodZone
  "Steve Bannon quoted by Michael Lewis, 2018; later scholarly/media discussion of the 'flood the zone' strategy"
  "Bannon publicly described the media as the real opposition and advocated overwhelming the information environment rather than merely rebutting individual stories."
  true false

bannonOppositionMediaReceipt : PublicPlaybookReceipt
bannonOppositionMediaReceipt = public-playbook-receipt
  bannonOppositionMedia
  "CPAC 2017 / Washington Post reporting"
  "Bannon repeatedly described major media as the 'opposition party' and framed political communication as continuing conflict with that institutional adversary."
  true false

bannonAdministrativeReceipt : PublicPlaybookReceipt
bannonAdministrativeReceipt = public-playbook-receipt
  bannonAdministrativeDeconstruction
  "CPAC 2017 transcript/reporting"
  "Bannon publicly named 'deconstruction of the administrative state' as one of the Trump administration's three principal lines of work and linked cabinet selection to that objective."
  true false

caTargetingReceipt : PublicPlaybookReceipt
caTargetingReceipt = public-playbook-receipt
  cambridgeAnalyticaTargeting
  "Cambridge Analytica / SCL / FEC / FTC / UK Parliament source bundle"
  "Bannon's Cambridge Analytica period supplies a documented voter-data, segmentation, targeting and campaign-delivery infrastructure. Deployment does not establish outcome causation."
  true false

bondiMobilisationReceipt : PublicPlaybookReceipt
bondiMobilisationReceipt = public-playbook-receipt
  bondiPostAttackMobilisation
  "Australian government, Royal Commission, ABC and NSW post-Bondi legal sources, 2025-2026"
  "Following the Bondi attack, governments and political actors converted security/antisemitism framing into Herzog solidarity diplomacy, protest restrictions, policing/security operations, hate-speech policy activity and a Royal Commission with dedicated online/media and intelligence/security hearing blocks. One NSW protest-law expansion was later invalidated by the Court of Appeal."
  true false

tpusaPressureReceipt : PublicPlaybookReceipt
tpusaPressureReceipt = public-playbook-receipt
  tpusaEpsteinNarrativePressure
  "TPUSA Student Action Summit / AmericaFest 2025 source bundle"
  "TPUSA provides a high-capacity narrative mobilisation surface around the Epstein-files dispute, including base pressure, leadership response and later attenuation."
  true false

------------------------------------------------------------------------
-- Event ontology is independent of mobilisation/exploitation.
------------------------------------------------------------------------

record EventMobilisationBoundary : Set where
  constructor event-mobilisation-boundary
  field
    mobilisationRequiresStagedEvent : Bool
    realEventCannotBeStrategicallyExploited : Bool
    documentedPlaybookProvesEventAuthorship : Bool
    policyBenefitProvesPriorPlanning : Bool
    mobilisationSequenceWorthComparing : Bool
open EventMobilisationBoundary public

canonicalEventMobilisationBoundary : EventMobilisationBoundary
canonicalEventMobilisationBoundary = event-mobilisation-boundary
  false false false false true

data MobilisationImpliesStaging : Set where
data BenefitImpliesAuthorship : Set where
data PublicPlaybookImpliesSpecificEventControl : Set where

mobilisationDoesNotCreateStaging : MobilisationImpliesStaging → ⊥
mobilisationDoesNotCreateStaging ()

benefitDoesNotCreateAuthorship : BenefitImpliesAuthorship → ⊥
benefitDoesNotCreateAuthorship ()

playbookDoesNotCreateSpecificEventControl : PublicPlaybookImpliesSpecificEventControl → ⊥
playbookDoesNotCreateSpecificEventControl ()

------------------------------------------------------------------------
-- Comparative mobilisation pipeline.
------------------------------------------------------------------------

record MobilisationPipeline : Set where
  constructor mobilisation-pipeline
  field
    label : String
    eventStatus : EventStatus
    stages : List MobilisationStage
    firstOrderBeneficiaryQuestion : String
    secondOrderBeneficiaryQuestion : String
    thirdOrderBeneficiaryQuestion : String
    sameActorCoordinationPaid : Bool
open MobilisationPipeline public

bondiPipeline : MobilisationPipeline
bondiPipeline = mobilisation-pipeline
  "Bondi attack -> security/antisemitism mobilisation -> law/policing/commission"
  independentlyEstablishedEvent
  (selectEvent ∷ frameThreat ∷ demandExceptionalResponse ∷ institutionaliseResponse ∷ retainNewCapacity ∷ suppressOrRaiseCounterNarratives ∷ [])
  "Which specific political, advocacy, security and community organisations gained immediate agenda access, resources or legitimacy?"
  "Which institutions gained new policing, speech-regulation, inquiry, intelligence or security capacities?"
  "Which post-Bondi capacities persist after the immediate emergency and alter future protest, speech, diplomacy or security routing?"
  false

bannonPipeline : MobilisationPipeline
bannonPipeline = mobilisation-pipeline
  "Bannon public information-conflict playbook"
  contestedUnderlyingEvent
  (frameThreat ∷ identifyEnemyOrOutGroup ∷ saturateAttention ∷ delegitimiseCounterMedia ∷ institutionaliseResponse ∷ retainNewCapacity ∷ [])
  "Who gains attention, audience capture or agenda-setting advantage from saturation/conflict?"
  "Which political organisations convert attention into votes, donations, appointments or policy leverage?"
  "Which institutional changes persist after the information cycle, especially personnel/state-capacity changes?"
  false

------------------------------------------------------------------------
-- Ideology / identity boundary for beneficiary analysis.
------------------------------------------------------------------------

data BeneficiaryCategory : Set where
  specificZionistPoliticalOrganisation : BeneficiaryCategory
  specificChristianZionistPoliticalNetwork : BeneficiaryCategory
  israeliStateInstitution : BeneficiaryCategory
  defenceOrIntelligenceContractor : BeneficiaryCategory
  politicalPartyOrCampaign : BeneficiaryCategory
  jewishPeopleAsCollective : BeneficiaryCategory
  christiansAsCollective : BeneficiaryCategory

record BeneficiaryBoundary : Set where
  constructor beneficiary-boundary
  field
    zionismCanBeAnalysedAsPoliticalIdeology : Bool
    christianZionistNetworksCanBeAnalysedAsPoliticalActors : Bool
    jewishIdentityImpliesZionistAgency : Bool
    christianIdentityImpliesChristianZionistAgency : Bool
    beneficiaryStatusImpliesEventAuthorship : Bool
open BeneficiaryBoundary public

canonicalBeneficiaryBoundary : BeneficiaryBoundary
canonicalBeneficiaryBoundary = beneficiary-boundary true true false false false

------------------------------------------------------------------------
-- Next max-cut: prove actual method/capacity transfer, not mere resemblance.
------------------------------------------------------------------------

data MobilisationDebt : Set where
  bannonFloodZoneToEpsteinMedia : MobilisationDebt
  bannonPlaybookToTPUSANarrative : MobilisationDebt
  bondiSecurityFramingToSpecificLaw : MobilisationDebt
  bondiMobilisationToPersistentCapacity : MobilisationDebt
  zionistOrganisationToSpecificPolicyBenefit : MobilisationDebt
  christianZionistNetworkToSpecificPolicyBenefit : MobilisationDebt

record MobilisationAcquisition : Set where
  constructor mobilisation-acquisition
  field
    debt : MobilisationDebt
    priority : Nat
    requiresSameObjectReceipt : Bool
    question : String
open MobilisationAcquisition public

canonicalMobilisationAcquisition : List MobilisationAcquisition
canonicalMobilisationAcquisition =
  mobilisation-acquisition bannonFloodZoneToEpsteinMedia 100 true
    "Do Bannon's Epstein rehabilitation materials instantiate his publicly documented saturation/opposition-media playbook in traceable messages, timing, channel selection or measurement?"
  ∷ mobilisation-acquisition bondiSecurityFramingToSpecificLaw 98 true
    "For each post-Bondi law/power, which actor proposed it, which event justification was invoked, who lobbied for it, and what exact power changed?"
  ∷ mobilisation-acquisition bondiMobilisationToPersistentCapacity 97 true
    "Which exceptional post-Bondi capacities persisted, expanded or migrated after the immediate security event?"
  ∷ mobilisation-acquisition bannonPlaybookToTPUSANarrative 95 true
    "Is there personnel/method/channel continuity between Bannon-style saturation strategy and TPUSA's Epstein-files narrative handling?"
  ∷ mobilisation-acquisition zionistOrganisationToSpecificPolicyBenefit 94 true
    "Which named Zionist political/advocacy organisations obtained identifiable policy, access, funding or regulatory benefits from post-Bondi mobilisation?"
  ∷ mobilisation-acquisition christianZionistNetworkToSpecificPolicyBenefit 92 true
    "Which named Christian-Zionist political networks obtained identifiable agenda, electoral, policy or foreign-policy benefits, independently of Christian identity as such?"
  ∷ []
