module DASHI.Governance.HansonIsraelJewishPluralitySurveillanceGrammarExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.EmancipatoryVocabularyRelationalGrammarNoncollapseExact as Vocabulary
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Interop.GodsEyeViewProofCarryingWorldOntologyExact as Panopticon
import DASHI.Governance.PalantirProcurementLegibilityAdapterExact as PalantirProcurement
import DASHI.Governance.PalantirPlatformCapabilityEvidenceExact as PalantirCapability
import DASHI.Law.AustraliaIsraelInfluenceLobbyingSpeechGovernanceExact as Influence
import DASHI.Governance.HansonOneNationPoliticalEcologyExact as HansonEcology
import DASHI.Governance.HansonHerzogEmancipatoryGrammarCrossPollinationExact as HansonHerzog

------------------------------------------------------------------------
-- HANSON / ISRAEL / JEWISH-PLURALITY / PALANTIR-SURVEILLANCE BOUNDARY
--
-- ATTRIBUTION
--
-- External sources own documented relations/statements:
--   * Pauline Hanson's One Nation: explicit pro-Israel / antisemitism-protection
--     rhetoric and "Judeo-Christian society" self-description.
--   * Australian Jewish Association (AJA) / JNS reporting: AJA praise/support
--     for Hanson, including after the 2025 burqa stunt.
--   * AIJAC / SBS: 2016 condemnation of Hanson/One Nation anti-minority rhetoric.
--   * Jewish Council of Australia submission reported in 2026: attributed
--     concern about One Nation, neo-Nazi networks and antisemitism.
--   * ECAJ: Jillian Segal was ECAJ immediate past president at appointment as
--     Special Envoy to Combat Antisemitism.
--   * Guardian/ABC/Parliamentary reporting: Shoebridge scrutiny of Palantir's
--     Australian government footprint and data/procurement opacity.
--
-- DASHI owns the theorem shape:
--
--   support/protection vocabulary for one community
--     != universal minority-protection grammar
--     != support for every political organisation claiming to speak for that
--        community
--     != foreign-state identity
--     != surveillance/procurement authority.
--
-- The module explicitly blocks conspiratorial closure:
--   Hanson + Segal + Palantir do NOT form a documented combined network here.
------------------------------------------------------------------------

data JewishPoliticalActorKind : Set where
  australianJewishPerson : JewishPoliticalActorKind
  australianJewishCommunityOrganisation : JewishPoliticalActorKind
  conservativeJewishAdvocacyOrganisation : JewishPoliticalActorKind
  mainstreamJewishPublicAffairsOrganisation : JewishPoliticalActorKind
  progressiveJewishOrganisation : JewishPoliticalActorKind
  antisemitismEnvoyInstitution : JewishPoliticalActorKind
  stateOfIsrael : JewishPoliticalActorKind
  israelAlignedBusinessOrganisation : JewishPoliticalActorKind

data SourceRole : Set where
  partySelfDescription : SourceRole
  organisationSelfDescription : SourceRole
  organisationPraise : SourceRole
  organisationCondemnation : SourceRole
  attributedCommunityCritique : SourceRole
  governmentAppointment : SourceRole
  parliamentaryScrutiny : SourceRole
  technologyProcurementReporting : SourceRole
  businessEngagementReporting : SourceRole
  searchResidual : SourceRole

record PoliticalSourceReceipt : Set where
  constructor political-source-receipt
  field
    institution : String
    title : String
    dateOrReference : String
    stableIdentifier : String
    role : SourceRole
    boundedClaim : String
    provesUnifiedJewishPosition : Bool
    provesUnifiedJewishPositionIsFalse :
      provesUnifiedJewishPosition ≡ false
    provesPolicyControl : Bool
    provesPolicyControlIsFalse :
      provesPolicyControl ≡ false

open PoliticalSourceReceipt public

oneNationIsraelSupport : PoliticalSourceReceipt
oneNationIsraelSupport =
  political-source-receipt
    "Pauline Hanson's One Nation"
    "Pauline Hanson supporting Israel and Australia's Jewish Community"
    "2024-05-16"
    "https://www.onenation.org.au/pauline-hanson-supporting-israel-and-australias-jewish-community"
    partySelfDescription
    "party-authored record of Hanson's strong public alignment with Israel and stated concern for Jewish community safety; contains broader party claims that remain party claims"
    false refl
    false refl

oneNationJudeoChristian2026 : PoliticalSourceReceipt
oneNationJudeoChristian2026 =
  political-source-receipt
    "Pauline Hanson's One Nation"
    "My Party is rightly called One Nation"
    "2026-06-22"
    "https://www.onenation.org.au/party-rightly-onenation"
    partySelfDescription
    "party-authored statement describing Australia as predominantly Judeo-Christian and framing Western civilisation as under siege"
    false refl
    false refl

ajaHansonPraise : PoliticalSourceReceipt
ajaHansonPraise =
  political-source-receipt
    "Australian Jewish Association / JNS reporting"
    "Australian Jewish group lauds senator for wearing burqa"
    "2025-11-25"
    "https://www.jns.org/israel-news/australian-jewish-group-lauds-senator-for-wearing-burqa"
    organisationPraise
    "AJA publicly thanked/praised Hanson for standing with its community and defended her after the 2025 burqa stunt"
    false refl
    false refl

aijacHansonCondemnation : PoliticalSourceReceipt
aijacHansonCondemnation =
  political-source-receipt
    "AIJAC / SBS reporting"
    "Jewish organisation condemns Hanson"
    "2016-07-06"
    "https://www.sbs.com.au/news/article/jewish-organisation-condemns-hanson/a90yk2zxv"
    organisationCondemnation
    "AIJAC publicly condemned Hanson/One Nation rhetoric as harmful to tolerance, community harmony and minorities"
    false refl
    false refl

jewishCouncil2026Concern : PoliticalSourceReceipt
jewishCouncil2026Concern =
  political-source-receipt
    "Jewish Council of Australia / Sydney Morning Herald reporting"
    "Jewish group links One Nation to neo-Nazis and antisemitism"
    "2026-06-16"
    "SMH report / royal-commission submission"
    attributedCommunityCritique
    "reported submission alleged a history of antisemitic views among some One Nation members and warned about far-right normalisation; this is an attributed submission, not a DASHI adjudication"
    false refl
    false refl

ecajSegalAppointment : PoliticalSourceReceipt
ecajSegalAppointment =
  political-source-receipt
    "Executive Council of Australian Jewry"
    "ECAJ statement on appointment of Jillian Segal AO as Special Envoy to Combat Antisemitism"
    "2024-07-09"
    "https://www.ecaj.org.au/appointment-of-jillian-segal-ao-as-special-envoy-to-combat-antisemitism/"
    organisationSelfDescription
    "ECAJ identified Segal as its immediate past president at the time of her appointment as Special Envoy"
    false refl
    false refl

shoebridgePalantirAudit : PoliticalSourceReceipt
shoebridgePalantirAudit =
  political-source-receipt
    "Guardian Australia / Senator David Shoebridge"
    "Calls grow to ban Palantir in Australia"
    "2026-04-30"
    "https://www.theguardian.com/technology/2026/apr/30/palantir-manifesto-australia-government-contracts"
    parliamentaryScrutiny
    "Shoebridge called for a halt/audit of new Palantir government contracts and raised lack of clarity about government data supplied to the company"
    false refl
    false refl

palantirAustraliaFootprint : PoliticalSourceReceipt
palantirAustraliaFootprint =
  political-source-receipt
    "ABC / Guardian Australia"
    "Palantir Australian government footprint"
    "2026 reporting"
    "ABC If You're Listening 2026-05-19; Guardian Australia 2026-04-30"
    technologyProcurementReporting
    "reporting describes substantial state/federal Australian Palantir contracts and use in defence, justice and other government data environments"
    false refl
    false refl

aiccHansonEngagementResidual : PoliticalSourceReceipt
aiccHansonEngagementResidual =
  political-source-receipt
    "Australian Financial Review"
    "Israel business group grapples with Pauline Hanson"
    "updated 2026-09-10"
    "AFR Rear Window headline/index; full event detail not independently recovered in this owner"
    businessEngagementReporting
    "AFR index confirms a report about an Israel-linked business group engaging with Hanson; exact invitation/event details remain a bounded source residual unless the full article is inspected"
    false refl
    false refl

canonicalSources : List PoliticalSourceReceipt
canonicalSources =
  oneNationIsraelSupport
  ∷ oneNationJudeoChristian2026
  ∷ ajaHansonPraise
  ∷ aijacHansonCondemnation
  ∷ jewishCouncil2026Concern
  ∷ ecajSegalAppointment
  ∷ shoebridgePalantirAudit
  ∷ palantirAustraliaFootprint
  ∷ aiccHansonEngagementResidual
  ∷ []

------------------------------------------------------------------------
-- JEWISH COMMUNITY / ISRAEL / ADVOCACY NONCOLLAPSE
------------------------------------------------------------------------

data JewishCommunityEqualsIsraelState : Set where
data AJAEqualsAllAustralianJews : Set where
data AIJACEqualsAllAustralianJews : Set where
data ECAJEqualsAllAustralianJews : Set where
data ProIsraelEqualsJewishCommunityPosition : Set where
data CriticismOfIsraelEqualsAntisemitismByDefinition : Set where
data SupportForIsraelEqualsUniversalMinorityProtection : Set where

jewishCommunityDoesNotEqualIsraelState :
  JewishCommunityEqualsIsraelState → ⊥
jewishCommunityDoesNotEqualIsraelState ()

ajaDoesNotEqualAllAustralianJews :
  AJAEqualsAllAustralianJews → ⊥
ajaDoesNotEqualAllAustralianJews ()

aijacDoesNotEqualAllAustralianJews :
  AIJACEqualsAllAustralianJews → ⊥
aijacDoesNotEqualAllAustralianJews ()

ecajDoesNotEqualAllAustralianJews :
  ECAJEqualsAllAustralianJews → ⊥
ecajDoesNotEqualAllAustralianJews ()

proIsraelDoesNotEqualUnifiedJewishPosition :
  ProIsraelEqualsJewishCommunityPosition → ⊥
proIsraelDoesNotEqualUnifiedJewishPosition ()

israelCriticismNotDefinitionallyAntisemitism :
  CriticismOfIsraelEqualsAntisemitismByDefinition → ⊥
israelCriticismNotDefinitionallyAntisemitism ()

israelSupportDoesNotAutoPayUniversalMinorityProtection :
  SupportForIsraelEqualsUniversalMinorityProtection → ⊥
israelSupportDoesNotAutoPayUniversalMinorityProtection ()

------------------------------------------------------------------------
-- SAME "COMMUNITY SAFETY" VOCABULARY, DIFFERENT MINORITY ROUTING
------------------------------------------------------------------------

data MinorityProtectionState : Set where
  universalMinorityProtectionState : MinorityProtectionState
  selectiveMinorityProtectionState : MinorityProtectionState

data CommunitySafetySurface : Set where
  protectMinoritiesFromHatred : CommunitySafetySurface

data MinorityRouting : Set where
  universalProtectionRouting : MinorityRouting
  selectiveProtectionRouting : MinorityRouting

communitySafetyObserver :
  MinorityProtectionState → CommunitySafetySurface
communitySafetyObserver universalMinorityProtectionState =
  protectMinoritiesFromHatred
communitySafetyObserver selectiveMinorityProtectionState =
  protectMinoritiesFromHatred

minorityRouting :
  MinorityProtectionState → MinorityRouting
minorityRouting universalMinorityProtectionState =
  universalProtectionRouting
minorityRouting selectiveMinorityProtectionState =
  selectiveProtectionRouting

minorityRoutingDiffers :
  minorityRouting universalMinorityProtectionState
  ≡ minorityRouting selectiveMinorityProtectionState → ⊥
minorityRoutingDiffers ()

communitySafetyVocabularyCannotDetermineUniversalProtection :
  INF.FactorsThrough communitySafetyObserver minorityRouting → ⊥
communitySafetyVocabularyCannotDetermineUniversalProtection =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      universalMinorityProtectionState
      selectiveMinorityProtectionState
      refl
      minorityRoutingDiffers)

------------------------------------------------------------------------
-- LOBBYING / PUBLIC AFFAIRS / INFLUENCE BOUNDARY
------------------------------------------------------------------------

australiaIsraelInfluenceBoundary : Influence.InfluenceBoundary
australiaIsraelInfluenceBoundary =
  Influence.canonicalInfluenceBoundary

data PublicAffairsProvesPolicyCapture : Set where
data SponsoredAccessProvesForeignControl : Set where
data JewishOrganisationAccessProvesJewishControl : Set where
data IsraelAlignmentProvesLobbyDirection : Set where

publicAffairsDoesNotProveCapture :
  PublicAffairsProvesPolicyCapture → ⊥
publicAffairsDoesNotProveCapture ()

sponsoredAccessDoesNotProveForeignControl :
  SponsoredAccessProvesForeignControl → ⊥
sponsoredAccessDoesNotProveForeignControl ()

organisationAccessDoesNotProveCollectiveControl :
  JewishOrganisationAccessProvesJewishControl → ⊥
organisationAccessDoesNotProveCollectiveControl ()

alignmentDoesNotProveLobbyDirection :
  IsraelAlignmentProvesLobbyDirection → ⊥
alignmentDoesNotProveLobbyDirection ()

------------------------------------------------------------------------
-- SEGAL / HANSON / PALANTIR: BLOCK UNSOURCED TRIADIC CLOSURE
------------------------------------------------------------------------

data HansonSegalDirectRelationshipEstablished : Set where
data SegalPalantirDirectRelationshipEstablished : Set where
data HansonPalantirDirectRelationshipEstablished : Set where
data HansonSegalPalantirCoordinatedNetworkEstablished : Set where

noHansonSegalRelationConstructed :
  HansonSegalDirectRelationshipEstablished → ⊥
noHansonSegalRelationConstructed ()

noSegalPalantirRelationConstructed :
  SegalPalantirDirectRelationshipEstablished → ⊥
noSegalPalantirRelationConstructed ()

noHansonPalantirRelationConstructed :
  HansonPalantirDirectRelationshipEstablished → ⊥
noHansonPalantirRelationConstructed ()

noTriadicNetworkConstructed :
  HansonSegalPalantirCoordinatedNetworkEstablished → ⊥
noTriadicNetworkConstructed ()

------------------------------------------------------------------------
-- PALANTIR / PANOPTICON
------------------------------------------------------------------------

palantirProcurementBoundary :
  PalantirProcurement.PalantirProcurementAdapterBoundary
palantirProcurementBoundary =
  PalantirProcurement.canonicalPalantirProcurementAdapterBoundary

palantirCapabilityBoundary :
  PalantirCapability.PalantirCapabilityBoundary
palantirCapabilityBoundary =
  PalantirCapability.canonicalPalantirCapabilityBoundary

antiPanopticonBoundary :
  Panopticon.AntiPanopticonBoundary
antiPanopticonBoundary =
  Panopticon.canonicalAntiPanopticonBoundary

data SecurityProcurementCreatesSurveillanceAuthority : Set where
data DataIntegrationCapabilityCreatesGodsEyeTruth : Set where
data AuditLoggingCreatesSubjectContestability : Set where
data GovernmentContractProvesAbuse : Set where
data GovernmentContractProvesNeutrality : Set where

securityProcurementDoesNotCreateAuthority :
  SecurityProcurementCreatesSurveillanceAuthority → ⊥
securityProcurementDoesNotCreateAuthority ()

dataIntegrationDoesNotCreateGodsEyeTruth :
  DataIntegrationCapabilityCreatesGodsEyeTruth → ⊥
dataIntegrationDoesNotCreateGodsEyeTruth ()

auditLoggingDoesNotCreateSubjectContestability :
  AuditLoggingCreatesSubjectContestability → ⊥
auditLoggingDoesNotCreateSubjectContestability ()

contractDoesNotProveAbuse :
  GovernmentContractProvesAbuse → ⊥
contractDoesNotProveAbuse ()

contractDoesNotProveNeutrality :
  GovernmentContractProvesNeutrality → ⊥
contractDoesNotProveNeutrality ()

------------------------------------------------------------------------
-- TRUMPISM / ALIGNMENT BOUNDARY
--
-- Palantir is publicly described as Trump-aligned in contemporary reporting.
-- Hanson has separately expressed admiration/support for Trump in public
-- political rhetoric. Those two facts do NOT construct a common command,
-- procurement or ideological-control graph.
------------------------------------------------------------------------

data SharedTrumpAlignmentCreatesCoordination : Set where
data IdeologicalAffinityCreatesProcurementCausation : Set where
data SimilarSecurityVocabularyCreatesInstitutionalIdentity : Set where

sharedTrumpAlignmentDoesNotCreateCoordination :
  SharedTrumpAlignmentCreatesCoordination → ⊥
sharedTrumpAlignmentDoesNotCreateCoordination ()

affinityDoesNotCreateProcurementCause :
  IdeologicalAffinityCreatesProcurementCausation → ⊥
affinityDoesNotCreateProcurementCause ()

similarSecurityWordsDoNotCreateInstitutionalIdentity :
  SimilarSecurityVocabularyCreatesInstitutionalIdentity → ⊥
similarSecurityWordsDoNotCreateInstitutionalIdentity ()

------------------------------------------------------------------------
-- ENDPOINT
------------------------------------------------------------------------

record HansonIsraelJewishSurveillanceBoundary : Set where
  constructor hanson-israel-jewish-surveillance-boundary
  field
    jewishPoliticalPluralityRetained : Bool
    israelStateCommunityOrganisationSeparated : Bool
    hansonAJAAlignmentRecorded : Bool
    hansonMainstreamJewishCondemnationRecorded : Bool
    segalECAJHistoryRecorded : Bool
    palantirAustraliaScrutinyRecorded : Bool
    publicAffairsPolicyCaptureAutomaticallyProved : Bool
    publicAffairsPolicyCaptureAutomaticallyProvedIsFalse :
      publicAffairsPolicyCaptureAutomaticallyProved ≡ false
    unifiedJewishPositionAutomaticallyConstructed : Bool
    unifiedJewishPositionAutomaticallyConstructedIsFalse :
      unifiedJewishPositionAutomaticallyConstructed ≡ false
    universalMinorityProtectionAutomaticallyPaid : Bool
    universalMinorityProtectionAutomaticallyPaidIsFalse :
      universalMinorityProtectionAutomaticallyPaid ≡ false
    hansonSegalPalantirNetworkConstructed : Bool
    hansonSegalPalantirNetworkConstructedIsFalse :
      hansonSegalPalantirNetworkConstructed ≡ false
    panopticonAuthorityConstructedFromCapability : Bool
    panopticonAuthorityConstructedFromCapabilityIsFalse :
      panopticonAuthorityConstructedFromCapability ≡ false
    subjectContestabilityAutomaticallyInstalled : Bool
    subjectContestabilityAutomaticallyInstalledIsFalse :
      subjectContestabilityAutomaticallyInstalled ≡ false

open HansonIsraelJewishSurveillanceBoundary public

canonicalHansonIsraelJewishSurveillanceBoundary :
  HansonIsraelJewishSurveillanceBoundary
canonicalHansonIsraelJewishSurveillanceBoundary =
  hanson-israel-jewish-surveillance-boundary
    true
    true
    true
    true
    true
    true
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
