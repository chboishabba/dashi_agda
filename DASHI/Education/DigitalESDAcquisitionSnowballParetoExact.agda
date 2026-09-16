module DASHI.Education.DigitalESDAcquisitionSnowballParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Pareto
import DASHI.Core.NDimParetoHyperfabricExact as NDim
import DASHI.Education.DigitalInnovationESDSourceAtlas as Call

------------------------------------------------------------------------
-- DIGITAL-ESD ACQUISITION / SNOWBALL / PARETO FRONTIER
--
-- Attribution discipline:
--   * acquisition may occur out of dependency order;
--   * same-object identity, source kind, relationship and visibility survive;
--   * citation imports neither proof nor authority;
--   * downstream payment may not silently skip an unpaid dependency;
--   * contextual evidence can pay a coarse/source-role coordinate while a
--     finer same-object/context-transfer/authority coordinate remains unpaid.
------------------------------------------------------------------------

gianniniTwinTransitionSource : Attr.AttributedSource
gianniniTwinTransitionSource =
  Attr.mkDOISource
    "Stefania Giannini"
    "Bridging the green and digital transitions through education"
    "UNESCO"
    "2024"
    "10.54675/ZACQ4808"
    "https://www.unesco.org/en/articles/bridging-digital-and-green-transitions-through-education"
    Attr.institutionalSource
    "Exact 2024 UNESCO twin-transition antecedent named by the Special Issue; supports a source-bounded education/green/digital framing including possible tension, not automatic synergy or intervention effectiveness."
    Attr.publicAttribution

garciaHernandezReviewSource : Attr.AttributedSource
garciaHernandezReviewSource =
  Attr.mkDOISource
    "Alien Garcia-Hernandez; Ana Garcia-Valcarcel Munoz-Repiso; Sonia Casillas-Martin; Marcos Cabezas-Gonzalez"
    "Sustainability in Digital Education: A Systematic Review of Innovative Proposals"
    "Education Sciences 13(1), 33"
    "2023"
    "10.3390/educsci13010033"
    "https://www.mdpi.com/2227-7102/13/1/33"
    Attr.academicArticleSource
    "Systematic-review antecedent for the call's literature-concentration premise; supports the reviewed corpus distribution and reported sustainability-in-digital-education themes, not a universal intervention rule."
    Attr.publicAttribution

unescoGEMTechnologySource : Attr.AttributedSource
unescoGEMTechnologySource =
  Attr.mkNoDOISource
    "Global Education Monitoring Report Team"
    "Global Education Monitoring Report 2023: Technology in education: A tool on whose terms?"
    "UNESCO Global Education Monitoring Report"
    "2023"
    "https://gem-report-2023.unesco.org/"
    Attr.institutionalSource
    "Institutional evidence/recommendation source on relevance, equity, scalability and sustainability of education technology; does not prove any named product effective."
    Attr.publicAttribution

unescoYouthTechnologySource : Attr.AttributedSource
unescoYouthTechnologySource =
  Attr.mkNoDOISource
    "Global Education Monitoring Report Team; Restless Development; consulted youth and students"
    "Technology in education: A tool on our terms!"
    "UNESCO 2024 Youth Report"
    "2024"
    "https://www.unesco.org/gem-report/en/publication/tecnologia-en-la-educacion-una-herramienta-nuestra-medida-2024"
    Attr.institutionalSource
    "Youth-consultation source supporting learner-centred technology-governance questions and contextual appropriateness/equity/sustainability; not a substitute for Alice Brown's constitutive-agency evidence or local participant authority."
    Attr.publicAttribution

oecdDigitalLearningImpactSource : Attr.AttributedSource
oecdDigitalLearningImpactSource =
  Attr.mkDOISource
    "Sanna Forsstrom; Morten Nja; Elaine Munthe; Jose-Luis Alvarez-Galvan; Lawrence Houldsworth"
    "The impact of digital technologies on students' learning: Results from a literature review"
    "OECD Education Working Papers No. 335"
    "2025"
    "10.1787/9997e7b3-en"
    "https://www.oecd.org/en/publications/the-impact-of-digital-technologies-on-students-learning_9997e7b3-en.html"
    Attr.institutionalSource
    "Literature-review source for access-to-technology not guaranteeing educational gain and for the continuing pedagogical implementation dependency."
    Attr.publicAttribution

pinzoneEducationLCASource : Attr.AttributedSource
pinzoneEducationLCASource =
  Attr.mkDOISource
    "Marta Pinzone; Damiano Sarti; Luca Amodeo"
    "What is the environmental impact of digitally enhanced education? Findings from a life cycle assessment of educational scenarios at an Italian university"
    "The International Journal of Life Cycle Assessment"
    "2026"
    "10.1007/s11367-026-02656-7"
    "https://doi.org/10.1007/s11367-026-02656-7"
    Attr.academicArticleSource
    "Education-scenario LCA benchmark comparing face-to-face, hybrid and online higher-education scenarios; pays a contextual lifecycle-method/evidence benchmark but not the same-object footprint or universal superiority of any digital-ESD intervention."
    Attr.publicAttribution

descampsDigitalSobrietySource : Attr.AttributedSource
descampsDigitalSobrietySource =
  Attr.mkDOISource
    "Sarah Descamps; Gaetan Temperman; Bruno De Lievre"
    "Effects of two scenario approaches for digital sobriety education among higher education students"
    "International Journal of Educational Technology in Higher Education"
    "2025"
    "10.1186/s41239-025-00569-3"
    "https://doi.org/10.1186/s41239-025-00569-3"
    Attr.academicArticleSource
    "Experimental digital-sobriety education source and reflexive-sustainability comparator: digital technology can be an environmental object of inquiry, not merely a tool used to teach environmental content; does not establish a universal pedagogy or infrastructure result."
    Attr.publicAttribution

fernandoTajanParticipatoryESDSource : Attr.AttributedSource
fernandoTajanParticipatoryESDSource =
  Attr.mkDOISource
    "Alexa Ray R. Fernando; Gizelle P. Tajan"
    "Education for sustainable development (ESD) through participatory research (PR): A systematic review"
    "Journal of Cleaner Production 482, 144237"
    "2024"
    "10.1016/j.jclepro.2024.144237"
    "https://doi.org/10.1016/j.jclepro.2024.144237"
    Attr.academicArticleSource
    "Systematic-review context for participatory ESD, local knowledge, collaborative knowledge co-generation and stakeholder involvement; does not by itself establish Alice Brown's stronger constitutive epistemic-agency stages or authority for a new participant population."
    Attr.publicAttribution

colladoLongitudinalESDSource : Attr.AttributedSource
colladoLongitudinalESDSource =
  Attr.mkDOISource
    "Silvia Collado; Jose David Moreno; Jose Martin-Albo"
    "Innovation for environmental sustainability: longitudinal effects of an education for sustainable development intervention on university students' pro-environmentalism"
    "International Journal of Sustainability in Higher Education 23(6), 1277-1293"
    "2022"
    "10.1108/IJSHE-07-2021-0315"
    "https://doi.org/10.1108/IJSHE-07-2021-0315"
    Attr.academicArticleSource
    "One-year longitudinal ESD intervention benchmark for pro-environmental knowledge, norms and self-reported behaviour; not a digital-ESD, infrastructure, institutional-lock-in or seven-generation result."
    Attr.publicAttribution

aksoyZawackiRichterOERSustainabilitySource : Attr.AttributedSource
aksoyZawackiRichterOERSustainabilitySource =
  Attr.mkDOISource
    "Dilara Arzugul Aksoy; Olaf Zawacki-Richter"
    "Factors affecting the sustainability of open educational resource initiatives in higher education: A systematic review"
    "Review of Education 13(1), e70029"
    "2025"
    "10.1002/rev3.70029"
    "https://doi.org/10.1002/rev3.70029"
    Attr.academicArticleSource
    "Systematic-review source for organisational and practice sustainability of OER initiatives across platform, creator, learner, material and institutional contexts; organisational durability does not pay material repairability, hardware longevity or infrastructure interoperability."
    Attr.publicAttribution

brasslerOERESDStudentProducerSource : Attr.AttributedSource
brasslerOERESDStudentProducerSource =
  Attr.mkDOISource
    "Mirjam Brassler"
    "Students' Digital Competence Development in the Production of Open Educational Resources in Education for Sustainable Development"
    "Sustainability 16(4), 1674"
    "2024"
    "10.3390/su16041674"
    "https://doi.org/10.3390/su16041674"
    Attr.academicArticleSource
    "Higher-education ESD/OER source in which students produce open resources and digital competence is evaluated; supports an open-practice/student-producer precedent, not constitutive authority, material sustainability or universal transfer."
    Attr.publicAttribution

ieaEnergyAISource : Attr.AttributedSource
ieaEnergyAISource =
  Attr.mkNoDOISource
    "International Energy Agency"
    "Energy and AI"
    "IEA"
    "2025"
    "https://www.iea.org/reports/energy-and-ai"
    Attr.institutionalSource
    "Energy-system source for data-centre and AI electricity demand, supply, emissions, security and affordability; general infrastructure evidence only, not education-specific lifecycle evidence."
    Attr.publicAttribution

ieaKeyQuestionsEnergyAISource : Attr.AttributedSource
ieaKeyQuestionsEnergyAISource =
  Attr.mkNoDOISource
    "International Energy Agency"
    "Key Questions on Energy and AI"
    "IEA"
    "2026"
    "https://www.iea.org/reports/key-questions-on-energy-and-ai"
    Attr.institutionalSource
    "Current update on AI/data-centre electricity demand, efficiency and system bottlenecks; retained as infrastructure context and not promoted into an intervention-level education footprint."
    Attr.publicAttribution

ituGlobalEwasteSource : Attr.AttributedSource
ituGlobalEwasteSource =
  Attr.mkNoDOISource
    "ITU; UNITAR SCYCLE Programme; Fondation Carmignac"
    "Global E-waste Monitor 2024"
    "International Telecommunication Union"
    "2024"
    "https://www.itu.int/en/ITU-D/Environment/Pages/Publications/The-Global-E-waste-Monitor-2024.aspx"
    Attr.institutionalSource
    "Global electronics/e-waste stock-flow and policy context; not an education-specific device-replacement or procurement lifecycle estimate."
    Attr.publicAttribution

unescoSixPillarsSource : Attr.AttributedSource
unescoSixPillarsSource =
  Attr.mkNoDOISource
    "UNESCO"
    "The Six Pillars Framework"
    "Digital Transformation Collaborative Financing Toolkit"
    "undated web toolkit; acquired 2026-09-16"
    "https://www.unesco.org/en/dtc-financing-toolkit/six-pillars"
    Attr.institutionalSource
    "Planning/toolkit source for total cost of ownership across technology lifecycles and environmentally sustainable digital-education financing; not an empirical lifecycle inventory."
    Attr.publicAttribution

canonicalDigitalESDAcquisitionSourceAtlas : Attr.AttributedSourceAtlas
canonicalDigitalESDAcquisitionSourceAtlas =
  Attr.mkSourceAtlas
    "digital ESD acquisition snowball source atlas"
    "DASHI.Education.DigitalESDAcquisitionSnowballParetoExact"
    ( Call.mdpiDigitalInnovationESDCall
    ∷ gianniniTwinTransitionSource
    ∷ garciaHernandezReviewSource
    ∷ unescoGEMTechnologySource
    ∷ unescoYouthTechnologySource
    ∷ oecdDigitalLearningImpactSource
    ∷ pinzoneEducationLCASource
    ∷ descampsDigitalSobrietySource
    ∷ fernandoTajanParticipatoryESDSource
    ∷ colladoLongitudinalESDSource
    ∷ aksoyZawackiRichterOERSustainabilitySource
    ∷ brasslerOERESDStudentProducerSource
    ∷ ieaEnergyAISource
    ∷ ieaKeyQuestionsEnergyAISource
    ∷ ituGlobalEwasteSource
    ∷ unescoSixPillarsSource
    ∷ []
    )
    "Exact call antecedents plus pedagogical, participatory, learner-centred, longitudinal, OER/open-practice, education-LCA, digital-sobriety and infrastructure sustainability context. Contextual payments retain scope and do not erase finer same-object, transfer, material or authority residuals."

------------------------------------------------------------------------
-- Source-role snowball receipts. These reuse the canonical owner directly.
------------------------------------------------------------------------

gianniniSourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt gianniniTwinTransitionSource
gianniniSourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt gianniniTwinTransitionSource

reviewSourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt garciaHernandezReviewSource
reviewSourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt garciaHernandezReviewSource

oecdSourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt oecdDigitalLearningImpactSource
oecdSourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt oecdDigitalLearningImpactSource

pinzoneSourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt pinzoneEducationLCASource
pinzoneSourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt pinzoneEducationLCASource

descampsSourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt descampsDigitalSobrietySource
descampsSourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt descampsDigitalSobrietySource

participatoryESDSourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt fernandoTajanParticipatoryESDSource
participatoryESDSourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt fernandoTajanParticipatoryESDSource

longitudinalESDSourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt colladoLongitudinalESDSource
longitudinalESDSourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt colladoLongitudinalESDSource

oerSustainabilitySourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt aksoyZawackiRichterOERSustainabilitySource
oerSustainabilitySourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt aksoyZawackiRichterOERSustainabilitySource

oerESDStudentProducerSourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt brasslerOERESDStudentProducerSource
oerESDStudentProducerSourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt brasslerOERESDStudentProducerSource

ieaSourceRoleReceipt : Snowball.SourceRoleSnowballReceipt ieaEnergyAISource
ieaSourceRoleReceipt = Snowball.canonicalSourceRoleSnowballReceipt ieaEnergyAISource

ituSourceRoleReceipt : Snowball.SourceRoleSnowballReceipt ituGlobalEwasteSource
ituSourceRoleReceipt = Snowball.canonicalSourceRoleSnowballReceipt ituGlobalEwasteSource

------------------------------------------------------------------------
-- Acquisition state. Paid here means exactly the named contextual coordinate,
-- never the stronger downstream consumer claim.
------------------------------------------------------------------------

record DigitalESDAcquisitionAtlas : Set where
  constructor digital-esd-acquisition-atlas
  field
    attributedSources : Attr.AttributedSourceAtlas
    unescoTwinTransitionExactObjectPaid : Bool
    unescoTwinTransitionExactObjectPaidIsTrue :
      unescoTwinTransitionExactObjectPaid ≡ true
    systematicReviewExactObjectPaid : Bool
    systematicReviewExactObjectPaidIsTrue :
      systematicReviewExactObjectPaid ≡ true
    pedagogicalAccessNonSufficiencySourcePaid : Bool
    pedagogicalAccessNonSufficiencySourcePaidIsTrue :
      pedagogicalAccessNonSufficiencySourcePaid ≡ true
    learnerCentredInstitutionalSourcePaid : Bool
    learnerCentredInstitutionalSourcePaidIsTrue :
      learnerCentredInstitutionalSourcePaid ≡ true
    educationScenarioLCABenchmarkPaid : Bool
    educationScenarioLCABenchmarkPaidIsTrue :
      educationScenarioLCABenchmarkPaid ≡ true
    digitalSobrietyPedagogySourcePaid : Bool
    digitalSobrietyPedagogySourcePaidIsTrue :
      digitalSobrietyPedagogySourcePaid ≡ true
    participatoryESDResearchContextPaid : Bool
    participatoryESDResearchContextPaidIsTrue :
      participatoryESDResearchContextPaid ≡ true
    longitudinalESDBenchmarkPaid : Bool
    longitudinalESDBenchmarkPaidIsTrue :
      longitudinalESDBenchmarkPaid ≡ true
    oerOrganisationalSustainabilityReviewPaid : Bool
    oerOrganisationalSustainabilityReviewPaidIsTrue :
      oerOrganisationalSustainabilityReviewPaid ≡ true
    oerESDStudentProducerEvidencePaid : Bool
    oerESDStudentProducerEvidencePaidIsTrue :
      oerESDStudentProducerEvidencePaid ≡ true
    generalDataCentreEnergyContextPaid : Bool
    generalDataCentreEnergyContextPaidIsTrue :
      generalDataCentreEnergyContextPaid ≡ true
    generalEwasteContextPaid : Bool
    generalEwasteContextPaidIsTrue : generalEwasteContextPaid ≡ true
    totalCostOfOwnershipLifecyclePlanningSourcePaid : Bool
    totalCostOfOwnershipLifecyclePlanningSourcePaidIsTrue :
      totalCostOfOwnershipLifecyclePlanningSourcePaid ≡ true
    ieaEnergyEvidenceIsEducationSpecific : Bool
    ieaEnergyEvidenceIsEducationSpecificIsFalse :
      ieaEnergyEvidenceIsEducationSpecific ≡ false
    ituEwasteEvidenceIsEducationSpecific : Bool
    ituEwasteEvidenceIsEducationSpecificIsFalse :
      ituEwasteEvidenceIsEducationSpecific ≡ false
    sourceRolesSnowball : Bool
    sourceRolesSnowballIsTrue : sourceRolesSnowball ≡ true
    citationCreatesProof : Bool
    citationCreatesProofIsFalse : citationCreatesProof ≡ false
    citationCreatesAuthority : Bool
    citationCreatesAuthorityIsFalse : citationCreatesAuthority ≡ false

open DigitalESDAcquisitionAtlas public

canonicalDigitalESDAcquisitionAtlas : DigitalESDAcquisitionAtlas
canonicalDigitalESDAcquisitionAtlas =
  digital-esd-acquisition-atlas
    canonicalDigitalESDAcquisitionSourceAtlas
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl

data CitationPromotesDigitalESDConclusion : Set where

citationDoesNotPromoteDigitalESDConclusion :
  CitationPromotesDigitalESDConclusion → ⊥
citationDoesNotPromoteDigitalESDConclusion ()

data TeachingSustainabilityWithTechnologyPromotesSustainabilityOfTechnology : Set where

teachingSustainabilityWithTechnologyDoesNotPromoteSustainabilityOfTechnology :
  TeachingSustainabilityWithTechnologyPromotesSustainabilityOfTechnology → ⊥
teachingSustainabilityWithTechnologyDoesNotPromoteSustainabilityOfTechnology ()

data OneEducationLCAEstablishesUniversalOnlineSuperiority : Set where

oneEducationLCADoesNotEstablishUniversalOnlineSuperiority :
  OneEducationLCAEstablishesUniversalOnlineSuperiority → ⊥
oneEducationLCADoesNotEstablishUniversalOnlineSuperiority ()

data ParticipatoryESDPromotesConstitutiveEpistemicAuthority : Set where

participatoryESDDoesNotPromoteConstitutiveEpistemicAuthority :
  ParticipatoryESDPromotesConstitutiveEpistemicAuthority → ⊥
participatoryESDDoesNotPromoteConstitutiveEpistemicAuthority ()

data OneYearESDResultPaysDigitalESDLongHorizonImpact : Set where

oneYearESDResultDoesNotPayDigitalESDLongHorizonImpact :
  OneYearESDResultPaysDigitalESDLongHorizonImpact → ⊥
oneYearESDResultDoesNotPayDigitalESDLongHorizonImpact ()

data OEROrganisationalSustainabilityPaysMaterialRepairability : Set where

oerOrganisationalSustainabilityDoesNotPayMaterialRepairability :
  OEROrganisationalSustainabilityPaysMaterialRepairability → ⊥
oerOrganisationalSustainabilityDoesNotPayMaterialRepairability ()

------------------------------------------------------------------------
-- Bidi acquisition leaves: evidence -> bounded claim; consumer -> reopen debt.
------------------------------------------------------------------------

data AcquisitionLeaf : Set where
  exactCallAntecedentIdentity : AcquisitionLeaf
  pedagogicalNonSufficiencyContext : AcquisitionLeaf
  genericInfrastructureExternalityContext : AcquisitionLeaf
  educationSpecificLifecycleMeasurement : AcquisitionLeaf
  longitudinalInterventionImpact : AcquisitionLeaf
  esdParticipantGovernanceTransfer : AcquisitionLeaf
  openInteroperabilityDurability : AcquisitionLeaf

leafReference : AcquisitionLeaf → String
leafReference exactCallAntecedentIdentity =
  "exact UNESCO-2024 twin-transition paper plus exact 2023 systematic-review antecedent"
leafReference pedagogicalNonSufficiencyContext =
  "UNESCO GEM + OECD digital-learning literature: technology/access alone is not sufficient"
leafReference genericInfrastructureExternalityContext =
  "IEA energy/AI + ITU e-waste + UNESCO lifecycle/TCO planning context"
leafReference educationSpecificLifecycleMeasurement =
  "Pinzone/Sarti/Amodeo education-scenario LCA benchmark plus still-unpaid same-object device/network/cloud/data-centre lifecycle inventory for the actual intervention"
leafReference longitudinalInterventionImpact =
  "Collado/Moreno/Martin-Albo one-year ESD benchmark plus still-unpaid digital-ESD/institutional/long-horizon outcome carrier"
leafReference esdParticipantGovernanceTransfer =
  "Fernando/Tajan participatory-ESD review plus still-unpaid context-generalised Alice constitutive-agency/authority transfer"
leafReference openInteroperabilityDurability =
  "Aksoy/Zawacki-Richter OER organisational-sustainability review + Brassler student-producer OER/ESD precedent; material repairability/interoperability/lifecycle durability remains unpaid"

data PaymentState : Set where
  unpaid : PaymentState
  sourceRolePaid : PaymentState
  exactSameObjectPaid : PaymentState
  contextTransferPaid : PaymentState

paymentState : AcquisitionLeaf → PaymentState
paymentState exactCallAntecedentIdentity = exactSameObjectPaid
paymentState pedagogicalNonSufficiencyContext = sourceRolePaid
paymentState genericInfrastructureExternalityContext = sourceRolePaid
paymentState educationSpecificLifecycleMeasurement = unpaid
paymentState longitudinalInterventionImpact = unpaid
paymentState esdParticipantGovernanceTransfer = unpaid
paymentState openInteroperabilityDurability = unpaid

record AcquisitionBidiReceipt : Set where
  constructor acquisition-bidi-receipt
  field
    leaf : AcquisitionLeaf
    forwardEvidenceReference : String
    forwardBoundedClaimReference : String
    reverseDependencyReference : String
    sourceIdentityRetained : Bool
    sourceRoleRetained : Bool
    sameObjectStatusRetained : Bool
    acquisitionMayOccurBeforePayment : Bool
    paymentMaySkipUnpaidDependency : Bool
    citationCreatesAuthority : Bool

open AcquisitionBidiReceipt public

lifecycleMeasurementBidi : AcquisitionBidiReceipt
lifecycleMeasurementBidi =
  acquisition-bidi-receipt
    educationSpecificLifecycleMeasurement
    "Pinzone/Sarti/Amodeo pays a standardized higher-education scenario-LCA benchmark; IEA/ITU/UNESCO pay broader energy/e-waste/TCO context"
    "digital education has measurable material, transport, electricity, device, streaming/recording and AI-sensitive lifecycle coordinates whose relative importance depends on scenario and context"
    "the proposed Alice/digital-ESD intervention remains unpaid as a same-object lifecycle object; reopen before turning benchmark scenario results into its footprint or into universal online-vs-face-to-face superiority"
    true true true true false false

longitudinalImpactBidi : AcquisitionBidiReceipt
longitudinalImpactBidi =
  acquisition-bidi-receipt
    longitudinalInterventionImpact
    "Collado/Moreno/Martin-Albo pays a one-year ESD intervention/follow-up precedent; the Special Issue asks for longer-term digital/transformative conditions and impacts"
    "longitudinal ESD effects are empirically measurable and can persist beyond an intervention in at least the studied context"
    "reopen digital-ESD/institutional/long-horizon claims: one ESD intervention and one-year self-reported outcomes do not identify digital infrastructure durability, transfer, institutional memory, or future-option effects"
    true true true true false false

participantGovernanceBidi : AcquisitionBidiReceipt
participantGovernanceBidi =
  acquisition-bidi-receipt
    esdParticipantGovernanceTransfer
    "Fernando/Tajan pays participatory-ESD/local-knowledge/stakeholder context; UNESCO youth consultation and canonical Alice Brown machinery remain separately attributed"
    "participatory research and collaborative knowledge co-generation are established ESD practices in the reviewed literature"
    "reopen context/authority transfer before promoting participation into Alice's question/coding/co-interpretation/co-design/evidence-return stages or assigning authority to a new population"
    true true true true false false

openDurabilityBidi : AcquisitionBidiReceipt
openDurabilityBidi =
  acquisition-bidi-receipt
    openInteroperabilityDurability
    "Aksoy/Zawacki-Richter pays an OER initiative-sustainability review and Brassler pays a student-producer OER/HESD precedent"
    "open-resource sustainability depends on multiple institutional/platform/creator/learner/material factors, and students can co-produce OERs in HESD"
    "reopen before claiming source availability, licensing or OER organisational sustainability pays hardware repairability, interoperability, energy/material lifecycle durability or durable governance of the actual digital-ESD system"
    true true true true false false

------------------------------------------------------------------------
-- N-dimensional Pareto specialization. Lower ordinal = lower declared debt.
-- These are planning coordinates, never truth, probability, prestige or value.
------------------------------------------------------------------------

data FrontierAxis : Set where
  sourceDependencyDebt : FrontierAxis
  consumerSpecificityDebt : FrontierAxis
  sustainabilityCoverageDebt : FrontierAxis
  authorityPromotionRisk : FrontierAxis
  opportunityLoss : FrontierAxis
  acquisitionEffort : FrontierAxis

axisReference : FrontierAxis → String
axisReference sourceDependencyDebt = "unpaid source/dependency identity and role debt"
axisReference consumerSpecificityDebt = "distance from the paper's actual education/intervention consumer"
axisReference sustainabilityCoverageDebt = "unpaid environmental/social/economic/epistemic/temporal coordinates"
axisReference authorityPromotionRisk = "risk of promoting context, citation or consultation beyond source authority"
axisReference opportunityLoss = "scientific leverage lost if this leaf is deferred"
axisReference acquisitionEffort = "relative evidence acquisition / integration effort"

leafCost : FrontierAxis → AcquisitionLeaf → Nat
leafCost sourceDependencyDebt exactCallAntecedentIdentity = 0
leafCost sourceDependencyDebt pedagogicalNonSufficiencyContext = 0
leafCost sourceDependencyDebt genericInfrastructureExternalityContext = 0
leafCost sourceDependencyDebt educationSpecificLifecycleMeasurement = 1
leafCost sourceDependencyDebt longitudinalInterventionImpact = 1
leafCost sourceDependencyDebt esdParticipantGovernanceTransfer = 1
leafCost sourceDependencyDebt openInteroperabilityDurability = 1

leafCost consumerSpecificityDebt exactCallAntecedentIdentity = 1
leafCost consumerSpecificityDebt pedagogicalNonSufficiencyContext = 1
leafCost consumerSpecificityDebt genericInfrastructureExternalityContext = 3
leafCost consumerSpecificityDebt educationSpecificLifecycleMeasurement = 0
leafCost consumerSpecificityDebt longitudinalInterventionImpact = 1
leafCost consumerSpecificityDebt esdParticipantGovernanceTransfer = 1
leafCost consumerSpecificityDebt openInteroperabilityDurability = 2

leafCost sustainabilityCoverageDebt exactCallAntecedentIdentity = 3
leafCost sustainabilityCoverageDebt pedagogicalNonSufficiencyContext = 3
leafCost sustainabilityCoverageDebt genericInfrastructureExternalityContext = 1
leafCost sustainabilityCoverageDebt educationSpecificLifecycleMeasurement = 0
leafCost sustainabilityCoverageDebt longitudinalInterventionImpact = 1
leafCost sustainabilityCoverageDebt esdParticipantGovernanceTransfer = 1
leafCost sustainabilityCoverageDebt openInteroperabilityDurability = 1

leafCost authorityPromotionRisk exactCallAntecedentIdentity = 0
leafCost authorityPromotionRisk pedagogicalNonSufficiencyContext = 0
leafCost authorityPromotionRisk genericInfrastructureExternalityContext = 2
leafCost authorityPromotionRisk educationSpecificLifecycleMeasurement = 1
leafCost authorityPromotionRisk longitudinalInterventionImpact = 1
leafCost authorityPromotionRisk esdParticipantGovernanceTransfer = 4
leafCost authorityPromotionRisk openInteroperabilityDurability = 2

leafCost opportunityLoss exactCallAntecedentIdentity = 4
leafCost opportunityLoss pedagogicalNonSufficiencyContext = 3
leafCost opportunityLoss genericInfrastructureExternalityContext = 2
leafCost opportunityLoss educationSpecificLifecycleMeasurement = 0
leafCost opportunityLoss longitudinalInterventionImpact = 1
leafCost opportunityLoss esdParticipantGovernanceTransfer = 1
leafCost opportunityLoss openInteroperabilityDurability = 2

leafCost acquisitionEffort exactCallAntecedentIdentity = 0
leafCost acquisitionEffort pedagogicalNonSufficiencyContext = 0
leafCost acquisitionEffort genericInfrastructureExternalityContext = 0
leafCost acquisitionEffort educationSpecificLifecycleMeasurement = 3
leafCost acquisitionEffort longitudinalInterventionImpact = 3
leafCost acquisitionEffort esdParticipantGovernanceTransfer = 2
leafCost acquisitionEffort openInteroperabilityDurability = 2

frontierProblem : Pareto.ConsumerMDLProblem
frontierProblem =
  Pareto.consumerMDLProblem
    AcquisitionLeaf
    (λ _ → ⊤)
    (λ _ → ⊤)
    (leafCost acquisitionEffort)
    _≡_
    leafReference
    "application-declared acquisition axes; no weighted truth/prestige/authority score"
    "inspect non-dominated unpaid evidence leaves before promoting digital-ESD conclusions"

frontierCosts : Pareto.CostHyperfabric frontierProblem
frontierCosts = Pareto.costHyperfabric FrontierAxis leafCost axisReference

frontierView : NDim.NDimParetoView frontierCosts
frontierView =
  NDim.ndimParetoView
    6
    "six source/debt/scope/risk/opportunity/effort axes"
    axisReference
    true
    "retain multiple non-dominated acquisition leaves; execution order is consumer-relative"

-- Coarse/contextual payments remain in provenance history while the finer
-- same-object/context-transfer/material-authority residuals stay live.
currentAcquisitionFrontier : List AcquisitionLeaf
currentAcquisitionFrontier =
  educationSpecificLifecycleMeasurement
  ∷ longitudinalInterventionImpact
  ∷ esdParticipantGovernanceTransfer
  ∷ openInteroperabilityDurability
  ∷ []

firstAcquisitionLeaf : AcquisitionLeaf
firstAcquisitionLeaf = educationSpecificLifecycleMeasurement

parallelAcquisitionLeaf : AcquisitionLeaf
parallelAcquisitionLeaf = esdParticipantGovernanceTransfer

record SnowballParetoBoundary : Set where
  constructor snowball-pareto-boundary
  field
    acquisitionOrderEqualsPaymentOrder : Bool
    citationCreatesProof : Bool
    citationCreatesAuthority : Bool
    genericInfrastructureEvidenceEqualsEducationInterventionLCA : Bool
    consultationEqualsConstitutiveParticipantAuthority : Bool
    oneScenarioLCAEstablishesUniversalOrdering : Bool
    sustainabilityTeachingImpliesSustainableTechnology : Bool
    participatoryContextCreatesParticipantAuthority : Bool
    oneYearESDClosesDigitalLongHorizonImpact : Bool
    oerOrganisationalDurabilityEqualsMaterialDurability : Bool
    paretoRequiresScalarScore : Bool
    lowestAcquisitionEffortAutomaticallyWins : Bool
    paidLeafMustStayOnUnpaidFrontier : Bool
    multipleNonDominatedLeavesMayRemainLive : Bool
    unpaidDependencyMayReopenDownstreamClaim : Bool

open SnowballParetoBoundary public

canonicalSnowballParetoBoundary : SnowballParetoBoundary
canonicalSnowballParetoBoundary =
  snowball-pareto-boundary
    false false false false false false false false false false false false false true true

currentHighestAlphaReading : String
currentHighestAlphaReading =
  "Exact call antecedents, pedagogical context, participatory-ESD context, a one-year ESD longitudinal benchmark, OER organisational-sustainability review, student-producer OER/HESD precedent, education-scenario LCA benchmark, digital-sobriety pedagogy, and general infrastructure context are now source-role paid. The live frontier intentionally remains four finer residuals: same-object intervention lifecycle measurement; digital-ESD/institutional long-horizon impact; context-generalised constitutive participant governance; and material/interoperability/repairability durability. Context acquisition reduces debt without silently paying these stronger consumers."
