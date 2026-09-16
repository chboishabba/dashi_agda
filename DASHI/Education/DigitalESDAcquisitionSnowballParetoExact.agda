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
--   * external infrastructure evidence remains scope-bounded and does not
--     become an education-intervention-specific lifecycle estimate.
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
    ∷ ieaEnergyAISource
    ∷ ieaKeyQuestionsEnergyAISource
    ∷ ituGlobalEwasteSource
    ∷ unescoSixPillarsSource
    ∷ []
    )
    "Exact call antecedents plus pedagogical, learner-centred, education-LCA, digital-sobriety and infrastructure sustainability context. Source identity and role remain non-promoting; contextual benchmarks do not become a same-object intervention footprint or universal rule."

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

ieaSourceRoleReceipt : Snowball.SourceRoleSnowballReceipt ieaEnergyAISource
ieaSourceRoleReceipt = Snowball.canonicalSourceRoleSnowballReceipt ieaEnergyAISource

ituSourceRoleReceipt : Snowball.SourceRoleSnowballReceipt ituGlobalEwasteSource
ituSourceRoleReceipt = Snowball.canonicalSourceRoleSnowballReceipt ituGlobalEwasteSource

------------------------------------------------------------------------
-- Acquisition state.
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
  "longitudinal educational, inclusion, institutional and sustainability outcomes beyond short-term engagement/learning"
leafReference esdParticipantGovernanceTransfer =
  "context-generalised participant-agency/voice governance evidence specifically in ESD/digital-green settings"
leafReference openInteroperabilityDurability =
  "evidence connecting openness/interoperability/repairability/reuse/maintenance to durable educational and sustainability outcomes"

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
    "call requests stronger evidence about outcomes, conditions, scalability, institutionalisation and longer-term impact"
    "short-term engagement or learning measures cannot by themselves pay long-horizon transformative/sustainability claims"
    "reopen longitudinal outcomes whenever a downstream claim exceeds the time horizon and consumer scope of its underlying study"
    true true true true false false

participantGovernanceBidi : AcquisitionBidiReceipt
participantGovernanceBidi =
  acquisition-bidi-receipt
    esdParticipantGovernanceTransfer
    "UNESCO youth consultation plus canonical Alice Brown participant-agency machinery"
    "learner-centred governance is a live ESD design coordinate, but constitutive agency must remain context- and source-specific"
    "reopen context transfer before promoting Alice's Australian/regional education findings or UNESCO consultation framing into a universal ESD participant-authority theorem"
    true true true true false false

openDurabilityBidi : AcquisitionBidiReceipt
openDurabilityBidi =
  acquisition-bidi-receipt
    openInteroperabilityDurability
    "current discussion raises openness as a possible sustainability mechanism"
    "openness/interoperability/repairability may be acquisition targets but are not yet paid as a sustainability theorem"
    "reopen this leaf before claiming source availability, interoperability, repairability, reuse or maintenance causes durable sustainability"
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
leafCost sourceDependencyDebt longitudinalInterventionImpact = 2
leafCost sourceDependencyDebt esdParticipantGovernanceTransfer = 1
leafCost sourceDependencyDebt openInteroperabilityDurability = 2

leafCost consumerSpecificityDebt exactCallAntecedentIdentity = 1
leafCost consumerSpecificityDebt pedagogicalNonSufficiencyContext = 1
leafCost consumerSpecificityDebt genericInfrastructureExternalityContext = 3
leafCost consumerSpecificityDebt educationSpecificLifecycleMeasurement = 0
leafCost consumerSpecificityDebt longitudinalInterventionImpact = 0
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
leafCost opportunityLoss openInteroperabilityDurability = 3

leafCost acquisitionEffort exactCallAntecedentIdentity = 0
leafCost acquisitionEffort pedagogicalNonSufficiencyContext = 0
leafCost acquisitionEffort genericInfrastructureExternalityContext = 0
leafCost acquisitionEffort educationSpecificLifecycleMeasurement = 3
leafCost acquisitionEffort longitudinalInterventionImpact = 4
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

-- Paid antecedent/context leaves remain in provenance history but are removed
-- from the live unpaid frontier. The LCA benchmark reduces conceptual/method
-- debt but does not pay the same-object intervention lifecycle leaf.
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
    paretoRequiresScalarScore : Bool
    lowestAcquisitionEffortAutomaticallyWins : Bool
    paidLeafMustStayOnUnpaidFrontier : Bool
    multipleNonDominatedLeavesMayRemainLive : Bool
    unpaidDependencyMayReopenDownstreamClaim : Bool

open SnowballParetoBoundary public

canonicalSnowballParetoBoundary : SnowballParetoBoundary
canonicalSnowballParetoBoundary =
  snowball-pareto-boundary
    false false false false false false false false false false true true

currentHighestAlphaReading : String
currentHighestAlphaReading =
  "Exact Special-Issue antecedents and general pedagogical/infrastructure context are paid. An education-scenario LCA benchmark and a digital-sobriety pedagogy source are now also paid as contextual source-role evidence. The first live target remains the same-object lifecycle measurement for the proposed/governed digital-ESD intervention: a benchmark scenario cannot pay that identity. Longitudinal impact, ESD-specific participant-governance transfer, and openness/interoperability durability remain parallel non-dominated debts."
