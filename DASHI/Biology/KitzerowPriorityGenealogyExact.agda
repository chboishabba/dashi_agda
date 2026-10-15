module DASHI.Biology.KitzerowPriorityGenealogyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

import DASHI.Biology.KitzerowBH4EvidenceAtlasExact as Atlas

------------------------------------------------------------------------
-- PRIORITY / CONTACT / ATTRIBUTION GENEALOGY
--
-- Four independent questions are carried explicitly:
--   A. Was a proposition public before a later work?       (priority)
--   B. Was the later actor plausibly or demonstrably exposed? (contact/access)
--   C. How specific is the scientific/structural overlap?  (scientific relation)
--   D. Is there sufficient evidence for an attribution breach? (attribution)
--
-- No projection between these coordinates is available by definition.
------------------------------------------------------------------------

data DisclosureKind : Set where
  socialPublicDisclosure : DisclosureKind
  bookPublication : DisclosureKind
  researchGatePreprint : DisclosureKind
  institutionalCommunication : DisclosureKind
  laterResearchPublication : DisclosureKind
  laterInstitutionalFramework : DisclosureKind

data VerificationLevel : Set where
  creatorTimelineClaim : VerificationLevel
  publicTimestampRecord : VerificationLevel
  primaryDocumentInspected : VerificationLevel
  publicationMetadataVerified : VerificationLevel
  independentInstitutionalRecord : VerificationLevel
  verificationOpen : VerificationLevel

data NoveltyClass : Set where
  inheritedPriorArt : NoveltyClass
  distinctiveSelection : NoveltyClass
  distinctiveOrdering : NoveltyClass
  distinctiveMechanismClaim : NoveltyClass
  laterIndependentFinding : NoveltyClass
  noveltyUnresolved : NoveltyClass

record GenealogyNode : Set where
  constructor genealogyNode
  field
    nodeId : String
    dateLabel : String
    actor : String
    work : String
    disclosureKind : DisclosureKind
    verification : VerificationLevel
    noveltyClass : NoveltyClass
    sourceLocator : String
    boundedReading : String

open GenealogyNode public

publicDisclosure2023 : GenealogyNode
publicDisclosure2023 =
  genealogyNode
    "K-P0"
    "2023-05 through 2023-11"
    "Kimberly Kitzerow"
    "public development of BH4/autism/comorbidity architecture"
    socialPublicDisclosure
    publicTimestampRecord
    distinctiveSelection
    "Kitzerow documented timeline; linked social-media records"
    "The public record claims BH4 centrality, AAAH integration, redox regulation, CSTL E/I consequences, trait clustering, and transamination links during 2023. Each individual biology component still requires subtraction of older prior art."

formalPreprint2024 : GenealogyNode
formalPreprint2024 =
  genealogyNode
    "K-P1"
    "2024-01"
    "Kimberly Kitzerow"
    "Autism & the Comorbidities Along the BH4 Pathway"
    researchGatePreprint
    publicationMetadataVerified
    distinctiveOrdering
    "ResearchGate DOI 10.13140/RG.2.2.23124.37761/1"
    "Formalizes the BH4-centered autism/comorbidity synthesis; publication metadata establishes public availability but does not establish novelty of every component."

allostaticPreprint2024 : GenealogyNode
allostaticPreprint2024 =
  genealogyNode
    "K-P2"
    "2024-08"
    "Kimberly Kitzerow"
    "The BH4 Pathway as an Allostatic Mechanism in the Pathology of Autism and Systemic Comorbidities"
    researchGatePreprint
    publicationMetadataVerified
    distinctiveMechanismClaim
    "ResearchGate publication 383021907"
    "Makes the stress-induced BH4 resource-reallocation/shunt architecture explicit across NOS, AAAH and AGMO branches."

priorArtBeforeKitzerow : GenealogyNode
priorArtBeforeKitzerow =
  genealogyNode
    "K-PA"
    "pre-2023"
    "multiple prior authors"
    "BH4/redox/NOS/AAAH/AGMO/allostasis/E-I/cellular-stress prior art"
    laterResearchPublication
    publicationMetadataVerified
    inheritedPriorArt
    "representative anchor: Eichwald et al. 2023 Antioxidants 12(5):1037 plus earlier allostasis/E-I/BH4 literature"
    "Broad BH4 stress biology and many component edges predate Kitzerow. Priority evaluation therefore concerns distinctive selection, ordering, synthesis and claimed causal architecture rather than ownership of individual biochemical facts."

stanfordContactClaim2023 : GenealogyNode
stanfordContactClaim2023 =
  genealogyNode
    "K-C1"
    "2023-11-27"
    "Stanford Neurodiversity Project-affiliated researchers / Kimberly Kitzerow"
    "request for information about Kitzerow autism framework"
    institutionalCommunication
    creatorTimelineClaim
    noveltyUnresolved
    "Kitzerow documented timeline links an email screenshot"
    "Acquired public evidence establishes that Kitzerow claims a dated outreach and supplies a linked screenshot. Until the underlying correspondence is independently inspected and participants tied to the later study, encode this as explicitContactClaim rather than verifiedPrimaryContact."

princetonComplaint2025 : GenealogyNode
princetonComplaint2025 =
  genealogyNode
    "K-C2"
    "2025-09-17"
    "Kimberly Kitzerow / Princeton research integrity office"
    "formal attribution complaint after publication"
    institutionalCommunication
    creatorTimelineClaim
    noveltyUnresolved
    "Kitzerow documented timeline"
    "Post-publication complaint establishes neither pre-publication exposure nor wrongdoing. The same timeline reports a December 2025 Princeton response finding no evidence of wrongdoing in its internal review."

record ContactEvidence : Set where
  constructor contactEvidence
  field
    contactLabel : String
    claimedStatus : Atlas.ContactStatus
    verification : VerificationLevel
    sourceLocator : String
    directlyTiesLaterAuthors : Bool
    contentOfFrameworkTransferred : Bool
    verifiedPrimaryContact : Bool

open ContactEvidence public

stanfordContactEvidence : ContactEvidence
stanfordContactEvidence =
  contactEvidence
    "Stanford 2023 outreach claimed in Kitzerow timeline"
    Atlas.explicitContactClaim
    creatorTimelineClaim
    "timeline entry 2023-11-27; linked Adobe email screenshot"
    false
    false
    false

record AttributionAssessment : Set where
  constructor attributionAssessment
  field
    assessmentId : String
    priorityEstablished : Bool
    specificOverlapEstablished : Bool
    exposureEstablished : Bool
    directCopyEvidenceEstablished : Bool
    alternativeIndependentDevelopmentPlausible : Bool
    attributionStatus : Atlas.AttributionStatus
    plagiarismProven : Bool
    plagiarismProvenIsFalse : plagiarismProven ≡ false
    explanation : String

open AttributionAssessment public

mkOpenAssessment :
  String → Bool → Bool → Bool → Bool → Bool → Atlas.AttributionStatus → String → AttributionAssessment
mkOpenAssessment ident priority overlap exposure copying independent status explanation =
  attributionAssessment ident priority overlap exposure copying independent status false refl explanation

stanfordAssessment : AttributionAssessment
stanfordAssessment =
  mkOpenAssessment
    "K-A-STANFORD"
    true true false false true Atlas.attributionConcern
    "Temporal priority and bounded circuit-level structural overlap coexist with a claimed 2023 Stanford-affiliated contact. The acquired record does not yet tie that contact to the later paper authors or establish transfer/use of the relevant mechanism."

brazilAssessment : AttributionAssessment
brazilAssessment =
  mkOpenAssessment
    "K-A-BRAZIL"
    true true false false true Atlas.attributionConcern
    "The 2025 BH4 autism systematic review is later than Kitzerow's 2023-24 public synthesis, but its evidentiary corpus largely predates that synthesis. Similarity therefore raises a chronology question without establishing derivation."

princetonAssessment : AttributionAssessment
princetonAssessment =
  mkOpenAssessment
    "K-A-PRINCETON"
    true true false false true Atlas.attributionInvestigationReported
    "Kitzerow reports a formal complaint and a later Princeton internal response finding no evidence of wrongdoing. This owner records both events without treating either party's assertion as a proof token for plagiarism or non-overlap."

naviauxAssessment : AttributionAssessment
naviauxAssessment =
  mkOpenAssessment
    "K-A-NAVIAUX"
    true true false false true Atlas.attributionConcern
    "Later structured similarity must be interpreted against Naviaux's long pre-2023 cell-danger-response lineage; both prior art and later overlap remain explicit."

------------------------------------------------------------------------
-- Non-collapse witnesses.
------------------------------------------------------------------------

record IndependentCoordinates : Set where
  constructor independentCoordinates
  field
    scientificSupportCoordinate : Atlas.ScientificSupport
    priorityCoordinate : Atlas.PriorityStatus
    contactCoordinate : Atlas.ContactStatus
    attributionCoordinate : Atlas.AttributionStatus

supportWithoutPriority : IndependentCoordinates
supportWithoutPriority =
  independentCoordinates
    Atlas.directInterventionSupport
    Atlas.priorArtBeforeKitzerow
    Atlas.noContactEvidenceAcquired
    Atlas.independentConvergence

priorityWithoutContact : IndependentCoordinates
priorityWithoutContact =
  independentCoordinates
    Atlas.structuralConvergence
    Atlas.laterThanKitzerowDisclosure
    Atlas.noContactEvidenceAcquired
    Atlas.attributionStatusUnresolved

contactWithoutPlagiarism : IndependentCoordinates
contactWithoutPlagiarism =
  independentCoordinates
    Atlas.directInterventionSupport
    Atlas.laterThanKitzerowDisclosure
    Atlas.explicitContactClaim
    Atlas.attributionConcern

record GenealogyBoundary : Set where
  constructor genealogyBoundary
  field
    priorityImpliesNovelty : Bool
    noveltyImpliesAccess : Bool
    accessImpliesUse : Bool
    useImpliesMisconduct : Bool
    structuralOverlapImpliesCopying : Bool
    plagiarismProven : Bool
    plagiarismProvenIsFalse : plagiarismProven ≡ false

canonicalGenealogyBoundary : GenealogyBoundary
canonicalGenealogyBoundary =
  genealogyBoundary false false false false false false refl

nodes : List GenealogyNode
nodes =
  priorArtBeforeKitzerow
  ∷ publicDisclosure2023
  ∷ formalPreprint2024
  ∷ allostaticPreprint2024
  ∷ stanfordContactClaim2023
  ∷ princetonComplaint2025
  ∷ []

assessments : List AttributionAssessment
assessments =
  stanfordAssessment
  ∷ brazilAssessment
  ∷ princetonAssessment
  ∷ naviauxAssessment
  ∷ []
