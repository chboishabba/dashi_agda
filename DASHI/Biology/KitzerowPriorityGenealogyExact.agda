module DASHI.Biology.KitzerowPriorityGenealogyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

import DASHI.Biology.KitzerowBH4EvidenceAtlasExact as Atlas

------------------------------------------------------------------------
-- PRIORITY / CONTACT / REFERENCE / ATTRIBUTION GENEALOGY
--
-- Five independent questions are carried explicitly:
--   A. Was a proposition public before a later work?          (priority)
--   B. Was the later actor plausibly/demonstrably exposed?    (contact/access)
--   C. Does the later publication itself cite/reference it?   (publication reference)
--   D. How specific is the scientific/structural overlap?     (scientific relation)
--   E. Is there sufficient evidence for an attribution breach? (attribution)
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

data PublicationReferenceStatus : Set where
  explicitKitzerowCitation : PublicationReferenceStatus
  explicitKitzerowAcknowledgment : PublicationReferenceStatus
  kitzerowNotFoundInArticleText : PublicationReferenceStatus
  creatorReportsUncited : PublicationReferenceStatus
  publicationReferenceUnresolved : PublicationReferenceStatus

record PublicationReferenceEvidence : Set where
  constructor publicationReferenceEvidence
  field
    referenceLabel : String
    publicationReferenceStatus : PublicationReferenceStatus
    verification : VerificationLevel
    sourceLocator : String
    searchOrEvidence : String
    articleAuthorContactEstablished : Bool
    boundedReading : String

open PublicationReferenceEvidence public

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
    "Acquired public evidence establishes that Kitzerow claims a dated outreach and supplies a linked screenshot. The linked Adobe artifact could not be fetched in this acquisition environment. Until the underlying correspondence is independently inspected and participants tied to the later study, encode this as explicitContactClaim rather than verifiedPrimaryContact."

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

------------------------------------------------------------------------
-- Publication-reference evidence is deliberately separate from contact.
-- Current primary/public full-text acquisition does NOT establish that the
-- later papers themselves cite Kitzerow.  In fact, Kitzerow's Nov 2025 public
-- statement describes the Japan/Brazil/Stanford/Princeton results as uncited.
------------------------------------------------------------------------

stanford2025ReferenceEvidence : PublicationReferenceEvidence
stanford2025ReferenceEvidence =
  publicationReferenceEvidence
    "Jang/Takahashi/Huguenard 2025 Science Advances reference check"
    kitzerowNotFoundInArticleText
    primaryDocumentInspected
    "PMC12366697 / DOI 10.1126/sciadv.adw4682"
    "Full-text search acquired no match for 'Kitzerow'; separate creator timeline claims Stanford-affiliated outreach in 2023."
    false
    "No article citation was found. This does not negate the separate contact claim; it means contact and article attribution are different coordinates."

ojha2026ReferenceEvidence : PublicationReferenceEvidence
ojha2026ReferenceEvidence =
  publicationReferenceEvidence
    "Ojha et al. 2026 Molecular Psychiatry reference check"
    kitzerowNotFoundInArticleText
    primaryDocumentInspected
    "DOI 10.1038/s41380-026-03514-6"
    "Nature full-text search acquired no match for 'Kitzerow'."
    false
    "The NO-TSC2-mTOR result may supply strong bounded mechanistic convergence without being a citation of Kitzerow."

brazil2025ReferenceEvidence : PublicationReferenceEvidence
brazil2025ReferenceEvidence =
  publicationReferenceEvidence
    "Colpani Filho et al. 2025 Brain Sciences reference check"
    creatorReportsUncited
    primaryDocumentInspected
    "DOI 10.3390/brainsci15020151; Kitzerow Nov 15 2025 public statement"
    "MDPI full text contains the review's source corpus and 1967-2021 search window; no Kitzerow reference was located in this pass. Kitzerow publicly describes this and the Japan/Stanford/Princeton studies as uncited."
    false
    "The review's submission/publication chronology and conceptual overlap are provenance questions separate from article citation and from the age of its underlying evidence corpus."

creatorUncitedFour2025 : PublicationReferenceEvidence
creatorUncitedFour2025 =
  publicationReferenceEvidence
    "Kitzerow public statement that four convergent 2025 pillars remained uncited"
    creatorReportsUncited
    publicTimestampRecord
    "Change.org update dated 2025-11-15"
    "Kitzerow names Japan, Brazil, Stanford and Princeton and says none cited her work."
    false
    "This is primary evidence for what Kitzerow herself claimed about citation status, not independent proof of access or attribution breach."

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
    "timeline entry 2023-11-27; linked Adobe email screenshot (not fetchable in current acquisition environment)"
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
mkOpenAssessment ident priority hasOverlap exposure copying independent status explanation =
  attributionAssessment ident priority hasOverlap exposure copying independent status false refl explanation

stanfordAssessment : AttributionAssessment
stanfordAssessment =
  mkOpenAssessment
    "K-A-STANFORD"
    true true false false true Atlas.attributionConcern
    "Temporal priority and bounded circuit-level structural overlap coexist with a claimed 2023 Stanford-affiliated contact. The later paper itself does not contain a Kitzerow citation in the acquired full text. The acquired record does not yet tie the 2023 contact to the later paper authors or establish transfer/use of the relevant mechanism."

brazilAssessment : AttributionAssessment
brazilAssessment =
  mkOpenAssessment
    "K-A-BRAZIL"
    true true false false true Atlas.attributionConcern
    "The 2025 BH4 autism systematic review is later than Kitzerow's 2023-24 public synthesis, but its evidentiary corpus covers 1967-2021 and its analysis was conducted 2020-2021. Similarity therefore raises a synthesis-chronology question without establishing derivation."

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

open IndependentCoordinates public

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
    contactImpliesArticleCitation : Bool
    articleCitationImpliesDerivation : Bool
    useImpliesMisconduct : Bool
    structuralOverlapImpliesCopying : Bool
    plagiarismProven : Bool
    plagiarismProvenIsFalse : plagiarismProven ≡ false

canonicalGenealogyBoundary : GenealogyBoundary
canonicalGenealogyBoundary =
  genealogyBoundary false false false false false false false false refl

nodes : List GenealogyNode
nodes =
  priorArtBeforeKitzerow
  ∷ publicDisclosure2023
  ∷ formalPreprint2024
  ∷ allostaticPreprint2024
  ∷ stanfordContactClaim2023
  ∷ princetonComplaint2025
  ∷ []

referenceEvidence : List PublicationReferenceEvidence
referenceEvidence =
  stanford2025ReferenceEvidence
  ∷ ojha2026ReferenceEvidence
  ∷ brazil2025ReferenceEvidence
  ∷ creatorUncitedFour2025
  ∷ []

assessments : List AttributionAssessment
assessments =
  stanfordAssessment
  ∷ brazilAssessment
  ∷ princetonAssessment
  ∷ naviauxAssessment
  ∷ []
