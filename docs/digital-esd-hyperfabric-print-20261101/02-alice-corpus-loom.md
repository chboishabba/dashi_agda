# Digital-ESD hyperfabric — exact-source print, part 2 of 5

**Source ref:** `agent/digital-esd-source-crosspollination-20261101` (2026-11-01). **Role:** exact snapshot of the Alice Brown/associates educational foundation, including the nine-item attributed corpus and cross-paper relationships. Neither the corpus loom nor the juxtaposition of its sources creates a combined finding attributed to any one original author.

1. `DASHI/Biology/EducationCorpusSourceRegistry.agda` — SHA `fca3fb21bb53216c5915185782bb7cbc4c24489e`, 258 lines
2. `DASHI/Biology/CrossPaperDialecticalDevelopment.agda` — SHA `bdff1a0c862e434565d623e85ef877818e04057d`, 229 lines
3. `DASHI/Biology/OEFMultiFibreFeedbackHyperfabric.agda` — SHA `0dbdfacc91e1d193945864a0103753e8d9da06ee`, 691 lines
4. `DASHI/Biology/HumourEpistemicAgencyHyperfabricBridge.agda` — SHA `bdc7920600b0e931c86a9fc0b23bf21cceca25c6`, 419 lines
5. `DASHI/Biology/EcologyOfDataHyperfabricBridge.agda` — SHA `8ed5f46dbdbf93cdb7735cfbdbccb5764923e6ab`, 144 lines
6. `DASHI/Biology/StudentVoiceEpistemicAgencyBridge.agda` — SHA `f991f3ad5398b98bda0970493c5c54e693c98449`, 156 lines
7. `DASHI/Biology/AliceBrownCorpusLoom.agda` — SHA `e3d1a45fcaa10f441924655e9a6b867d60863b76`, 188 lines

## DASHI/Biology/EducationCorpusSourceRegistry.agda

Source: https://github.com/chboishabba/dashi_agda/blob/agent/digital-esd-source-crosspollination-20261101/DASHI/Biology/EducationCorpusSourceRegistry.agda

Blob SHA: `fca3fb21bb53216c5915185782bb7cbc4c24489e`

```agda
module DASHI.Biology.EducationCorpusSourceRegistry where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source-bound registry for the education-paper corpus.
--
-- Every row preserves title, authors, DOI, venue, year and the source-level
-- contribution.  Cross-paper and DASHI inferences are stored separately;
-- metadata does not promote any paper into universal authority.

record PaperReference : Set where
  constructor mkPaperReference
  field
    paperKey : String
    paperTitle : String
    paperAuthors : List String
    paperDOI : String
    paperJournal : String
    paperYear : Nat
    paperVolumeIssue : String
    paperPages : String
    paperSourceContribution : String
    paperSourceBoundary : String
    paperMetadataVerified : Bool
    paperMetadataVerifiedIsTrue : paperMetadataVerified ≡ true

open PaperReference public

aiFeedbackAuthors : List String
aiFeedbackAuthors =
  "Christopher Dann"
  ∷ "Petrea Redmond"
  ∷ "Melissa Fanshawe"
  ∷ "Alice Brown"
  ∷ "Seyum Getenet"
  ∷ "Thanveer Shaik"
  ∷ "Xiaohui Tao"
  ∷ "Linda Galligan"
  ∷ "Yan Li"
  ∷ []

humourFrameworkAuthors : List String
humourFrameworkAuthors =
  "Alice Brown" ∷ "Josephine Pryce" ∷ "Anja Pabel" ∷ []

voiceAgencyAuthors : List String
voiceAgencyAuthors = "Alice Brown" ∷ "Megan Kimber" ∷ []

onlineSupportAuthors : List String
onlineSupportAuthors =
  "Seyum Getenet"
  ∷ "Katie Burke"
  ∷ "Melissa Fanshawe"
  ∷ "Alice Brown"
  ∷ []

ecologyDataAuthors : List String
ecologyDataAuthors = "Roxanne Finn" ∷ "Alice Brown" ∷ []

parentalAllyshipLensAuthors : List String
parentalAllyshipLensAuthors =
  "Rachel Leslie" ∷ "Alice Brown" ∷ "Ellen Larsen" ∷ []

advocacyAllyshipAuthors : List String
advocacyAllyshipAuthors =
  "Rachel Leslie"
  ∷ "Ellen Larsen"
  ∷ "Melissa Fanshawe"
  ∷ "Alice Brown"
  ∷ []

partnershipBarriersAuthors : List String
partnershipBarriersAuthors =
  "Rachel Leslie"
  ∷ "Melissa Fanshawe"
  ∷ "Ellen Larsen"
  ∷ "Alice Brown"
  ∷ []

parentalFearIndependentMobilityAuthors : List String
parentalFearIndependentMobilityAuthors =
  "Justen O'Connor" ∷ "Alice Brown" ∷ []

aiFeedbackPaper : PaperReference
aiFeedbackPaper =
  mkPaperReference
    "ajet-oef-ai-feedback-2024"
    "Making sense of student feedback and engagement using artificial intelligence"
    aiFeedbackAuthors
    "10.14742/ajet.8903"
    "Australasian Journal of Educational Technology"
    2024
    "40(3)"
    "58-76"
    "MVP feasibility evidence that manually OEF-labelled feedback can train an NLP/deep-learning classifier and aggregate visualisation surface."
    "Classification remains a bounded proxy: not student meaning, complete voice, individual truth, equity, causal redesign effect, or pedagogical authority."
    true refl

humourFrameworkPaper : PaperReference
humourFrameworkPaper =
  mkPaperReference
    "online-humour-engagement-framework-2025"
    "Considerations for integrating humour as a strategy to heighten online student engagement and learning in higher education: An emerging framework"
    humourFrameworkAuthors
    "no DOI assigned"
    "Higher Education Research and Development Society of Australasia (HERDSA) Conference"
    2025
    "conference program"
    "64"
    "Develops an emerging seven-consideration framework for integrating humour into online higher-education teaching, including rationale, presenter, audience/context, content, technical delivery, humour type and feedback."
    "The bibliographic row anchors the HERDSA 2025 conference item. The richer seven-consideration formalisation is source-bound to the supplied manuscript/draft and is not promoted here to a claim of peer-reviewed empirical validation or student co-construction."
    true refl

voiceAgencyPaper : PaperReference
voiceAgencyPaper =
  mkPaperReference
    "student-voice-epistemic-expansion-2026"
    "Repositioning Student Voice and Agency: A Call for the Epistemic Expansion of Scholarship of Teaching and Learning Inquiry"
    voiceAgencyAuthors
    "10.1177/14697874261426374"
    "Active Learning in Higher Education"
    2026
    "27(2)"
    "253-264"
    "Critiques extractive SoTL feedback practices and calls for students to participate as domain experts and contributors to research design and scholarship praxis."
    "The paper supplies an epistemic-participation correction; it does not imply that every survey, partnership, or co-design process automatically realises agency."
    true refl

onlineSupportStrategiesPaper : PaperReference
onlineSupportStrategiesPaper =
  mkPaperReference
    "online-teacher-education-support-strategies-2026"
    "Supporting online learning in teacher education: student-identified strategies and social constructivist implications"
    onlineSupportAuthors
    "10.1080/01587919.2026.2669288"
    "Distance Education"
    2026
    "online first"
    "online first"
    "Uses 584 pre-service-teacher responses to identify five student-valued support themes: autonomy/flexibility, accessible centralised resources, meaningful interaction, self-organisation, and guided scaffolding."
    "The five themes are candidate support families in an Australian regional teacher-education context, not universal interventions or automatic causal effects."
    true refl

ecologyOfDataPaper : PaperReference
ecologyOfDataPaper =
  mkPaperReference
    "ecology-of-data-custodianship-2025"
    "Custodians of an ecology of data: Foundational theory and practice for data analysis in a complex world"
    ecologyDataAuthors
    "10.1177/14687941241234293"
    "Qualitative Research"
    2025
    "25(1)"
    "110-129"
    "Develops an eco-behavioural, person-place co-constituted account of qualitative analysis through five responsibilities of data custodianship."
    "Custodianship is a methodological and ethical stance; it does not make contextual interpretation infallible or eliminate the need for reflexivity and evidence."
    true refl

parentalAllyshipLensPaper : PaperReference
parentalAllyshipLensPaper =
  mkPaperReference
    "parental-allyship-conceptual-lens-2025"
    "Parental Allyship for Children With Dyslexia: A Conceptual Lens on Disability Experience"
    parentalAllyshipLensAuthors
    "10.1177/07319487241251730"
    "Learning Disability Quarterly"
    2025
    "48(1)"
    "3-12"
    "Extends disability-experience analysis to parent allies through primary, vicarious, and primary-adjacent proximity to a child's dyslexic identity."
    "Parent allyship is not identical to the child's voice, identity, or lived disability experience and cannot replace the child's epistemic position."
    true refl

advocacyAllyshipPaper : PaperReference
advocacyAllyshipPaper =
  mkPaperReference
    "advocacy-allyship-distinction-2024"
    "It is more than the average parent goes through: using the experiences of Australian parents of dyslexic children to draw a distinction between advocacy and allyship"
    advocacyAllyshipAuthors
    "10.1080/19404158.2024.2342523"
    "Australian Journal of Learning Difficulties"
    2024
    "29(1)"
    "53-74"
    "Uses interviews with ten Australian parents to distinguish parental allyship from ordinary parental advocacy and describe additional responsibilities and disability-adjacent experience."
    "The qualitative sample supports situated conceptual development, not prevalence, universal parent experience, or substitution of parent testimony for child testimony."
    true refl

partnershipBarriersPaper : PaperReference
partnershipBarriersPaper =
  mkPaperReference
    "dyslexia-parent-school-partnership-barriers-2025"
    "The Perceptions Parents of Dyslexic Children Have on Barriers to Meaningful Parent-School Partnerships in Australia"
    partnershipBarriersAuthors
    "10.1080/09362835.2024.2389081"
    "Exceptionality"
    2025
    "33(1)"
    "40-58"
    "Reports parent-perceived interpersonal and systemic barriers, including rejection of parent expertise, in parent-school partnerships for dyslexic children."
    "Parent perceptions are valid situated observer surfaces but do not alone establish every participant's state, institutional intent, or universal school-system behaviour."
    true refl

parentalFearIndependentMobilityPaper : PaperReference
parentalFearIndependentMobilityPaper =
  mkPaperReference
    "parental-fear-independent-mobility-2013"
    "A qualitative study of 'fear' as a regulator of children's independent physical activity in the suburbs"
    parentalFearIndependentMobilityAuthors
    "10.1016/j.healthplace.2013.09.002"
    "Health & Place"
    2013
    "24"
    "157-164"
    "Uses interviews with 24 parents and Tudor's parameters-of-fear framework to show IAST fear as a situated, repeated negotiation among environmental, cultural, social, bodily, personality and biographical factors, alongside perceived benefits and child independence."
    "The evidence is context-bound qualitative parent testimony from one white middle-class suburban Australian setting. It does not establish population prevalence, a universal causal fear model, or the child's own voice."
    true refl

canonicalEducationCorpusPapers : List PaperReference
canonicalEducationCorpusPapers =
  aiFeedbackPaper
  ∷ humourFrameworkPaper
  ∷ voiceAgencyPaper
  ∷ onlineSupportStrategiesPaper
  ∷ ecologyOfDataPaper
  ∷ parentalAllyshipLensPaper
  ∷ advocacyAllyshipPaper
  ∷ partnershipBarriersPaper
  ∷ parentalFearIndependentMobilityPaper
  ∷ []

record EducationCorpusSourceRegistry : Set where
  constructor mkEducationCorpusSourceRegistry
  field
    papers : List PaperReference
    papersAreCanonical : papers ≡ canonicalEducationCorpusPapers
    sourceClaimsSeparatedFromDashiInference : Bool
    sourceClaimsSeparatedFromDashiInferenceIsTrue :
      sourceClaimsSeparatedFromDashiInference ≡ true
    metadataDoesNotConferAuthority : Bool
    metadataDoesNotConferAuthorityIsTrue :
      metadataDoesNotConferAuthority ≡ true
    reading : String

open EducationCorpusSourceRegistry public

canonicalEducationCorpusSourceRegistry : EducationCorpusSourceRegistry
canonicalEducationCorpusSourceRegistry =
  mkEducationCorpusSourceRegistry
    canonicalEducationCorpusPapers refl
    true refl
    true refl
    "Nine source-bound papers/items are retained with title, author, DOI-or-explicit-no-DOI, venue and boundary metadata. Paper claims, cross-paper inferences, and DASHI extensions remain distinct promotion levels."
```

## DASHI/Biology/CrossPaperDialecticalDevelopment.agda

Source: https://github.com/chboishabba/dashi_agda/blob/agent/digital-esd-source-crosspollination-20261101/DASHI/Biology/CrossPaperDialecticalDevelopment.agda

Blob SHA: `bdff1a0c862e434565d623e85ef877818e04057d`

```agda
module DASHI.Biology.CrossPaperDialecticalDevelopment where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.EducationCorpusSourceRegistry as Sources

------------------------------------------------------------------------
-- Cross-paper developmental relation.
--
-- A source paper, a cross-paper inference and a DASHI extension remain
-- distinct claim registers.  The sequence below is a corpus-level synthesis,
-- not a claim that any one paper states the entire programme.

data ClaimRegister : Set where
  sourcePaperClaim : ClaimRegister
  crossPaperInference : ClaimRegister
  dashiFormalExtension : ClaimRegister
  empiricalFollowUpHypothesis : ClaimRegister


data DevelopmentStage : Set where
  engagementFibreStage : DevelopmentStage
  scalableFeedbackClassificationStage : DevelopmentStage
  teacherDesignedHumourFrameworkStage : DevelopmentStage
  ecologicalContextRestorationStage : DevelopmentStage
  epistemicAgencyRedistributionStage : DevelopmentStage
  studentIdentifiedSupportStage : DevelopmentStage
  multiObserverAllyshipStage : DevelopmentStage
  coDesignedEnactmentStage : DevelopmentStage
  evidenceReturnRechartingStage : DevelopmentStage

canonicalDevelopmentStages : List DevelopmentStage
canonicalDevelopmentStages =
  engagementFibreStage
  ∷ scalableFeedbackClassificationStage
  ∷ teacherDesignedHumourFrameworkStage
  ∷ ecologicalContextRestorationStage
  ∷ epistemicAgencyRedistributionStage
  ∷ studentIdentifiedSupportStage
  ∷ multiObserverAllyshipStage
  ∷ coDesignedEnactmentStage
  ∷ evidenceReturnRechartingStage
  ∷ []

stageName : DevelopmentStage → String
stageName engagementFibreStage = "name overlapping engagement fibres"
stageName scalableFeedbackClassificationStage = "scale feedback classification"
stageName teacherDesignedHumourFrameworkStage =
  "construct teacher-designed seven-consideration humour framework"
stageName ecologicalContextRestorationStage = "restore person-place ecology"
stageName epistemicAgencyRedistributionStage = "redistribute epistemic agency"
stageName studentIdentifiedSupportStage = "route student-identified support candidates"
stageName multiObserverAllyshipStage = "preserve plural observer and allyship fibres"
stageName coDesignedEnactmentStage = "co-design local enactment"
stageName evidenceReturnRechartingStage = "return evidence and revise the chart"

data CrossPaperRelationKind : Set where
  suppliesVocabulary : CrossPaperRelationKind
  scalesInterpretation : CrossPaperRelationKind
  correctsExtractiveRisk : CrossPaperRelationKind
  restoresEcologicalContext : CrossPaperRelationKind
  suppliesCandidateHandles : CrossPaperRelationKind
  addsObserverFibre : CrossPaperRelationKind
  suppliesGovernanceGate : CrossPaperRelationKind
  exposesProjectionBoundary : CrossPaperRelationKind
  proposesEmpiricalFollowUp : CrossPaperRelationKind

record CrossPaperRelation : Set where
  constructor mkCrossPaperRelation
  field
    relationLabel : String
    sourcePaper : Sources.PaperReference
    targetPaper : Sources.PaperReference
    relationKind : CrossPaperRelationKind
    claimRegister : ClaimRegister
    preservedContribution : String
    nonPromotionBoundary : String
    relationSourceBound : Bool
    relationSourceBoundIsTrue : relationSourceBound ≡ true

open CrossPaperRelation public

aiToVoiceRelation : CrossPaperRelation
aiToVoiceRelation =
  mkCrossPaperRelation
    "feedback classification to epistemic participation"
    Sources.aiFeedbackPaper
    Sources.voiceAgencyPaper
    correctsExtractiveRisk
    crossPaperInference
    "The later voice/agency critique can govern the earlier feedback-classification pipeline by requiring student participation beyond passive data provision."
    "The relation is a corpus synthesis; it does not imply that the 2024 paper was invalid or that the 2026 paper empirically tests the classifier."
    true refl

humourToVoiceRelation : CrossPaperRelation
humourToVoiceRelation =
  mkCrossPaperRelation
    "teacher-designed humour framework to constitutive epistemic agency"
    Sources.humourFrameworkPaper
    Sources.voiceAgencyPaper
    correctsExtractiveRisk
    crossPaperInference
    "The seven humour considerations are preserved as a useful teacher-side pedagogical projection while the later Brown/Kimber distinction asks which inquiry decisions students may shape before they are reduced to audience or feedback roles."
    "The later paper does not invalidate the humour framework or empirically test it; the governance relation is a DASHI cross-paper synthesis."
    true refl

humourToEcologyRelation : CrossPaperRelation
humourToEcologyRelation =
  mkCrossPaperRelation
    "audience/context descriptor to situated person-place ecology"
    Sources.humourFrameworkPaper
    Sources.ecologyOfDataPaper
    restoresEcologicalContext
    crossPaperInference
    "Audience/context can be recharted from a flat demographic descriptor into a relational person-place surface carrying teacher, peer, institutional, life-context and intersectional relations."
    "The ecology paper does not claim a humour-specific causal model, and omitted context cannot be reconstructed from feedback alone."
    true refl

aiToEcologyRelation : CrossPaperRelation
aiToEcologyRelation =
  mkCrossPaperRelation
    "feedback surface to ecology of data"
    Sources.aiFeedbackPaper
    Sources.ecologyOfDataPaper
    restoresEcologicalContext
    crossPaperInference
    "The ecology-of-data stance restores person-place transactions, affordances, minutiae and value flows hidden by flat aggregate coding."
    "The relation does not claim hidden context can be reconstructed from the comment alone."
    true refl

aiToSupportRelation : CrossPaperRelation
aiToSupportRelation =
  mkCrossPaperRelation
    "OEF residuals to student-identified support families"
    Sources.aiFeedbackPaper
    Sources.onlineSupportStrategiesPaper
    suppliesCandidateHandles
    empiricalFollowUpHypothesis
    "OEF residual signals may be cross-tested against five student-identified support families as optional +1 candidates."
    "No fixed category-to-intervention causal table is established by the two papers."
    true refl

voiceToSupportRelation : CrossPaperRelation
voiceToSupportRelation =
  mkCrossPaperRelation
    "student voice to support choice"
    Sources.voiceAgencyPaper
    Sources.onlineSupportStrategiesPaper
    suppliesGovernanceGate
    crossPaperInference
    "Student-identified strategies become stronger when students may shape, choose, reject and review the proposed support."
    "Student identification in one study does not make a strategy universally preferred."
    true refl

allyshipToPartnershipRelation : CrossPaperRelation
allyshipToPartnershipRelation =
  mkCrossPaperRelation
    "parental allyship to partnership barriers"
    Sources.parentalAllyshipLensPaper
    Sources.partnershipBarriersPaper
    addsObserverFibre
    crossPaperInference
    "The conceptual lens and empirical barrier study jointly motivate a parent-ally observer fibre carrying expertise and disability-adjacent experience."
    "Parent testimony remains distinct from child voice and does not alone prove institutional intent."
    true refl

advocacyToLensRelation : CrossPaperRelation
advocacyToLensRelation =
  mkCrossPaperRelation
    "advocacy/allyship distinction to conceptual proximity lens"
    Sources.advocacyAllyshipPaper
    Sources.parentalAllyshipLensPaper
    suppliesVocabulary
    crossPaperInference
    "The empirical distinction between advocacy and allyship supports a vocabulary of primary, vicarious and primary-adjacent experience."
    "The qualitative sources do not establish prevalence or universal parent trajectories."
    true refl

canonicalCrossPaperRelations : List CrossPaperRelation
canonicalCrossPaperRelations =
  aiToVoiceRelation
  ∷ humourToVoiceRelation
  ∷ humourToEcologyRelation
  ∷ aiToEcologyRelation
  ∷ aiToSupportRelation
  ∷ voiceToSupportRelation
  ∷ allyshipToPartnershipRelation
  ∷ advocacyToLensRelation
  ∷ []

record CrossPaperDialecticalDevelopment : Set where
  constructor mkCrossPaperDialecticalDevelopment
  field
    registry : Sources.EducationCorpusSourceRegistry
    registryIsCanonical : registry ≡ Sources.canonicalEducationCorpusSourceRegistry
    stages : List DevelopmentStage
    stagesAreCanonical : stages ≡ canonicalDevelopmentStages
    relations : List CrossPaperRelation
    relationsAreCanonical : relations ≡ canonicalCrossPaperRelations
    sourceInferenceExtensionSeparated : Bool
    sourceInferenceExtensionSeparatedIsTrue :
      sourceInferenceExtensionSeparated ≡ true
    laterPaperMayCorrectWithoutErasingEarlierContribution : Bool
    laterPaperMayCorrectWithoutErasingEarlierContributionIsTrue :
      laterPaperMayCorrectWithoutErasingEarlierContribution ≡ true
    crossPaperRelationsRemainCandidates : Bool
    crossPaperRelationsRemainCandidatesIsTrue :
      crossPaperRelationsRemainCandidates ≡ true
    empiricalCrossTestingRequired : Bool
    empiricalCrossTestingRequiredIsTrue : empiricalCrossTestingRequired ≡ true
    reading : String

open CrossPaperDialecticalDevelopment public

canonicalCrossPaperDialecticalDevelopment : CrossPaperDialecticalDevelopment
canonicalCrossPaperDialecticalDevelopment =
  mkCrossPaperDialecticalDevelopment
    Sources.canonicalEducationCorpusSourceRegistry refl
    canonicalDevelopmentStages refl
    canonicalCrossPaperRelations refl
    true refl
    true refl
    true refl
    true refl
    "The corpus is represented as a developmental braid: engagement vocabulary, scalable classification, a teacher-designed humour framework, ecological restoration, epistemic participation, student-identified support, multi-observer allyship, co-designed enactment and evidence-return recharting. The humour framework is sublated rather than erased: its seven practical considerations remain useful while later papers expose the governance, observer and contextual distinctions suppressed by a teacher-side projection. This ordering is a DASHI cross-paper synthesis and remains open to empirical testing."
```

## DASHI/Biology/OEFMultiFibreFeedbackHyperfabric.agda

Source: https://github.com/chboishabba/dashi_agda/blob/agent/digital-esd-source-crosspollination-20261101/DASHI/Biology/OEFMultiFibreFeedbackHyperfabric.agda

Blob SHA: `0dbdfacc91e1d193945864a0103753e8d9da06ee`

```agda
module DASHI.Biology.OEFMultiFibreFeedbackHyperfabric where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Source-bound OEF / AI feedback formalisation.
--
-- Primary source:
--   Dann, Christopher; Redmond, Petrea; Fanshawe, Melissa; Brown, Alice;
--   Getenet, Seyum; Shaik, Thanveer; Tao, Xiaohui; Galligan, Linda; Li, Yan.
--   "Making sense of student feedback and engagement using artificial
--   intelligence." Australasian Journal of Educational Technology 40(3),
--   58-76 (2024). DOI: 10.14742/ajet.8903.
--
-- Formal position:
--   - the paper is retained as an MVP / feasibility evidence surface;
--   - the five OEF elements are overlapping fibres, not exclusive essences;
--   - human labels are compiled into a classifier rather than removed;
--   - end-of-course feedback is a sparse, self-selected, time-local
--     projection of a larger student ecology;
--   - model outputs route human attention but do not become student meaning,
--     complete voice, learning truth, equity, diagnosis, or pedagogical
--     authority.

------------------------------------------------------------------------
-- Generic helpers.

data Never : Set where

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

------------------------------------------------------------------------
-- Paper metadata.

record PaperReference : Set where
  constructor mkPaperReference
  field
    paperTitle : String
    paperAuthors : List String
    paperJournal : String
    paperYear : Nat
    paperVolume : Nat
    paperIssue : Nat
    paperPages : String
    paperDOI : String
    paperInstitution : String
    paperStudyReading : String

open PaperReference public

canonicalPaperAuthors : List String
canonicalPaperAuthors =
  "Christopher Dann"
  ∷ "Petrea Redmond"
  ∷ "Melissa Fanshawe"
  ∷ "Alice Brown"
  ∷ "Seyum Getenet"
  ∷ "Thanveer Shaik"
  ∷ "Xiaohui Tao"
  ∷ "Linda Galligan"
  ∷ "Yan Li"
  ∷ []

canonicalPaperReference : PaperReference
canonicalPaperReference =
  mkPaperReference
    "Making sense of student feedback and engagement using artificial intelligence"
    canonicalPaperAuthors
    "Australasian Journal of Educational Technology"
    2024
    40
    3
    "58-76"
    "10.14742/ajet.8903"
    "University of Southern Queensland, Toowoomba, Queensland, Australia"
    "MVP feasibility study: manually labelled OEF feedback can train a scalable classification and visualisation prototype; semantic, ecological, longitudinal, and pedagogical closure are not promoted."

canonicalPaperTitle : paperTitle canonicalPaperReference ≡ "Making sense of student feedback and engagement using artificial intelligence"
canonicalPaperTitle = refl

canonicalPaperDOI : paperDOI canonicalPaperReference ≡ "10.14742/ajet.8903"
canonicalPaperDOI = refl

canonicalPaperAuthorCount : listCount canonicalPaperAuthors ≡ 9
canonicalPaperAuthorCount = refl

------------------------------------------------------------------------
-- Five Online Engagement Framework fibres.

data OEFElement : Set where
  socialEngagement : OEFElement
  cognitiveEngagement : OEFElement
  behaviouralEngagement : OEFElement
  collaborativeEngagement : OEFElement
  emotionalEngagement : OEFElement

canonicalOEFElements : List OEFElement
canonicalOEFElements =
  socialEngagement
  ∷ cognitiveEngagement
  ∷ behaviouralEngagement
  ∷ collaborativeEngagement
  ∷ emotionalEngagement
  ∷ []

canonicalOEFElementCount : listCount canonicalOEFElements ≡ 5
canonicalOEFElementCount = refl

oefElementName : OEFElement → String
oefElementName socialEngagement = "social engagement"
oefElementName cognitiveEngagement = "cognitive engagement"
oefElementName behaviouralEngagement = "behavioural engagement"
oefElementName collaborativeEngagement = "collaborative engagement"
oefElementName emotionalEngagement = "emotional engagement"

record OEFElementProfile : Set where
  constructor mkOEFElementProfile
  field
    profileElement : OEFElement
    profileIndicators : List String
    profileInterconnected : Bool
    profileInterconnectedIsTrue : profileInterconnected ≡ true
    profileDynamic : Bool
    profileDynamicIsTrue : profileDynamic ≡ true
    profileMultidimensional : Bool
    profileMultidimensionalIsTrue : profileMultidimensional ≡ true

open OEFElementProfile public

socialProfile : OEFElementProfile
socialProfile =
  mkOEFElementProfile
    socialEngagement
    ( "building community"
    ∷ "creating a sense of belonging"
    ∷ "developing relationships"
    ∷ "establishing trust"
    ∷ [] )
    true refl true refl true refl

cognitiveProfile : OEFElementProfile
cognitiveProfile =
  mkOEFElementProfile
    cognitiveEngagement
    ( "thinking critically"
    ∷ "activating metacognition"
    ∷ "integrating ideas"
    ∷ "justifying decisions"
    ∷ "developing deep discipline understanding"
    ∷ "distributing expertise"
    ∷ [] )
    true refl true refl true refl

behaviouralProfile : OEFElementProfile
behaviouralProfile =
  mkOEFElementProfile
    behaviouralEngagement
    ( "developing academic skills"
    ∷ "identifying opportunities and challenges"
    ∷ "developing multidisciplinary skills"
    ∷ "developing agency"
    ∷ "upholding online learning norms"
    ∷ "supporting and encouraging peers"
    ∷ [] )
    true refl true refl true refl

collaborativeProfile : OEFElementProfile
collaborativeProfile =
  mkOEFElementProfile
    collaborativeEngagement
    ( "learning with peers"
    ∷ "relating to faculty members"
    ∷ "connecting to institutional opportunities"
    ∷ "developing professional networks"
    ∷ [] )
    true refl true refl true refl

emotionalProfile : OEFElementProfile
emotionalProfile =
  mkOEFElementProfile
    emotionalEngagement
    ( "managing expectations"
    ∷ "articulating assumptions"
    ∷ "recognising motivations"
    ∷ "committing to learning"
    ∷ [] )
    true refl true refl true refl

canonicalOEFProfiles : List OEFElementProfile
canonicalOEFProfiles =
  socialProfile
  ∷ cognitiveProfile
  ∷ behaviouralProfile
  ∷ collaborativeProfile
  ∷ emotionalProfile
  ∷ []

------------------------------------------------------------------------
-- Multi-fibre bundles.

record OEFBundle : Set where
  constructor mkOEFBundle
  field
    bundleLabel : String
    bundleElements : List OEFElement
    bundleAllowsOverlap : Bool
    bundleAllowsOverlapIsTrue : bundleAllowsOverlap ≡ true
    bundleNotStudentEssence : Bool
    bundleNotStudentEssenceIsTrue : bundleNotStudentEssence ≡ true

open OEFBundle public

canonicalForumBundle : OEFBundle
canonicalForumBundle =
  mkOEFBundle
    "learning and collaborating in online forum discussions"
    ( cognitiveEngagement
    ∷ behaviouralEngagement
    ∷ collaborativeEngagement
    ∷ socialEngagement
    ∷ [] )
    true
    refl
    true
    refl

canonicalForumBundleHasFourFibres :
  listCount (bundleElements canonicalForumBundle) ≡ 4
canonicalForumBundleHasFourFibres = refl

EngagementOverlapIsSignalNotNoise : Set
EngagementOverlapIsSignalNotNoise =
  bundleAllowsOverlap canonicalForumBundle ≡ true

engagementOverlapIsSignalNotNoise : EngagementOverlapIsSignalNotNoise
engagementOverlapIsSignalNotNoise =
  bundleAllowsOverlapIsTrue canonicalForumBundle

------------------------------------------------------------------------
-- Survey projection and educational hypervoxel.

data FeedbackSurfaceKind : Set where
  voluntaryEndOfCourseComment : FeedbackSurfaceKind
  cleanedCommentSurface : FeedbackSurfaceKind
  humanLabelSurface : FeedbackSurfaceKind
  modelPredictionSurface : FeedbackSurfaceKind
  aggregateVisualisationSurface : FeedbackSurfaceKind

record FeedbackHypervoxel : Set where
  constructor mkFeedbackHypervoxel
  field
    studentSurface : String
    courseSurface : String
    timeSurface : String
    assessmentSurface : String
    teacherRelationSurface : String
    peerRelationSurface : String
    institutionSurface : String
    lifeContextSurface : String
    intersectionalAxisSurface : List String
    feedbackTextSurface : String

open FeedbackHypervoxel public

record SurveyProjection : Set where
  constructor mkSurveyProjection
  field
    projectionSource : FeedbackHypervoxel
    projectionKind : FeedbackSurfaceKind
    projectionText : String
    projectionSparse : Bool
    projectionSparseIsTrue : projectionSparse ≡ true
    projectionSelfSelected : Bool
    projectionSelfSelectedIsTrue : projectionSelfSelected ≡ true
    projectionTimeLocal : Bool
    projectionTimeLocalIsTrue : projectionTimeLocal ≡ true
    projectionNotWholeHypervoxel : Bool
    projectionNotWholeHypervoxelIsTrue : projectionNotWholeHypervoxel ≡ true
    projectionNoHiddenChartRecovery : Bool
    projectionNoHiddenChartRecoveryIsTrue : projectionNoHiddenChartRecovery ≡ true

open SurveyProjection public

canonicalFeedbackHypervoxel : FeedbackHypervoxel
canonicalFeedbackHypervoxel =
  mkFeedbackHypervoxel
    "student surface"
    "course surface"
    "end-of-course time surface"
    "assessment surface"
    "teacher relation surface"
    "peer relation surface"
    "institution surface"
    "life-context surface"
    ( "race"
    ∷ "class"
    ∷ "gender"
    ∷ "disability"
    ∷ "neurotype"
    ∷ "language"
    ∷ "culture"
    ∷ "caring role"
    ∷ "digital access"
    ∷ "prior education"
    ∷ "institutional trust"
    ∷ [] )
    "voluntary end-of-course comment"

canonicalSurveyProjection : SurveyProjection
canonicalSurveyProjection =
  mkSurveyProjection
    canonicalFeedbackHypervoxel
    voluntaryEndOfCourseComment
    "one textual projection of a larger situated student ecology"
    true refl
    true refl
    true refl
    true refl
    true refl

FeedbackIsHypervoxelProjection : Set
FeedbackIsHypervoxelProjection =
  projectionNotWholeHypervoxel canonicalSurveyProjection ≡ true

feedbackIsHypervoxelProjection : FeedbackIsHypervoxelProjection
feedbackIsHypervoxelProjection =
  projectionNotWholeHypervoxelIsTrue canonicalSurveyProjection

------------------------------------------------------------------------
-- Human coding and model prediction.

record HumanCodingDatum : Set where
  constructor mkHumanCodingDatum
  field
    codingCommentSurface : String
    codingHumanAssignedBundle : OEFBundle
    codingInterpretive : Bool
    codingInterpretiveIsTrue : codingInterpretive ≡ true
    codingNotEngagementTruth : Bool
    codingNotEngagementTruthIsTrue : codingNotEngagementTruth ≡ true

open HumanCodingDatum public

record ModelPrediction : Set where
  constructor mkModelPrediction
  field
    predictionInputSurface : String
    predictedBundle : OEFBundle
    sentimentProxy : String
    confidenceSurface : String
    predictionCompiledHumanCoding : Bool
    predictionCompiledHumanCodingIsTrue : predictionCompiledHumanCoding ≡ true
    predictionProxyOnly : Bool
    predictionProxyOnlyIsTrue : predictionProxyOnly ≡ true
    predictionNotStudentMeaning : Bool
    predictionNotStudentMeaningIsTrue : predictionNotStudentMeaning ≡ true
    predictionNotCompleteVoice : Bool
    predictionNotCompleteVoiceIsTrue : predictionNotCompleteVoice ≡ true
    predictionNotPedagogicalAuthority : Bool
    predictionNotPedagogicalAuthorityIsTrue : predictionNotPedagogicalAuthority ≡ true

open ModelPrediction public

canonicalHumanCodingDatum : HumanCodingDatum
canonicalHumanCodingDatum =
  mkHumanCodingDatum
    "I liked learning and collaborating in the online forums."
    canonicalForumBundle
    true refl
    true refl

canonicalModelPrediction : ModelPrediction
canonicalModelPrediction =
  mkModelPrediction
    "cleaned student comment surface"
    canonicalForumBundle
    "sentiment proxy"
    "classification confidence surface"
    true refl
    true refl
    true refl
    true refl
    true refl

HumanLabelCompiledNotRemoved : Set
HumanLabelCompiledNotRemoved =
  predictionCompiledHumanCoding canonicalModelPrediction ≡ true

humanLabelCompiledNotRemoved : HumanLabelCompiledNotRemoved
humanLabelCompiledNotRemoved =
  predictionCompiledHumanCodingIsTrue canonicalModelPrediction

AIClassificationIsProxy : Set
AIClassificationIsProxy =
  predictionProxyOnly canonicalModelPrediction ≡ true

aiClassificationIsProxy : AIClassificationIsProxy
aiClassificationIsProxy =
  predictionProxyOnlyIsTrue canonicalModelPrediction

------------------------------------------------------------------------
-- Study counts and reported classifier metrics.

record ClassifierPerformanceRow : Set where
  constructor mkClassifierPerformanceRow
  field
    performanceElement : OEFElement
    trainingCount : Nat
    precisionHundredths : Nat
    f1Hundredths : Nat
    recallHundredths : Nat
    balancedAccuracyTenthsPercent : Nat

open ClassifierPerformanceRow public

behaviouralPerformance : ClassifierPerformanceRow
behaviouralPerformance =
  mkClassifierPerformanceRow behaviouralEngagement 98 65 51 42 611

cognitivePerformance : ClassifierPerformanceRow
cognitivePerformance =
  mkClassifierPerformanceRow cognitiveEngagement 114 56 54 52 639

emotionalPerformance : ClassifierPerformanceRow
emotionalPerformance =
  mkClassifierPerformanceRow emotionalEngagement 118 86 72 62 931

socialPerformance : ClassifierPerformanceRow
socialPerformance =
  mkClassifierPerformanceRow socialEngagement 28 56 58 60 722

collaborativePerformance : ClassifierPerformanceRow
collaborativePerformance =
  mkClassifierPerformanceRow collaborativeEngagement 25 87 70 58 561

canonicalPerformanceRows : List ClassifierPerformanceRow
canonicalPerformanceRows =
  behaviouralPerformance
  ∷ cognitivePerformance
  ∷ emotionalPerformance
  ∷ socialPerformance
  ∷ collaborativePerformance
  ∷ []

record PaperStudySurface : Set where
  constructor mkPaperStudySurface
  field
    labelledTrainingFeedbackSentiments : Nat
    laterTestingFeedbackSentiments : Nat
    overallAccuracyPercent : Nat
    performanceRows : List ClassifierPerformanceRow
    categorySpecificErrorVisible : Bool
    categorySpecificErrorVisibleIsTrue : categorySpecificErrorVisible ≡ true
    classImbalanceRecorded : Bool
    classImbalanceRecordedIsTrue : classImbalanceRecorded ≡ true
    ambiguitySarcasmDomainLanguageRecorded : Bool
    ambiguitySarcasmDomainLanguageRecordedIsTrue : ambiguitySarcasmDomainLanguageRecorded ≡ true
    annotationBiasOpen : Bool
    annotationBiasOpenIsTrue : annotationBiasOpen ≡ true
    singleRegionalUniversityScope : Bool
    singleRegionalUniversityScopeIsTrue : singleRegionalUniversityScope ≡ true

open PaperStudySurface public

canonicalPaperStudySurface : PaperStudySurface
canonicalPaperStudySurface =
  mkPaperStudySurface
    383
    311
    76
    canonicalPerformanceRows
    true refl
    true refl
    true refl
    true refl
    true refl

canonicalTrainingCount :
  labelledTrainingFeedbackSentiments canonicalPaperStudySurface ≡ 383
canonicalTrainingCount = refl

canonicalTestingCount :
  laterTestingFeedbackSentiments canonicalPaperStudySurface ≡ 311
canonicalTestingCount = refl

canonicalOverallAccuracy :
  overallAccuracyPercent canonicalPaperStudySurface ≡ 76
canonicalOverallAccuracy = refl

canonicalBehaviouralRecall :
  recallHundredths behaviouralPerformance ≡ 42
canonicalBehaviouralRecall = refl

------------------------------------------------------------------------
-- Residual decomposition.

data FeedbackResidualKind : Set where
  samplingResidual : FeedbackResidualKind
  nonresponseResidual : FeedbackResidualKind
  annotationResidual : FeedbackResidualKind
  classificationResidual : FeedbackResidualKind
  semanticResidual : FeedbackResidualKind
  multilabelCompressionResidual : FeedbackResidualKind
  ecologicalResidual : FeedbackResidualKind
  intersectionalResidual : FeedbackResidualKind
  temporalResidual : FeedbackResidualKind
  pedagogicalResidual : FeedbackResidualKind

canonicalFeedbackResidualKinds : List FeedbackResidualKind
canonicalFeedbackResidualKinds =
  samplingResidual
  ∷ nonresponseResidual
  ∷ annotationResidual
  ∷ classificationResidual
  ∷ semanticResidual
  ∷ multilabelCompressionResidual
  ∷ ecologicalResidual
  ∷ intersectionalResidual
  ∷ temporalResidual
  ∷ pedagogicalResidual
  ∷ []

canonicalFeedbackResidualKindCount :
  listCount canonicalFeedbackResidualKinds ≡ 10
canonicalFeedbackResidualKindCount = refl

------------------------------------------------------------------------
-- Claim routes and fail-closed boundaries.

data FeedbackClaimRoute : Set where
  candidateFeedbackProxyRoute : FeedbackClaimRoute
  modelEqualsStudentMeaningRoute : FeedbackClaimRoute
  surveyEqualsCompleteVoiceRoute : FeedbackClaimRoute
  respondentsEqualCohortRoute : FeedbackClaimRoute
  missingCategoryEqualsMissingEngagementRoute : FeedbackClaimRoute
  sentimentEqualsWellbeingRoute : FeedbackClaimRoute
  aggregateEqualsIndividualRoute : FeedbackClaimRoute
  endpointEqualsTrajectoryRoute : FeedbackClaimRoute
  oefEqualsWholeEcologyRoute : FeedbackClaimRoute
  dashboardEqualsPedagogicalAuthorityRoute : FeedbackClaimRoute

AdmissibleFeedbackClaimRoute : FeedbackClaimRoute → Set
AdmissibleFeedbackClaimRoute candidateFeedbackProxyRoute = ⊤
AdmissibleFeedbackClaimRoute modelEqualsStudentMeaningRoute = Never
AdmissibleFeedbackClaimRoute surveyEqualsCompleteVoiceRoute = Never
AdmissibleFeedbackClaimRoute respondentsEqualCohortRoute = Never
AdmissibleFeedbackClaimRoute missingCategoryEqualsMissingEngagementRoute = Never
AdmissibleFeedbackClaimRoute sentimentEqualsWellbeingRoute = Never
AdmissibleFeedbackClaimRoute aggregateEqualsIndividualRoute = Never
AdmissibleFeedbackClaimRoute endpointEqualsTrajectoryRoute = Never
AdmissibleFeedbackClaimRoute oefEqualsWholeEcologyRoute = Never
AdmissibleFeedbackClaimRoute dashboardEqualsPedagogicalAuthorityRoute = Never

candidateFeedbackProxyRouteAdmissible :
  AdmissibleFeedbackClaimRoute candidateFeedbackProxyRoute
candidateFeedbackProxyRouteAdmissible = tt

modelEqualsStudentMeaningBlocked :
  AdmissibleFeedbackClaimRoute modelEqualsStudentMeaningRoute → Never
modelEqualsStudentMeaningBlocked ()

surveyEqualsCompleteVoiceBlocked :
  AdmissibleFeedbackClaimRoute surveyEqualsCompleteVoiceRoute → Never
surveyEqualsCompleteVoiceBlocked ()

respondentsEqualCohortBlocked :
  AdmissibleFeedbackClaimRoute respondentsEqualCohortRoute → Never
respondentsEqualCohortBlocked ()

missingCategoryEqualsMissingEngagementBlocked :
  AdmissibleFeedbackClaimRoute missingCategoryEqualsMissingEngagementRoute → Never
missingCategoryEqualsMissingEngagementBlocked ()

sentimentEqualsWellbeingBlocked :
  AdmissibleFeedbackClaimRoute sentimentEqualsWellbeingRoute → Never
sentimentEqualsWellbeingBlocked ()

aggregateEqualsIndividualBlocked :
  AdmissibleFeedbackClaimRoute aggregateEqualsIndividualRoute → Never
aggregateEqualsIndividualBlocked ()

endpointEqualsTrajectoryBlocked :
  AdmissibleFeedbackClaimRoute endpointEqualsTrajectoryRoute → Never
endpointEqualsTrajectoryBlocked ()

oefEqualsWholeEcologyBlocked :
  AdmissibleFeedbackClaimRoute oefEqualsWholeEcologyRoute → Never
oefEqualsWholeEcologyBlocked ()

dashboardEqualsPedagogicalAuthorityBlocked :
  AdmissibleFeedbackClaimRoute dashboardEqualsPedagogicalAuthorityRoute → Never
dashboardEqualsPedagogicalAuthorityBlocked ()

------------------------------------------------------------------------
-- Canonical aggregate.

record OEFMultiFibreFeedbackHyperfabric : Set where
  constructor mkOEFMultiFibreFeedbackHyperfabric
  field
    sourceReference : PaperReference
    sourceReferenceIsCanonical : sourceReference ≡ canonicalPaperReference
    oefElements : List OEFElement
    oefElementsAreCanonical : oefElements ≡ canonicalOEFElements
    oefProfiles : List OEFElementProfile
    oefProfilesAreCanonical : oefProfiles ≡ canonicalOEFProfiles
    forumMultiFibreBundle : OEFBundle
    forumMultiFibreBundleIsCanonical : forumMultiFibreBundle ≡ canonicalForumBundle
    surveyProjection : SurveyProjection
    surveyProjectionIsCanonical : surveyProjection ≡ canonicalSurveyProjection
    humanCodingDatum : HumanCodingDatum
    humanCodingDatumIsCanonical : humanCodingDatum ≡ canonicalHumanCodingDatum
    modelPrediction : ModelPrediction
    modelPredictionIsCanonical : modelPrediction ≡ canonicalModelPrediction
    paperStudySurface : PaperStudySurface
    paperStudySurfaceIsCanonical : paperStudySurface ≡ canonicalPaperStudySurface
    residualKinds : List FeedbackResidualKind
    residualKindsAreCanonical : residualKinds ≡ canonicalFeedbackResidualKinds
    claimRoute : FeedbackClaimRoute
    claimRouteIsCandidate : claimRoute ≡ candidateFeedbackProxyRoute
    claimRouteAdmissible : AdmissibleFeedbackClaimRoute claimRoute
    multiLabelPreserved : Bool
    multiLabelPreservedIsTrue : multiLabelPreserved ≡ true
    humanCodeInterpretive : Bool
    humanCodeInterpretiveIsTrue : humanCodeInterpretive ≡ true
    modelPredictionProxyOnly : Bool
    modelPredictionProxyOnlyIsTrue : modelPredictionProxyOnly ≡ true
    aggregateNotIndividual : Bool
    aggregateNotIndividualIsTrue : aggregateNotIndividual ≡ true
    missingCategoryNotMissingEngagement : Bool
    missingCategoryNotMissingEngagementIsTrue : missingCategoryNotMissingEngagement ≡ true
    humanReviewRequired : Bool
    humanReviewRequiredIsTrue : humanReviewRequired ≡ true
    reading : String

open OEFMultiFibreFeedbackHyperfabric public

canonicalOEFMultiFibreFeedbackHyperfabric :
  OEFMultiFibreFeedbackHyperfabric
canonicalOEFMultiFibreFeedbackHyperfabric =
  mkOEFMultiFibreFeedbackHyperfabric
    canonicalPaperReference refl
    canonicalOEFElements refl
    canonicalOEFProfiles refl
    canonicalForumBundle refl
    canonicalSurveyProjection refl
    canonicalHumanCodingDatum refl
    canonicalModelPrediction refl
    canonicalPaperStudySurface refl
    canonicalFeedbackResidualKinds refl
    candidateFeedbackProxyRoute refl tt
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    "Student feedback is a sparse, self-selected, time-local projection of a multi-fibred educational hyperfabric. OEF and NLP may organise the projection and expose candidate overlaps and residuals; contextual human review and governance are required before pedagogical action."

OEFIsMultiFibred : Set
OEFIsMultiFibred =
  multiLabelPreserved canonicalOEFMultiFibreFeedbackHyperfabric ≡ true

oefIsMultiFibred : OEFIsMultiFibred
oefIsMultiFibred =
  multiLabelPreservedIsTrue canonicalOEFMultiFibreFeedbackHyperfabric

AggregateVisualisationNotIndividualTruth : Set
AggregateVisualisationNotIndividualTruth =
  aggregateNotIndividual canonicalOEFMultiFibreFeedbackHyperfabric ≡ true

aggregateVisualisationNotIndividualTruth :
  AggregateVisualisationNotIndividualTruth
aggregateVisualisationNotIndividualTruth =
  aggregateNotIndividualIsTrue canonicalOEFMultiFibreFeedbackHyperfabric

MissingClassificationNotMissingEngagement : Set
MissingClassificationNotMissingEngagement =
  missingCategoryNotMissingEngagement canonicalOEFMultiFibreFeedbackHyperfabric ≡ true

missingClassificationNotMissingEngagement :
  MissingClassificationNotMissingEngagement
missingClassificationNotMissingEngagement =
  missingCategoryNotMissingEngagementIsTrue canonicalOEFMultiFibreFeedbackHyperfabric
```

## DASHI/Biology/HumourEpistemicAgencyHyperfabricBridge.agda

Source: https://github.com/chboishabba/dashi_agda/blob/agent/digital-esd-source-crosspollination-20261101/DASHI/Biology/HumourEpistemicAgencyHyperfabricBridge.agda

Blob SHA: `bdc7920600b0e931c86a9fc0b23bf21cceca25c6`

```agda
module DASHI.Biology.HumourEpistemicAgencyHyperfabricBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.HumourOnlineEngagementFramework as Humour
import DASHI.Biology.OEFMultiFibreFeedbackHyperfabric as OEF
import DASHI.Biology.StudentVoiceEpistemicAgencyBridge as Voice
import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.ConditionalNormalizationBoundary as Conditional
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.EpistemicInquiryGovernance as Governance
import DASHI.Core.PluralConsumerProjectionSafety as Plural
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Reasoning.DialecticInvariantGeometry as Dialectic

------------------------------------------------------------------------
-- CROSS-PAPER / DASHI FORMAL EXTENSION
--
-- Source anchors:
--
--   Alice Brown, Josephine Pryce, Anja Pabel (2025),
--   "Considerations for integrating humour as a strategy to heighten online
--   student engagement and learning in higher education: An emerging
--   framework", HERDSA Conference, p. 64. DOI: no DOI assigned/listed.
--
--   Alice Brown and Megan Kimber (2026),
--   "Repositioning Student Voice and Agency: A Call for the Epistemic
--   Expansion of Scholarship of Teaching and Learning Inquiry",
--   Active Learning in Higher Education 27(2), 253-264.
--   DOI: 10.1177/14697874261426374.
--
-- Intersectional reference / motivation:
--   Kimberle Crenshaw (1989), "Demarginalizing the Intersection of Race and
--   Sex", University of Chicago Legal Forum 1989(1), Article 8.
--   DOI: no DOI assigned to the original article.
--
-- These sources motivate the domain interpretation.  The typed governance,
-- carrier-expansion, plural-safety and dynamic-defect constructions below are
-- DASHI formal extensions and are not attributed as theorems of those papers.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Brown/Kimber participation stages as constitutive-governance coordinates.
--
-- Feedback alone supplies no constructor here.  Higher stages gain explicitly
-- scoped authority over the inquiry coordinates they can contest or revise.
------------------------------------------------------------------------

data StageAuthorises :
    Voice.EpistemicParticipationStage →
    Governance.InquiryCoordinate → Set where
  questionShapesConsumer :
    StageAuthorises
      Voice.questionContributorStage
      Governance.consumerCoordinate

  codingShapesProjection :
    StageAuthorises
      Voice.codingFrameContributorStage
      Governance.projectionCoordinate

  interpretationShapesRelevance :
    StageAuthorises
      Voice.coInterpreterStage
      Governance.relevanceCoordinate

  coDesignShapesCarrier :
    StageAuthorises
      Voice.coDesignerStage
      Governance.carrierCoordinate

  coDesignShapesProjection :
    StageAuthorises
      Voice.coDesignerStage
      Governance.projectionCoordinate

  coDesignShapesDynamics :
    StageAuthorises
      Voice.coDesignerStage
      Governance.dynamicsCoordinate

  evidenceReviewShapesResidual :
    StageAuthorises
      Voice.evidenceReturnReviewerStage
      Governance.residualCoordinate

  evidenceReviewShapesRevision :
    StageAuthorises
      Voice.evidenceReturnReviewerStage
      Governance.revisionCoordinate

humourStageGovernance :
  Governance.EpistemicGovernance Voice.EpistemicParticipationStage
humourStageGovernance = Governance.epistemicGovernance StageAuthorises

feedbackStageHasNoConstitutiveAuthority :
  (coordinate : Governance.InquiryCoordinate) →
  StageAuthorises Voice.feedbackSourceStage coordinate →
  ⊥
feedbackStageHasNoConstitutiveAuthority coordinate ()

questionContributionCanShapeConsumer :
  Governance.Authorised humourStageGovernance
    Voice.questionContributorStage Governance.consumerCoordinate
questionContributionCanShapeConsumer = questionShapesConsumer

codingContributionCanContestProjection :
  Governance.Authorised humourStageGovernance
    Voice.codingFrameContributorStage Governance.projectionCoordinate
codingContributionCanContestProjection = codingShapesProjection

------------------------------------------------------------------------
-- Intersectionality as strict carrier expansion, not merely reweighting.
------------------------------------------------------------------------

data FlatAudienceAxis : Set where
  ageAxis : FlatAudienceAxis
  cultureAxis : FlatAudienceAxis
  languageAxis : FlatAudienceAxis

data SituatedAudienceAxis : Set where
  situatedAgeAxis : SituatedAudienceAxis
  situatedCultureAxis : SituatedAudienceAxis
  situatedLanguageAxis : SituatedAudienceAxis
  raceAxis : SituatedAudienceAxis
  classAxis : SituatedAudienceAxis
  genderAxis : SituatedAudienceAxis
  disabilityAxis : SituatedAudienceAxis
  neurotypeAxis : SituatedAudienceAxis
  caringRoleAxis : SituatedAudienceAxis
  institutionalPowerAxis : SituatedAudienceAxis
  historicalContextAxis : SituatedAudienceAxis

embedFlatAudienceAxis : FlatAudienceAxis → SituatedAudienceAxis
embedFlatAudienceAxis ageAxis = situatedAgeAxis
embedFlatAudienceAxis cultureAxis = situatedCultureAxis
embedFlatAudienceAxis languageAxis = situatedLanguageAxis

institutionalPowerHasNoFlatPreimage :
  (axis : FlatAudienceAxis) →
  embedFlatAudienceAxis axis ≡ institutionalPowerAxis →
  ⊥
institutionalPowerHasNoFlatPreimage ageAxis ()
institutionalPowerHasNoFlatPreimage cultureAxis ()
institutionalPowerHasNoFlatPreimage languageAxis ()

historicalContextHasNoFlatPreimage :
  (axis : FlatAudienceAxis) →
  embedFlatAudienceAxis axis ≡ historicalContextAxis →
  ⊥
historicalContextHasNoFlatPreimage ageAxis ()
historicalContextHasNoFlatPreimage cultureAxis ()
historicalContextHasNoFlatPreimage languageAxis ()

------------------------------------------------------------------------
-- Situated humour as dynamics.
--
-- Two students can have the same present positive observable while the same
-- later admissible interaction separates their consumer-visible futures.
------------------------------------------------------------------------

data HumourStudentState : Set where
  visibleLaughTrust : HumourStudentState
  visibleLaughMasking : HumourStudentState
  laterTrust : HumourStudentState
  laterWithdrawal : HumourStudentState

data HumourAction : Set where
  subsequentClassInteraction : HumourAction

data HumourPrecondition : HumourStudentState → HumourAction → Set where
  trustReady :
    HumourPrecondition visibleLaughTrust subsequentClassInteraction
  maskingReady :
    HumourPrecondition visibleLaughMasking subsequentClassInteraction

data HumourPostcondition :
    HumourStudentState → HumourAction → HumourStudentState → Set where
  trustContinues :
    HumourPostcondition
      visibleLaughTrust subsequentClassInteraction laterTrust
  maskingWithdraws :
    HumourPostcondition
      visibleLaughMasking subsequentClassInteraction laterWithdrawal

humourActionLabel : HumourAction → String
humourActionLabel subsequentClassInteraction =
  "subsequent classroom interaction after currently positive visible reception"

humourSystem :
  Dependency.DependentActionSystem HumourStudentState HumourAction
humourSystem = record
  { Precondition = HumourPrecondition
  ; Postcondition = HumourPostcondition
  ; actionLabel = humourActionLabel
  }

trustAdvance :
  Dependency.AdmissibleAction
    humourSystem visibleLaughTrust subsequentClassInteraction
trustAdvance = record
  { precondition = trustReady
  ; after = laterTrust
  ; postcondition = trustContinues
  ; dependencyReceipt = "trust-bearing state advances to later trust"
  }

maskingAdvance :
  Dependency.AdmissibleAction
    humourSystem visibleLaughMasking subsequentClassInteraction
maskingAdvance = record
  { precondition = maskingReady
  ; after = laterWithdrawal
  ; postcondition = maskingWithdraws
  ; dependencyReceipt = "masking/compliance state advances to later withdrawal"
  }

trustExecution :
  Reachability.Executes humourSystem
    (subsequentClassInteraction ∷ [])
    visibleLaughTrust
    laterTrust
trustExecution =
  Reachability.executesCons trustAdvance Reachability.executesNil

maskingExecution :
  Reachability.Executes humourSystem
    (subsequentClassInteraction ∷ [])
    visibleLaughMasking
    laterWithdrawal
maskingExecution =
  Reachability.executesCons maskingAdvance Reachability.executesNil


data HumourConsumer : Set where
  threeCsConsumer : HumourConsumer
  longTermEquityConsumer : HumourConsumer

humourProject : HumourConsumer → HumourStudentState → Bool
humourProject threeCsConsumer _ = true
humourProject longTermEquityConsumer visibleLaughTrust = true
humourProject longTermEquityConsumer visibleLaughMasking = true
humourProject longTermEquityConsumer laterTrust = true
humourProject longTermEquityConsumer laterWithdrawal = false

humourProjectionFamily :
  Plural.ConsumerProjectionFamily
    HumourStudentState HumourAction HumourConsumer Bool
humourProjectionFamily =
  Plural.consumerProjectionFamily humourSystem humourProject

threeCsProjectionDynamicallySafe :
  Dynamic.DynamicConsumerSafety humourSystem (humourProject threeCsConsumer)
threeCsProjectionDynamicallySafe =
  Dynamic.dynamicConsumerSafety
    (λ sameCurrent leftExecution rightExecution → refl)

longTermEquityProjectionDefect :
  Dynamic.TerminalisationDefect
    humourSystem
    (humourProject longTermEquityConsumer)
longTermEquityProjectionDefect =
  Dynamic.terminalisationDefect
    (subsequentClassInteraction ∷ [])
    visibleLaughTrust
    visibleLaughMasking
    laterTrust
    laterWithdrawal
    refl
    trustExecution
    maskingExecution
    (λ ())

humourConsumerSafetyAsymmetry :
  Plural.ConsumerSafetyAsymmetry
    humourProjectionFamily
    threeCsConsumer
    longTermEquityConsumer
humourConsumerSafetyAsymmetry =
  Plural.consumerSafetyAsymmetry
    threeCsProjectionDynamicallySafe
    longTermEquityProjectionDefect

threeCsSafetyDoesNotEstablishPluralSafety :
  Plural.PluralDynamicSafety humourProjectionFamily → ⊥
threeCsSafetyDoesNotEstablishPluralSafety =
  Plural.asymmetryContradictsPluralSafety humourConsumerSafetyAsymmetry

------------------------------------------------------------------------
-- Aggregate-positive reception is not universal-positive reception.
------------------------------------------------------------------------

data SampleStudent : Set where
  studentOne : SampleStudent
  studentTwo : SampleStudent
  studentThree : SampleStudent

studentPositiveReception : SampleStudent → Bool
studentPositiveReception studentOne = true
studentPositiveReception studentTwo = true
studentPositiveReception studentThree = false

headlineAggregatePositive : Bool
headlineAggregatePositive = true

headlineAggregatePositiveIsTrue : headlineAggregatePositive ≡ true
headlineAggregatePositiveIsTrue = refl

universalPositiveReceptionImpossible :
  ((student : SampleStudent) → studentPositiveReception student ≡ true) →
  ⊥
universalPositiveReceptionImpossible allPositive with allPositive studentThree
... | ()

------------------------------------------------------------------------
-- Dialectical disagreement is an inhabited corridor, not framework failure.
------------------------------------------------------------------------

data HumourEvent : Set where
  canonicalHumourEvent : HumourEvent

humourDialecticField : Dialectic.DialecticField HumourEvent
humourDialecticField = Dialectic.dialecticField observeHumour
  where
    observeHumour :
      Dialectic.Stance → Dialectic.Predicate HumourEvent
    observeHumour Dialectic.thesisSide canonicalHumourEvent = true
    observeHumour Dialectic.antithesisSide canonicalHumourEvent = false

humourDisagreementCorridorIsLive :
  Dialectic.corridor humourDialecticField canonicalHumourEvent ≡ true
humourDisagreementCorridorIsLive = refl

------------------------------------------------------------------------
-- Canonical bridge.
------------------------------------------------------------------------

record HumourEpistemicAgencyHyperfabricBridge : Set₁ where
  constructor humourEpistemicAgencyHyperfabricBridge
  field
    sourceFramework : Humour.HumourFrameworkSourceSurface
    sourceFrameworkIsCanonical :
      sourceFramework ≡ Humour.canonicalHumourFrameworkSourceSurface

    laterVoiceAgencyBridge : Voice.StudentVoiceEpistemicAgencyBridge
    laterVoiceAgencyBridgeIsCanonical :
      laterVoiceAgencyBridge ≡ Voice.canonicalStudentVoiceEpistemicAgencyBridge

    situatedFeedbackHypervoxel : OEF.FeedbackHypervoxel
    situatedFeedbackHypervoxelIsCanonical :
      situatedFeedbackHypervoxel ≡ OEF.canonicalFeedbackHypervoxel

    governance :
      Governance.EpistemicGovernance Voice.EpistemicParticipationStage
    governanceIsCanonical : governance ≡ humourStageGovernance

    conditionalNormalizationCounterexample :
      Conditional.ConditionalNormalizationCounterexample
    conditionalNormalizationCounterexampleIsCanonical :
      conditionalNormalizationCounterexample
      ≡ Conditional.canonicalConditionalNormalizationCounterexample

    dynamicReceptionDefect :
      Dynamic.TerminalisationDefect
        humourSystem
        (humourProject longTermEquityConsumer)
    dynamicReceptionDefectIsCanonical :
      dynamicReceptionDefect ≡ longTermEquityProjectionDefect

    consumerSafetyAsymmetry :
      Plural.ConsumerSafetyAsymmetry
        humourProjectionFamily
        threeCsConsumer
        longTermEquityConsumer
    consumerSafetyAsymmetryIsCanonical :
      consumerSafetyAsymmetry ≡ humourConsumerSafetyAsymmetry

    feedbackDoesNotConferConstitutiveAuthority :
      (coordinate : Governance.InquiryCoordinate) →
      StageAuthorises Voice.feedbackSourceStage coordinate →
      ⊥

    flatAudienceCarrierMissesInstitutionalPower :
      (axis : FlatAudienceAxis) →
      embedFlatAudienceAxis axis ≡ institutionalPowerAxis →
      ⊥

    aggregatePositiveDoesNotMeanUniversalPositive :
      ((student : SampleStudent) → studentPositiveReception student ≡ true) →
      ⊥

    disagreementCorridorRetained :
      Dialectic.corridor humourDialecticField canonicalHumourEvent ≡ true

    reading : String

open HumourEpistemicAgencyHyperfabricBridge public

canonicalHumourEpistemicAgencyHyperfabricBridge :
  HumourEpistemicAgencyHyperfabricBridge
canonicalHumourEpistemicAgencyHyperfabricBridge =
  humourEpistemicAgencyHyperfabricBridge
    Humour.canonicalHumourFrameworkSourceSurface refl
    Voice.canonicalStudentVoiceEpistemicAgencyBridge refl
    OEF.canonicalFeedbackHypervoxel refl
    humourStageGovernance refl
    Conditional.canonicalConditionalNormalizationCounterexample refl
    longTermEquityProjectionDefect refl
    humourConsumerSafetyAsymmetry refl
    feedbackStageHasNoConstitutiveAuthority
    institutionalPowerHasNoFlatPreimage
    universalPositiveReceptionImpossible
    humourDisagreementCorridorIsLive
    "The earlier humour framework is preserved as a useful teacher-side projection, then governed by the later voice/agency distinction and the existing situated OEF hypervoxel. Feedback alone has no constitutive-governance constructor; flat audience descriptors embed strictly into a richer intersectional carrier; a 3Cs-visible positive surface can be dynamically safe for one consumer while a long-term equity consumer has an explicit quotient defect; respondent renormalisation is not cohort completeness; aggregate positive reception is not universal reception; and teacher/student disagreement remains an epistemically live dialectical corridor rather than noise."
```

## DASHI/Biology/EcologyOfDataHyperfabricBridge.agda

Source: https://github.com/chboishabba/dashi_agda/blob/agent/digital-esd-source-crosspollination-20261101/DASHI/Biology/EcologyOfDataHyperfabricBridge.agda

Blob SHA: `8ed5f46dbdbf93cdb7735cfbdbccb5764923e6ab`

```agda
module DASHI.Biology.EcologyOfDataHyperfabricBridge where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.EducationCorpusSourceRegistry as Sources
import DASHI.Biology.OEFMultiFibreFeedbackHyperfabric as OEF

------------------------------------------------------------------------
-- Ecology-of-data / hyperfabric bridge.
--
-- The Finn/Brown paper supplies an eco-behavioural correction to flat coding:
-- person and place are co-constituted, and analysis should retain system
-- edges, affordances, minutiae, value flows, and pedagogical curation.

data CustodianResponsibility : Set where
  mapSystemEdgesAndIntersections : CustodianResponsibility
  analyseAffordancesOfPlace : CustodianResponsibility
  attendToMinutiaeAndEffort : CustodianResponsibility
  considerFlowsOfValue : CustodianResponsibility
  learnWithAndCurateData : CustodianResponsibility

canonicalCustodianResponsibilities : List CustodianResponsibility
canonicalCustodianResponsibilities =
  mapSystemEdgesAndIntersections
  ∷ analyseAffordancesOfPlace
  ∷ attendToMinutiaeAndEffort
  ∷ considerFlowsOfValue
  ∷ learnWithAndCurateData
  ∷ []

responsibilityName : CustodianResponsibility → String
responsibilityName mapSystemEdgesAndIntersections =
  "map system edges and intersections"
responsibilityName analyseAffordancesOfPlace =
  "analyse affordances of place"
responsibilityName attendToMinutiaeAndEffort =
  "attend to minutiae and effort after meaning and value"
responsibilityName considerFlowsOfValue =
  "consider flows of value"
responsibilityName learnWithAndCurateData =
  "learn with and curate data pedagogically"

record EcologicalFeedbackCell : Set where
  constructor mkEcologicalFeedbackCell
  field
    studentSurface : String
    placeSurface : String
    affordanceSurface : String
    activitySurface : String
    valueFlowSurface : String
    timeSurface : String
    feedbackProjection : OEF.FeedbackHypervoxel
    personPlaceCoConstituted : Bool
    personPlaceCoConstitutedIsTrue : personPlaceCoConstituted ≡ true
    projectionNotWholeEcology : Bool
    projectionNotWholeEcologyIsTrue : projectionNotWholeEcology ≡ true

open EcologicalFeedbackCell public

canonicalEcologicalFeedbackCell : EcologicalFeedbackCell
canonicalEcologicalFeedbackCell =
  mkEcologicalFeedbackCell
    "situated student"
    "course / home / platform / institution place field"
    "available and unavailable learning affordances"
    "student activity and effort"
    "flows of attention, labour, care, recognition and institutional benefit"
    "semester-local observation time"
    OEF.canonicalFeedbackHypervoxel
    true refl
    true refl

record CustodianshipGate : Set where
  constructor mkCustodianshipGate
  field
    contextRetained : Bool
    contextRetainedIsTrue : contextRetained ≡ true
    participantAgencyRetained : Bool
    participantAgencyRetainedIsTrue : participantAgencyRetained ≡ true
    dataOwnershipNotAssumed : Bool
    dataOwnershipNotAssumedIsTrue : dataOwnershipNotAssumed ≡ true
    valueExtractionAudited : Bool
    valueExtractionAuditedIsTrue : valueExtractionAudited ≡ true
    codingDoesNotEraseMinutiae : Bool
    codingDoesNotEraseMinutiaeIsTrue : codingDoesNotEraseMinutiae ≡ true
    curationOpenToContest : Bool
    curationOpenToContestIsTrue : curationOpenToContest ≡ true

open CustodianshipGate public

canonicalCustodianshipGate : CustodianshipGate
canonicalCustodianshipGate =
  mkCustodianshipGate
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl

record EcologyOfDataHyperfabricBridge : Set where
  constructor mkEcologyOfDataHyperfabricBridge
  field
    sourcePaper : Sources.PaperReference
    sourcePaperIsCanonical : sourcePaper ≡ Sources.ecologyOfDataPaper
    sourceFeedbackFormalisation : OEF.OEFMultiFibreFeedbackHyperfabric
    sourceFeedbackFormalisationIsCanonical :
      sourceFeedbackFormalisation ≡ OEF.canonicalOEFMultiFibreFeedbackHyperfabric
    responsibilities : List CustodianResponsibility
    responsibilitiesAreCanonical :
      responsibilities ≡ canonicalCustodianResponsibilities
    ecologicalCell : EcologicalFeedbackCell
    ecologicalCellIsCanonical : ecologicalCell ≡ canonicalEcologicalFeedbackCell
    governance : CustodianshipGate
    governanceIsCanonical : governance ≡ canonicalCustodianshipGate
    feedbackIsEcologicalEvent : Bool
    feedbackIsEcologicalEventIsTrue : feedbackIsEcologicalEvent ≡ true
    codingNotWholeAnalysis : Bool
    codingNotWholeAnalysisIsTrue : codingNotWholeAnalysis ≡ true
    noContextFreeMeaning : Bool
    noContextFreeMeaningIsTrue : noContextFreeMeaning ≡ true
    noCustodianInfallibility : Bool
    noCustodianInfallibilityIsTrue : noCustodianInfallibility ≡ true
    reading : String

open EcologyOfDataHyperfabricBridge public

canonicalEcologyOfDataHyperfabricBridge : EcologyOfDataHyperfabricBridge
canonicalEcologyOfDataHyperfabricBridge =
  mkEcologyOfDataHyperfabricBridge
    Sources.ecologyOfDataPaper refl
    OEF.canonicalOEFMultiFibreFeedbackHyperfabric refl
    canonicalCustodianResponsibilities refl
    canonicalEcologicalFeedbackCell refl
    canonicalCustodianshipGate refl
    true refl
    true refl
    true refl
    true refl
    "The end-of-course comment is retained as an ecological event and local projection within a person-place hyperfabric. Custodianship requires system-edge, affordance, minutiae, value-flow and pedagogical-curation audits; it does not turn context-rich interpretation into infallible or complete meaning."
```

## DASHI/Biology/StudentVoiceEpistemicAgencyBridge.agda

Source: https://github.com/chboishabba/dashi_agda/blob/agent/digital-esd-source-crosspollination-20261101/DASHI/Biology/StudentVoiceEpistemicAgencyBridge.agda

Blob SHA: `f991f3ad5398b98bda0970493c5c54e693c98449`

```agda
module DASHI.Biology.StudentVoiceEpistemicAgencyBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.EducationCorpusSourceRegistry as Sources
import DASHI.Biology.OEFAIFeedbackFormalisation as OEF

------------------------------------------------------------------------
-- Student voice and epistemic agency correction.
--
-- The 2026 Brown/Kimber paper is not collapsed into the 2024 AI-feedback
-- paper.  It supplies a later methodological correction: soliciting feedback
-- alone does not make students co-producers of knowledge.

data Never : Set where

data EpistemicParticipationStage : Set where
  feedbackSourceStage : EpistemicParticipationStage
  questionContributorStage : EpistemicParticipationStage
  codingFrameContributorStage : EpistemicParticipationStage
  coInterpreterStage : EpistemicParticipationStage
  coDesignerStage : EpistemicParticipationStage
  evidenceReturnReviewerStage : EpistemicParticipationStage

canonicalEpistemicParticipationStages : List EpistemicParticipationStage
canonicalEpistemicParticipationStages =
  feedbackSourceStage
  ∷ questionContributorStage
  ∷ codingFrameContributorStage
  ∷ coInterpreterStage
  ∷ coDesignerStage
  ∷ evidenceReturnReviewerStage
  ∷ []

stageName : EpistemicParticipationStage → String
stageName feedbackSourceStage = "feedback source"
stageName questionContributorStage = "research-question contributor"
stageName codingFrameContributorStage = "coding-frame contributor"
stageName coInterpreterStage = "co-interpreter"
stageName coDesignerStage = "co-designer"
stageName evidenceReturnReviewerStage = "evidence-return reviewer"

data VoicePromotionRoute : Set where
  candidateEpistemicParticipationRoute : VoicePromotionRoute
  surveyEqualsVoiceRoute : VoicePromotionRoute
  feedbackEqualsAgencyRoute : VoicePromotionRoute
  researcherInterpretationEqualsCoProductionRoute : VoicePromotionRoute
  invitationEqualsPartnershipRoute : VoicePromotionRoute
  coDesignEqualsAutomaticJusticeRoute : VoicePromotionRoute

AdmissibleVoicePromotionRoute : VoicePromotionRoute → Set
AdmissibleVoicePromotionRoute candidateEpistemicParticipationRoute = ⊤
AdmissibleVoicePromotionRoute surveyEqualsVoiceRoute = Never
AdmissibleVoicePromotionRoute feedbackEqualsAgencyRoute = Never
AdmissibleVoicePromotionRoute researcherInterpretationEqualsCoProductionRoute = Never
AdmissibleVoicePromotionRoute invitationEqualsPartnershipRoute = Never
AdmissibleVoicePromotionRoute coDesignEqualsAutomaticJusticeRoute = Never

surveyEqualsVoiceBlocked :
  AdmissibleVoicePromotionRoute surveyEqualsVoiceRoute → Never
surveyEqualsVoiceBlocked ()

feedbackEqualsAgencyBlocked :
  AdmissibleVoicePromotionRoute feedbackEqualsAgencyRoute → Never
feedbackEqualsAgencyBlocked ()

researcherInterpretationEqualsCoProductionBlocked :
  AdmissibleVoicePromotionRoute researcherInterpretationEqualsCoProductionRoute → Never
researcherInterpretationEqualsCoProductionBlocked ()

invitationEqualsPartnershipBlocked :
  AdmissibleVoicePromotionRoute invitationEqualsPartnershipRoute → Never
invitationEqualsPartnershipBlocked ()

record EpistemicAgencyGate : Set where
  constructor mkEpistemicAgencyGate
  field
    studentsMayShapeQuestions : Bool
    studentsMayShapeQuestionsIsTrue : studentsMayShapeQuestions ≡ true
    studentsMayContestCodingFrame : Bool
    studentsMayContestCodingFrameIsTrue : studentsMayContestCodingFrame ≡ true
    studentsMayCoInterpretOutputs : Bool
    studentsMayCoInterpretOutputsIsTrue : studentsMayCoInterpretOutputs ≡ true
    studentsMayChooseOrRejectHandle : Bool
    studentsMayChooseOrRejectHandleIsTrue : studentsMayChooseOrRejectHandle ≡ true
    evidenceReturnedForReview : Bool
    evidenceReturnedForReviewIsTrue : evidenceReturnedForReview ≡ true
    participationNotForced : Bool
    participationNotForcedIsTrue : participationNotForced ≡ true

open EpistemicAgencyGate public

canonicalEpistemicAgencyGate : EpistemicAgencyGate
canonicalEpistemicAgencyGate =
  mkEpistemicAgencyGate
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl

record StudentVoiceEpistemicAgencyBridge : Set where
  constructor mkStudentVoiceEpistemicAgencyBridge
  field
    sourcePaper : Sources.PaperReference
    sourcePaperIsCanonical : sourcePaper ≡ Sources.voiceAgencyPaper
    priorAIFormalisation : OEF.OEFAIFeedbackFormalisation
    priorAIFormalisationIsCanonical :
      priorAIFormalisation ≡ OEF.canonicalOEFAIFeedbackFormalisation
    participationStages : List EpistemicParticipationStage
    participationStagesAreCanonical :
      participationStages ≡ canonicalEpistemicParticipationStages
    agencyGate : EpistemicAgencyGate
    agencyGateIsCanonical : agencyGate ≡ canonicalEpistemicAgencyGate
    route : VoicePromotionRoute
    routeIsCandidate : route ≡ candidateEpistemicParticipationRoute
    routeAdmissible : AdmissibleVoicePromotionRoute route
    laterPaperCorrectsExtractiveRisk : Bool
    laterPaperCorrectsExtractiveRiskIsTrue :
      laterPaperCorrectsExtractiveRisk ≡ true
    studentsRemainSituatedEpistemicAgents : Bool
    studentsRemainSituatedEpistemicAgentsIsTrue :
      studentsRemainSituatedEpistemicAgents ≡ true
    noAutomaticEpistemicAuthority : Bool
    noAutomaticEpistemicAuthorityIsTrue :
      noAutomaticEpistemicAuthority ≡ true
    reading : String

open StudentVoiceEpistemicAgencyBridge public

canonicalStudentVoiceEpistemicAgencyBridge :
  StudentVoiceEpistemicAgencyBridge
canonicalStudentVoiceEpistemicAgencyBridge =
  mkStudentVoiceEpistemicAgencyBridge
    Sources.voiceAgencyPaper refl
    OEF.canonicalOEFAIFeedbackFormalisation refl
    canonicalEpistemicParticipationStages refl
    canonicalEpistemicAgencyGate refl
    candidateEpistemicParticipationRoute refl tt
    true refl
    true refl
    true refl
    "Brown and Kimber's epistemic-expansion paper is retained as a methodological correction to feedback-only SoTL: students may participate in question formation, coding-frame contestation, interpretation, co-design and evidence return. Survey capture alone does not become voice or agency, and co-design does not automatically become just or representative."

SurveyNotVoice : Set
SurveyNotVoice =
  AdmissibleVoicePromotionRoute surveyEqualsVoiceRoute → Never

surveyNotVoiceProof : SurveyNotVoice
surveyNotVoiceProof = surveyEqualsVoiceBlocked
```

## DASHI/Biology/AliceBrownCorpusLoom.agda

Source: https://github.com/chboishabba/dashi_agda/blob/agent/digital-esd-source-crosspollination-20261101/DASHI/Biology/AliceBrownCorpusLoom.agda

Blob SHA: `e3d1a45fcaa10f441924655e9a6b867d60863b76`

```agda
module DASHI.Biology.AliceBrownCorpusLoom where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.EducationCorpusSourceRegistry as Sources
import DASHI.Biology.OEFAIFeedbackFormalisationFull as AI
import DASHI.Biology.HumourOnlineEngagementFramework as Humour
import DASHI.Biology.HumourEpistemicAgencyHyperfabricBridge as HumourAgency
import DASHI.Biology.StudentVoiceEpistemicAgencyBridge as Voice
import DASHI.Biology.StudentIdentifiedSupportStrategiesBridge as Strategies
import DASHI.Biology.EcologyOfDataHyperfabricBridge as Ecology
import DASHI.Biology.ParentAllyshipMultiObserverBridge as Allyship
import DASHI.Biology.ParentalFearIndependentMobilityExact as FearMobility
import DASHI.Biology.ParentalFearSourceAttributionExact as FearAttribution
import DASHI.Biology.ParentalFearObserverRefinementExact as FearObserver
import DASHI.Biology.ParentalFearConsumerSufficiencyBridgeExact as FearSufficiency
import DASHI.Biology.ParentalFearDynamicQuotientBridgeExact as FearDynamics
import DASHI.Biology.ParentalFearIntegratedFormalismExact as FearIntegrated
import DASHI.Biology.InterpretiveCodingSystem as Coding
import DASHI.Biology.CrossPaperDialecticalDevelopment as Development

------------------------------------------------------------------------
-- Corpus-level loom.
--
-- This aggregate preserves each source paper as its own fibre, while exposing
-- typed cross-paper relations and DASHI extensions.  It does not flatten the
-- corpus into one claimed theory or promote any author/paper to authority.
------------------------------------------------------------------------

record AliceBrownCorpusLoom : Set₁ where
  constructor mkAliceBrownCorpusLoom
  field
    sourceRegistry : Sources.EducationCorpusSourceRegistry
    sourceRegistryIsCanonical :
      sourceRegistry ≡ Sources.canonicalEducationCorpusSourceRegistry

    aiFeedbackFormalisation : AI.OEFAIFeedbackFormalisationFull
    aiFeedbackFormalisationIsCanonical :
      aiFeedbackFormalisation ≡ AI.canonicalOEFAIFeedbackFormalisationFull

    humourFramework : Humour.HumourFrameworkSourceSurface
    humourFrameworkIsCanonical :
      humourFramework ≡ Humour.canonicalHumourFrameworkSourceSurface

    humourEpistemicAgencyBridge :
      HumourAgency.HumourEpistemicAgencyHyperfabricBridge
    humourEpistemicAgencyBridgeIsCanonical :
      humourEpistemicAgencyBridge
      ≡ HumourAgency.canonicalHumourEpistemicAgencyHyperfabricBridge

    studentVoiceAgencyBridge : Voice.StudentVoiceEpistemicAgencyBridge
    studentVoiceAgencyBridgeIsCanonical :
      studentVoiceAgencyBridge ≡ Voice.canonicalStudentVoiceEpistemicAgencyBridge

    supportStrategiesBridge : Strategies.StudentIdentifiedSupportStrategiesBridge
    supportStrategiesBridgeIsCanonical :
      supportStrategiesBridge ≡
      Strategies.canonicalStudentIdentifiedSupportStrategiesBridge

    ecologyHyperfabricBridge : Ecology.EcologyOfDataHyperfabricBridge
    ecologyHyperfabricBridgeIsCanonical :
      ecologyHyperfabricBridge ≡ Ecology.canonicalEcologyOfDataHyperfabricBridge

    parentAllyshipBridge : Allyship.ParentAllyshipMultiObserverBridge
    parentAllyshipBridgeIsCanonical :
      parentAllyshipBridge ≡ Allyship.canonicalParentAllyshipMultiObserverBridge

    parentalFearMobilityBridge : FearMobility.ParentalFearEcologyBridge
    parentalFearMobilityBridgeIsCanonical :
      parentalFearMobilityBridge ≡ FearMobility.canonicalParentalFearEcologyBridge

    parentalFearAttribution : FearAttribution.ParentalFearSourceAttribution
    parentalFearAttributionIsCanonical :
      parentalFearAttribution ≡
      FearAttribution.canonicalParentalFearSourceAttribution

    parentalFearObserverRefinement :
      FearObserver.ParentalFearObserverRefinementBridge
    parentalFearObserverRefinementIsCanonical :
      parentalFearObserverRefinement ≡
      FearObserver.canonicalParentalFearObserverRefinementBridge

    parentalFearConsumerSufficiency :
      FearSufficiency.ParentalFearConsumerSufficiencyBridge
    parentalFearConsumerSufficiencyIsCanonical :
      parentalFearConsumerSufficiency ≡
      FearSufficiency.canonicalParentalFearConsumerSufficiencyBridge

    parentalFearDynamicQuotient :
      FearDynamics.ParentalFearDynamicQuotientBridge
    parentalFearDynamicQuotientIsCanonical :
      parentalFearDynamicQuotient ≡
      FearDynamics.canonicalParentalFearDynamicQuotientBridge

    parentalFearIntegratedFormalism :
      FearIntegrated.ParentalFearIntegratedFormalism
    parentalFearIntegratedFormalismIsCanonical :
      parentalFearIntegratedFormalism ≡
      FearIntegrated.canonicalParentalFearIntegratedFormalism

    interpretiveCodingSystem : Coding.InterpretiveCodingSystem
    interpretiveCodingSystemIsCanonical :
      interpretiveCodingSystem ≡ Coding.canonicalInterpretiveCodingSystem

    dialecticalDevelopment : Development.CrossPaperDialecticalDevelopment
    dialecticalDevelopmentIsCanonical :
      dialecticalDevelopment ≡
      Development.canonicalCrossPaperDialecticalDevelopment

    paperFibresNotFlattened : Bool
    paperFibresNotFlattenedIsTrue : paperFibresNotFlattened ≡ true

    sourceClaimsNotCrossPaperInferences : Bool
    sourceClaimsNotCrossPaperInferencesIsTrue :
      sourceClaimsNotCrossPaperInferences ≡ true

    crossPaperInferencesNotEmpiricalResults : Bool
    crossPaperInferencesNotEmpiricalResultsIsTrue :
      crossPaperInferencesNotEmpiricalResults ≡ true

    studentAndParentObserverFibresRemainDistinct : Bool
    studentAndParentObserverFibresRemainDistinctIsTrue :
      studentAndParentObserverFibresRemainDistinct ≡ true

    agencyAndCustodianshipGovernDownstreamUse : Bool
    agencyAndCustodianshipGovernDownstreamUseIsTrue :
      agencyAndCustodianshipGovernDownstreamUse ≡ true

    humourSourcePreservedBeforeDialecticalCorrection : Bool
    humourSourcePreservedBeforeDialecticalCorrectionIsTrue :
      humourSourcePreservedBeforeDialecticalCorrection ≡ true

    parentalFearSourcePreservedBeforeEcologyBridge : Bool
    parentalFearSourcePreservedBeforeEcologyBridgeIsTrue :
      parentalFearSourcePreservedBeforeEcologyBridge ≡ true

    parentalFearAttributionRetainedThroughExtensions : Bool
    parentalFearAttributionRetainedThroughExtensionsIsTrue :
      parentalFearAttributionRetainedThroughExtensions ≡ true

    parentalFearStaticAndDynamicNonDescentSeparated : Bool
    parentalFearStaticAndDynamicNonDescentSeparatedIsTrue :
      parentalFearStaticAndDynamicNonDescentSeparated ≡ true

    corpusLoomCandidateOnly : Bool
    corpusLoomCandidateOnlyIsTrue : corpusLoomCandidateOnly ≡ true

    reading : String

open AliceBrownCorpusLoom public

canonicalAliceBrownCorpusLoom : AliceBrownCorpusLoom
canonicalAliceBrownCorpusLoom =
  mkAliceBrownCorpusLoom
    Sources.canonicalEducationCorpusSourceRegistry refl
    AI.canonicalOEFAIFeedbackFormalisationFull refl
    Humour.canonicalHumourFrameworkSourceSurface refl
    HumourAgency.canonicalHumourEpistemicAgencyHyperfabricBridge refl
    Voice.canonicalStudentVoiceEpistemicAgencyBridge refl
    Strategies.canonicalStudentIdentifiedSupportStrategiesBridge refl
    Ecology.canonicalEcologyOfDataHyperfabricBridge refl
    Allyship.canonicalParentAllyshipMultiObserverBridge refl
    FearMobility.canonicalParentalFearEcologyBridge refl
    FearAttribution.canonicalParentalFearSourceAttribution refl
    FearObserver.canonicalParentalFearObserverRefinementBridge refl
    FearSufficiency.canonicalParentalFearConsumerSufficiencyBridge refl
    FearDynamics.canonicalParentalFearDynamicQuotientBridge refl
    FearIntegrated.canonicalParentalFearIntegratedFormalism refl
    Coding.canonicalInterpretiveCodingSystem refl
    Development.canonicalCrossPaperDialecticalDevelopment refl
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
    "Corpus-level candidate loom: the OEF/AI paper supplies scalable proxy classification; the source-bound humour paper supplies a seven-consideration teacher-side pedagogical framework; the humour/agency hyperfabric bridge exposes constitutive governance without rewriting the source; voice/agency supplies epistemic-participation gates; online-support research supplies student-identified support families; ecology-of-data supplies person-place custodianship; dyslexia allyship research supplies plural observer and proximity fibres; the parental fear/IAST study supplies a situated reciprocal negotiation model whose O'Connor/Brown 2013 Health & Place attribution and DOI remain first-class. Its observer bridge constructs a coarse-fear collision, the generic consumer-descent owner proves fear-only insufficiency and factorization failure for intervention need, the generic dynamic-quotient owner gives a distinct synthetic terminalisation defect, and ParentalFearIntegratedFormalismExact packages source, provenance, ecology, static observer mathematics, consumer sufficiency and dynamic safety into one canonical object. Source claims, cross-paper inferences, static DASHI theorems, dynamic DASHI countermodels and future empirical tests remain distinct."

canonicalCorpusLoomSourceCountReading : String
canonicalCorpusLoomSourceCountReading =
  "nine source-bound papers/items with title, authors, DOI-or-explicit-no-DOI, venue and boundary metadata"
```

