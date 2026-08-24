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