module DASHI.Cognition.ClinicToStreetsSOTAEvidenceAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.TraumaNarrativeEvidenceBoundaryExact as Trauma
import DASHI.Law.SensibLawExpertEvidenceSituatedObserverExact as Situated

------------------------------------------------------------------------
-- CLINIC-TO-STREETS SOTA EVIDENCE ATLAS
--
-- Claim-relative surrounding literature for the Clinic-to-Streets programme.
-- Source identity, intellectual/theoretical role, empirical design and causal
-- authority remain distinct.  In particular, no literature item below turns
-- the theoretical phrase "therapy/counterinsurgency" into an empirical effect
-- or an intent finding.
------------------------------------------------------------------------

data ClinicEvidenceRole : Set where
  revolutionaryPsychoanalyticTheory : ClinicEvidenceRole
  structuralDeterminantsReview : ClinicEvidenceRole
  therapyPracticeSynthesis : ClinicEvidenceRole
  clinicalFormulationReview : ClinicEvidenceRole
  socioculturalFormulationFramework : ClinicEvidenceRole
  criticalLiberationFramework : ClinicEvidenceRole
  epistemicInjusticeAnalysis : ClinicEvidenceRole
  discriminationCausalMetaAnalysis : ClinicEvidenceRole
  familyMediationLongitudinalTrialAnalysis : ClinicEvidenceRole
  politicizedHealingQualitativeStudy : ClinicEvidenceRole
  counselingGroundedTheoryStudy : ClinicEvidenceRole

data ClinicEvidenceCeiling : Set where
  theoryFrameworkOnly : ClinicEvidenceCeiling
  reviewLevelEmpiricalPrior : ClinicEvidenceCeiling
  clinicalUsefulnessReview : ClinicEvidenceCeiling
  immediateExperimentalEffect : ClinicEvidenceCeiling
  longitudinalMediationSpecific : ClinicEvidenceCeiling
  qualitativePracticeEvidence : ClinicEvidenceCeiling

record ClinicEvidenceEntry : Set where
  constructor clinic-evidence-entry
  field
    source : Source.AttributedSource
    role : ClinicEvidenceRole
    ceiling : ClinicEvidenceCeiling
    claimReference : String

open ClinicEvidenceEntry public

sheehi2026 : Source.AttributedSource
sheehi2026 = Source.mkDOISource
  "Lara Sheehi"
  "From the Clinic to the Streets: Psychoanalysis for Revolutionary Futures"
  "Pluto Press / JSTOR"
  "2026"
  "10.2307/jj.33676841"
  "https://www.jstor.org/stable/jj.33676841"
  Source.academicBookSource
  "Primary theoretical programme for warfare psychologically waged, psychic intrusions, reskilling, psychic militancy and the psycho-politico-affective framing. This source does not by itself identify an empirical clinical effect, establish causal magnitude, or establish practitioner/institutional intent."
  Source.publicAttribution

kirkbrideEtAl2024 : Source.AttributedSource
kirkbrideEtAl2024 = Source.mkDOISource
  "James B. Kirkbride et al."
  "The social determinants of mental health and disorder: evidence, prevention and recommendations"
  "World Psychiatry 23(1):58-90"
  "2024"
  "10.1002/wps.21160"
  "https://onlinelibrary.wiley.com/doi/10.1002/wps.21160"
  Source.academicArticleSource
  "High-level review supporting structural/social determinants as important contributors to mental-health outcomes across the life course and motivating upstream prevention. It is not evidence for Sheehi's specific counterinsurgency thesis."
  Source.publicAttribution

pauling2023 : Source.AttributedSource
pauling2023 = Source.mkDOISource
  "Naomi Pauling"
  "Addressing social determinants of mental health in therapy: A thematic synthesis"
  "Counselling and Psychotherapy Research 23(4):982-994"
  "2023"
  "10.1002/capr.12672"
  "https://onlinelibrary.wiley.com/doi/10.1002/capr.12672"
  Source.academicArticleSource
  "Qualitative systematic/thematic synthesis of practice research addressing social determinants in therapy. It identified a small evidence base and themes around therapeutic relationship, adapting to client context, and community as a resource; it does not prove a universal treatment effect or political mechanism."
  Source.publicAttribution

aggarwal2024 : Source.AttributedSource
aggarwal2024 = Source.mkDOISource
  "Neil Krishan Aggarwal"
  "The Cultural Formulation Interview in Case Formulations: A State-of-the-Science Review"
  "Behavior Therapy 55(6):1130-1143"
  "2024"
  "10.1016/j.beth.2024.05.009"
  "https://pubmed.ncbi.nlm.nih.gov/39443057/"
  Source.academicArticleSource
  "State-of-the-science review: cultural/social-context information can contribute to differential diagnosis and treatment planning; ten of twelve included studies reported usefulness for clinical tasks. More research is required on how the CFI changes case formulation."
  Source.publicAttribution

weissEtAl2024 : Source.AttributedSource
weissEtAl2024 = Source.mkDOISource
  "Mitchell G. Weiss, Ankita Deshmukh, Sanjeev B. Sarmukaddam, Vasudeo P. Paralikar"
  "Sociocultural Framework for Psychiatric Case Formulation"
  "Journal of Nervous & Mental Disease 212(1):16-27"
  "2024"
  "10.1097/NMD.0000000000001721"
  "https://doi.org/10.1097/NMD.0000000000001721"
  Source.academicArticleSource
  "Clinical formulation framework motivated partly by structural omissions in existing cultural formulation. Supports a candidate formulation architecture, not universal superiority or a causal outcome estimate."
  Source.publicAttribution

morrillComasDiaz2025 : Source.AttributedSource
morrillComasDiaz2025 = Source.mkDOISource
  "Zenobia Morrill and Lillian Comas-Díaz"
  "Critical-liberation psychotherapy: Unsettling hegemonic power toward liberatory practice"
  "American Psychologist 80(4):576-588"
  "2025"
  "10.1037/amp0001444"
  "https://pubmed.ncbi.nlm.nih.gov/40549612/"
  Source.academicArticleSource
  "Contemporary critical-liberation psychotherapy framework emphasizing power, decolonial and intersectional context. Framework/theoretical role only here; citation does not establish comparative clinical efficacy."
  Source.publicAttribution

drozdzowiczGrodniewicz2025 : Source.AttributedSource
drozdzowiczGrodniewicz2025 = Source.mkDOISource
  "Anna Drożdżowicz and J.P. Grodniewicz"
  "Epistemic injustice and psychotherapy"
  "Philosophical Psychology"
  "2025"
  "10.1080/09515089.2025.2519320"
  "https://www.tandfonline.com/doi/full/10.1080/09515089.2025.2519320"
  Source.academicArticleSource
  "Conceptual analysis of testimonial, hermeneutical and participatory epistemic injustice risks in psychotherapy and their relation to self-understanding. It characterizes possible harms; it does not provide prevalence or causal effect estimates."
  Source.publicAttribution

emmerDornMata2024 : Source.AttributedSource
emmerDornMata2024 = Source.mkDOISource
  "Christine Emmer, Julia Dorn, Jutta Mata"
  "The immediate effect of discrimination on mental health: A meta-analytic review of the causal evidence"
  "Psychological Bulletin 150(3):215-252"
  "2024"
  "10.1037/bul0000419"
  "https://pubmed.ncbi.nlm.nih.gov/38330346/"
  Source.academicArticleSource
  "Meta-analysis of randomized discrimination-manipulation studies (73 studies, 12,097 participants) supporting immediate adverse mental-health effects under the included experimental paradigms. This is not a psychotherapy-effect study."
  Source.publicAttribution

burkinaFamilyStress2025 : Source.AttributedSource
burkinaFamilyStress2025 = Source.mkDOISource
  "Leyla Karimli, Leyla Ismayilova, Christine R. Wells"
  "Pathways From Poverty to Child Mental Health in Burkina Faso: Longitudinal Mediation Analyses in a Cluster-Randomized Clinical Trial"
  "Journal of Adolescent Health 76(3):415-428"
  "2025"
  "10.1016/j.jadohealth.2024.10.030"
  "https://pubmed.ncbi.nlm.nih.gov/39692681/"
  Source.academicArticleSource
  "Longitudinal mediation analysis in a cluster-randomized trial examining family-level pathways linking poverty-reduction intervention and child mental-health outcomes. Supports the empirical legitimacy of a structural/exposure -> family mediator -> mental-health causal shape in this specific study, not a universal family mechanism."
  Source.publicAttribution

pattersonMarkowitz2025 : Source.AttributedSource
pattersonMarkowitz2025 = Source.mkDOISource
  "Rebecca Patterson-Markowitz"
  "On the therapist's couch and in the streets: Politicized approaches to healing trauma and embodying liberation in the US and Canada"
  "Political Geography 121:103367"
  "2025"
  "10.1016/j.polgeo.2025.103367"
  "https://www.sciencedirect.com/science/article/pii/S096262982500099X"
  Source.academicArticleSource
  "Qualitative study of politicized-healing frameworks and practices, including the tension that healing can support collective transformation while also risking re-individualization and obscuring state responsibility. Qualitative/practice evidence only; not a causal psychotherapy trial."
  Source.publicAttribution

boydHaysJones2025 : Source.AttributedSource
boydHaysJones2025 = Source.mkDOISource
  "Danielle Pester Boyd, Danica G. Hays, Laura K. Jones"
  "Assessing and Addressing Social Determinants of Mental Health in Counseling: A Grounded Theory Investigation"
  "Journal of Counseling & Development 103(4):469-483"
  "2025"
  "10.1002/jcad.70003"
  "https://onlinelibrary.wiley.com/doi/10.1002/jcad.70003"
  Source.academicArticleSource
  "Grounded-theory study of 20 professional counselors self-identifying with SDMH expertise. Produces a practice model including broaching SDMH, cultural competence, contextualizing interventions, client self-advocacy and community-embedded resources. Qualitative model-building evidence, not comparative efficacy or causal outcome proof."
  Source.publicAttribution

clinicSOTASources : List Source.AttributedSource
clinicSOTASources =
  sheehi2026 ∷
  kirkbrideEtAl2024 ∷
  pauling2023 ∷
  aggarwal2024 ∷
  weissEtAl2024 ∷
  morrillComasDiaz2025 ∷
  drozdzowiczGrodniewicz2025 ∷
  emmerDornMata2024 ∷
  burkinaFamilyStress2025 ∷
  pattersonMarkowitz2025 ∷
  boydHaysJones2025 ∷ []

sotaSourceCount : Nat
sotaSourceCount = Source.sourceCount clinicSOTASources

clinicSOTAAtlas : Source.AttributedSourceAtlas
clinicSOTAAtlas = Source.mkSourceAtlas
  "Clinic-to-Streets surrounding SOTA atlas"
  "DASHI.Cognition.ClinicToStreetsSOTAEvidenceAtlasExact"
  clinicSOTASources
  "Claim-relative surrounding sources. Structural-determinants, discrimination, family-mediation and formulation studies provide empirical priors at their own designs; liberation, politicized-healing, epistemic-injustice and Sheehi sources retain framework/theoretical/qualitative roles. No source is promoted beyond its own object and design."

clinicEvidenceEntries : List ClinicEvidenceEntry
clinicEvidenceEntries =
  clinic-evidence-entry sheehi2026 revolutionaryPsychoanalyticTheory theoryFrameworkOnly "Sheehi theoretical programme" ∷
  clinic-evidence-entry kirkbrideEtAl2024 structuralDeterminantsReview reviewLevelEmpiricalPrior "structural/social determinants -> mental-health prior" ∷
  clinic-evidence-entry pauling2023 therapyPracticeSynthesis reviewLevelEmpiricalPrior "addressing social determinants in therapy/practice synthesis" ∷
  clinic-evidence-entry aggarwal2024 clinicalFormulationReview clinicalUsefulnessReview "contextual information -> formulation/diagnostic/treatment-planning use" ∷
  clinic-evidence-entry weissEtAl2024 socioculturalFormulationFramework theoryFrameworkOnly "structural context in sociocultural formulation" ∷
  clinic-evidence-entry morrillComasDiaz2025 criticalLiberationFramework theoryFrameworkOnly "critical-liberation psychotherapy framework" ∷
  clinic-evidence-entry drozdzowiczGrodniewicz2025 epistemicInjusticeAnalysis theoryFrameworkOnly "epistemic injustice risks in psychotherapy" ∷
  clinic-evidence-entry emmerDornMata2024 discriminationCausalMetaAnalysis immediateExperimentalEffect "manipulated discrimination -> immediate mental-health effects" ∷
  clinic-evidence-entry burkinaFamilyStress2025 familyMediationLongitudinalTrialAnalysis longitudinalMediationSpecific "poverty/intervention -> family mediator -> child mental-health pathway" ∷
  clinic-evidence-entry pattersonMarkowitz2025 politicizedHealingQualitativeStudy qualitativePracticeEvidence "politicized healing and individualization/collective-justice tension" ∷
  clinic-evidence-entry boydHaysJones2025 counselingGroundedTheoryStudy qualitativePracticeEvidence "SDMH assessment/contextualization/self-advocacy/community-resource practice model" ∷ []

------------------------------------------------------------------------
-- Existing empirical/situated boundaries reused rather than reimplemented.
------------------------------------------------------------------------

traumaNarrativeEvidenceBoundary : Trauma.TraumaNarrativeEvidenceBoundary
traumaNarrativeEvidenceBoundary = Trauma.canonicalTraumaNarrativeEvidenceBoundary

situatedObserverBoundary : Situated.ExpertSituatedObserverBoundary
situatedObserverBoundary = Situated.canonicalExpertSituatedObserverBoundary

record ClinicSOTABoundary : Set where
  constructor clinic-sota-boundary
  field
    attributedSourceCoreReused : Bool
    structuralDeterminantsEmpiricalPriorRetained : Bool
    formulationContextEvidenceRetained : Bool
    discriminationCausalEvidenceRetainedAtOwnObject : Bool
    familyMediationEvidenceRetainedAtOwnObject : Bool
    liberationSourcesRetainedAsFrameworkEvidence : Bool
    epistemicInjusticeRetainedAsConceptualAnalysis : Bool
    counselingPracticeEvidenceRetainedAsQualitativeModel : Bool
    traumaNarrativeEvidenceBoundaryReused : Bool
    situatedObserverBoundaryReused : Bool
    sheehiTheoryEstablishesEmpiricalCounterinsurgency : Bool
    structuralDeterminantsEvidenceEstablishesTherapyCounterinsurgency : Bool
    liberationFrameworkEstablishesComparativeEfficacy : Bool
    qualitativePoliticizedHealingEstablishesCausalTreatmentEffect : Bool
    counselingGroundedTheoryEstablishesComparativeEfficacy : Bool
    narrativeClarityCreatesTruth : Bool
    narrativeFragmentationCreatesFalsity : Bool
    confusionCreatesManipulationFinding : Bool
    contextualFormulationCreatesTruth : Bool

open ClinicSOTABoundary public

canonicalClinicSOTABoundary : ClinicSOTABoundary
canonicalClinicSOTABoundary =
  clinic-sota-boundary
    true true true true true true true true true true
    false false false false false false false false false

------------------------------------------------------------------------
-- Explicit bad-promotion propositions.
------------------------------------------------------------------------

data SheehiTheoryProvesEmpiricalCounterinsurgency : Set where
data StructuralDeterminantsProveTherapyCounterinsurgency : Set where
data LiberationFrameworkProvesComparativeEfficacy : Set where
data QualitativeHealingProvesCausalTreatmentEffect : Set where
data CounselingGroundedTheoryProvesComparativeEfficacy : Set where
data NarrativeClarityProvesTruth : Set where
data ConfusionProvesManipulation : Set where

sheehiTheoryDoesNotProveEmpiricalCounterinsurgency :
  SheehiTheoryProvesEmpiricalCounterinsurgency → ⊥
sheehiTheoryDoesNotProveEmpiricalCounterinsurgency ()

structuralDeterminantsDoNotProveTherapyCounterinsurgency :
  StructuralDeterminantsProveTherapyCounterinsurgency → ⊥
structuralDeterminantsDoNotProveTherapyCounterinsurgency ()

liberationFrameworkDoesNotProveComparativeEfficacy :
  LiberationFrameworkProvesComparativeEfficacy → ⊥
liberationFrameworkDoesNotProveComparativeEfficacy ()

qualitativeHealingDoesNotProveCausalTreatmentEffect :
  QualitativeHealingProvesCausalTreatmentEffect → ⊥
qualitativeHealingDoesNotProveCausalTreatmentEffect ()

counselingGroundedTheoryDoesNotProveComparativeEfficacy :
  CounselingGroundedTheoryProvesComparativeEfficacy → ⊥
counselingGroundedTheoryDoesNotProveComparativeEfficacy ()

narrativeClarityDoesNotProveTruth : NarrativeClarityProvesTruth → ⊥
narrativeClarityDoesNotProveTruth ()

confusionDoesNotProveManipulation : ConfusionProvesManipulation → ⊥
confusionDoesNotProveManipulation ()
