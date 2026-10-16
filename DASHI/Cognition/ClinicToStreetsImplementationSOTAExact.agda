module DASHI.Cognition.ClinicToStreetsImplementationSOTAExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- IMPLEMENTATION-FIDELITY SOTA
--
-- These sources address implementability, feasibility, acceptability,
-- fidelity, structural-clinical practice design, or small-sample clinical
-- utility.  They do not establish comparative efficacy or patient outcome
-- benefit unless their own design does so.
------------------------------------------------------------------------

data ImplementationEvidenceRole : Set where
  largeScaleCFIImplementationStudy : ImplementationEvidenceRole
  adolescentCFIPilotStudy : ImplementationEvidenceRole
  vocationalCFIPilotStudy : ImplementationEvidenceRole
  structuralCompetencyInterventionDesign : ImplementationEvidenceRole

data ImplementationEvidenceCeiling : Set where
  implementationBarrierEvidence : ImplementationEvidenceCeiling
  smallSampleFeasibilityUtilityEvidence : ImplementationEvidenceCeiling
  interventionDesignDescription : ImplementationEvidenceCeiling

record ImplementationEvidenceEntry : Set where
  constructor implementation-evidence-entry
  field
    source : Source.AttributedSource
    role : ImplementationEvidenceRole
    ceiling : ImplementationEvidenceCeiling
    claimReference : String

open ImplementationEvidenceEntry public

silviusAntezanaGhane2024 : Source.AttributedSource
silviusAntezanaGhane2024 = Source.mkDOISource
  "Linda Silvius, Katrina V. Antezana J., Samrad Ghane"
  "Symptom vs context: lessons learned from a large-scale implementation of the Cultural Formulation Interview"
  "Frontiers in Psychiatry 15:1410865"
  "2024"
  "10.3389/fpsyt.2024.1410865"
  "https://www.frontiersin.org/journals/psychiatry/articles/10.3389/fpsyt.2024.1410865/full"
  Source.academicArticleSource
  "Large-service implementation study. Preliminary organization-wide use was 13.2% of intakes; survey and intake analyses identified familiarity, perceived value, minority-only framing, and clinician cultural competence as implementation-relevant coordinates. This pays implementation/barrier evidence only, not CFI efficacy or patient outcome benefit."
  Source.publicAttribution

svamoDeMarinisHaug2026 : Source.AttributedSource
svamoDeMarinisHaug2026 = Source.mkDOISource
  "Nina Therese Øversveen Svamo, Valerie DeMarinis, Sigrid Helene Kjørven Haug"
  "Efficacy pilot study of the DSM-5 Cultural Formulation Interview in a specialized mental healthcare inpatient unit for adolescents in Norway"
  "Frontiers in Psychiatry 16:1595131"
  "2026"
  "10.3389/fpsyt.2025.1595131"
  "https://www.frontiersin.org/journals/psychiatry/articles/10.3389/fpsyt.2025.1595131/full"
  Source.academicArticleSource
  "Mixed-methods pilot with six adolescents and CFI-trained clinicians evaluating feasibility, acceptability, clinical utility and fidelity. Positive pilot findings remain small-sample feasibility/utility evidence; they do not establish comparative treatment efficacy or general service-wide implementability."
  Source.publicAttribution

haugDeMarinis2026 : Source.AttributedSource
haugDeMarinis2026 = Source.mkDOISource
  "Sigrid Helene Kjørven Haug, Valerie DeMarinis"
  "Efficacy testing of the DSM-5 Cultural Formulation Interview for patients in vocational rehabilitation in Norway"
  "Frontiers in Psychiatry 16:1546150"
  "2026"
  "10.3389/fpsyt.2025.1546150"
  "https://www.frontiersin.org/journals/psychiatry/articles/10.3389/fpsyt.2025.1546150/full"
  Source.academicArticleSource
  "Mixed-methods six-patient vocational-rehabilitation study following CFI information through treatment. Reports high fidelity and qualitative usefulness/reflection signals; small sample and noncomparative design do not establish comparative efficacy or broad implementation success."
  Source.publicAttribution

siberSanderowitzEtAl2022 : Source.AttributedSource
siberSanderowitzEtAl2022 = Source.mkDOISource
  "Shaina Siber-Sanderowitz, Allison Glasgow, Tara Chouake, Elizabeth Beckford, Amy Nim, Ana Ozdoba"
  "Developing a Structural Intervention for Outpatient Mental Health Care: Mapping Vulnerability and Privilege"
  "American Journal of Psychotherapy 75(3):134-140"
  "2022"
  "10.1176/appi.psychotherapy.20200057"
  "https://pubmed.ncbi.nlm.nih.gov/35903912/"
  Source.academicArticleSource
  "Describes development of the MVP structural-competency exercise for structural humility, assessment/formulation, treatment planning and structural action. Development/design role only here; the article does not establish comparative clinical outcome efficacy."
  Source.publicAttribution

implementationSources : List Source.AttributedSource
implementationSources =
  silviusAntezanaGhane2024 ∷
  svamoDeMarinisHaug2026 ∷
  haugDeMarinis2026 ∷
  siberSanderowitzEtAl2022 ∷ []

implementationSourceCount : Nat
implementationSourceCount = Source.sourceCount implementationSources

implementationAtlas : Source.AttributedSourceAtlas
implementationAtlas = Source.mkSourceAtlas
  "Clinic-to-Streets implementation-fidelity SOTA atlas"
  "DASHI.Cognition.ClinicToStreetsImplementationSOTAExact"
  implementationSources
  "Implementation, feasibility, fidelity and structural-practice design evidence. Large-scale adoption barriers, small-pilot utility, and intervention design remain distinct from comparative efficacy and patient outcome effects."

implementationEntries : List ImplementationEvidenceEntry
implementationEntries =
  implementation-evidence-entry silviusAntezanaGhane2024 largeScaleCFIImplementationStudy implementationBarrierEvidence "organization-wide uptake, familiarity, perceived relevance, clinician competence and documentation fidelity" ∷
  implementation-evidence-entry svamoDeMarinisHaug2026 adolescentCFIPilotStudy smallSampleFeasibilityUtilityEvidence "adolescent feasibility, acceptability, utility and fidelity" ∷
  implementation-evidence-entry haugDeMarinis2026 vocationalCFIPilotStudy smallSampleFeasibilityUtilityEvidence "vocational-rehabilitation CFI fidelity and treatment-process utility" ∷
  implementation-evidence-entry siberSanderowitzEtAl2022 structuralCompetencyInterventionDesign interventionDesignDescription "MVP structural humility/formulation/action intervention design" ∷ []

record ImplementationSOTABoundary : Set where
  constructor implementation-sota-boundary
  field
    implementationEvidenceKeptSeparateFromOutcomeEfficacy : Bool
    uptakeKeptSeparateFromFidelity : Bool
    fidelityKeptSeparateFromPatientBenefit : Bool
    pilotUtilityKeptSeparateFromComparativeEfficacy : Bool
    interventionDesignKeptSeparateFromMeasuredEffect : Bool
    largeScaleCFIImplementationEstablishesOutcomeBenefit : Bool
    smallPilotUtilityEstablishesComparativeEfficacy : Bool
    mvpDesignEstablishesClinicalOutcomeEffect : Bool
    lowUptakeEstablishesToolInefficacy : Bool
    highFidelityEstablishesTruth : Bool

open ImplementationSOTABoundary public

canonicalImplementationSOTABoundary : ImplementationSOTABoundary
canonicalImplementationSOTABoundary =
  implementation-sota-boundary
    true true true true true
    false false false false false

data ImplementationUptakeProvesOutcome : Set where
data SmallPilotProvesComparativeEfficacy : Set where
data MVPDesignProvesOutcome : Set where

implementationUptakeDoesNotProveOutcome : ImplementationUptakeProvesOutcome → ⊥
implementationUptakeDoesNotProveOutcome ()

smallPilotDoesNotProveComparativeEfficacy : SmallPilotProvesComparativeEfficacy → ⊥
smallPilotDoesNotProveComparativeEfficacy ()

mvpDesignDoesNotProveOutcome : MVPDesignProvesOutcome → ⊥
mvpDesignDoesNotProveOutcome ()
