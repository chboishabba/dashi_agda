module DASHI.Education.DigitalESDStudyIntersectionalAbsenceAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Education.EarlyLearningIntersectionalCapabilityExact as Situated
import DASHI.Cognition.PNF.TraumaMemoryHypervoxelBridge as Trauma
import DASHI.Education.DigitalESDExternalityIncidenceAuditExact as Incidence

------------------------------------------------------------------------
-- STUDY-LEVEL INTERSECTIONAL ABSENCE AUDIT
--
-- This is an audit overlay, not a demographic ontology or a claim that every
-- source must measure every identity axis.  For each study it asks which people
-- are represented, absent, structurally filtered, unable to disclose/access,
-- affected but unsampled, or denied interpretive/governance authority.
--
-- The motivating transcript question is "who's not at the table?".  The
-- disability literature below is retained as exact source evidence that online
-- flexibility and digital access can coexist with exclusion, support failure,
-- stigma and severe under-representation of some disability groups.
------------------------------------------------------------------------

krazinskiFoleyDisabledOnlineSource : Attr.AttributedSource
krazinskiFoleyDisabledOnlineSource =
  Attr.mkDOISource
    "Meaghan Krazinski; Alan Foley"
    "Intersections of Marginalization and Possibility: A Phenomenological Analysis of Disabled Students' Experiences with Online Learning"
    "Journal of Disability Studies in Education 4(1):98-126"
    "2024"
    "10.1163/25888803-bja10026"
    "https://doi.org/10.1163/25888803-bja10026"
    Attr.academicArticleSource
    "Intersectional Critical Disability Studies / queer-phenomenology interview source. Supports source-bounded disabled-student experience claims about online-learning barriers, support and inclusion; does not establish prevalence or universal digital-education effects."
    Attr.publicAttribution

lynchBruntonFarrellReviewSource : Attr.AttributedSource
lynchBruntonFarrellReviewSource =
  Attr.mkDOISource
    "Sinead Lynch; James Brunton; Orna Farrell"
    "Experiences of disabled students in online education: a systematic review"
    "Distance Education"
    "2025"
    "10.1080/01587919.2025.2562802"
    "https://doi.org/10.1080/01587919.2025.2562802"
    Attr.academicArticleSource
    "PRISMA systematic-review source of 14 studies on disabled students in online higher education. Reports strong under-representation of neurodivergent and intellectually disabled students and retains disability-model differences; review synthesis does not create a pooled causal effect."
    Attr.publicAttribution

chidlowHiddenDisabilitySource : Attr.AttributedSource
chidlowHiddenDisabilitySource =
  Attr.mkDOISource
    "Stewart Chidlow; Charlemagne Blyth; Keren Coney; Vicci Boyd; Philippa McCabe"
    "Lessons from a pandemic: how can we use disabled students experiences of online learning to develop more inclusive models of teaching?"
    "International Journal of Inclusive Education"
    "2025"
    "10.1080/13603116.2025.2551754"
    "https://doi.org/10.1080/13603116.2025.2551754"
    Attr.academicArticleSource
    "Mixed quantitative/qualitative survey source: 96 respondents with hidden disabilities at one UK university, including declared and non-declared disability. Supports context-bounded accessibility/flexibility/exclusion claims; does not establish population prevalence or universal blended-learning superiority."
    Attr.publicAttribution

unescoDisabilityTechnologyBriefSource : Attr.AttributedSource
unescoDisabilityTechnologyBriefSource =
  Attr.mkNoDOISource
    "Global Education Monitoring Report Team"
    "Learners with disabilities and technology: Advocacy brief"
    "UNESCO Global Education Monitoring Report"
    "2024"
    "https://www.unesco.org/en/articles/learners-disabilities-and-technology-advocacy-brief"
    Attr.institutionalSource
    "Institutional disability/accessibility source derived from the 2023 GEM technology-in-education evidence base. Supports accessibility, affordability, teacher-capacity and learner-centred governance questions; does not create a same-object intervention effect."
    Attr.publicAttribution

disabilitySources : List Attr.AttributedSource
disabilitySources =
  krazinskiFoleyDisabledOnlineSource
  ∷ lynchBruntonFarrellReviewSource
  ∷ chidlowHiddenDisabilitySource
  ∷ unescoDisabilityTechnologyBriefSource
  ∷ []

disabilitySourceCount : Nat
disabilitySourceCount = 4

data AbsenceAuditQuestion : Set where
  whoWasSampled : AbsenceAuditQuestion
  whoWasEligibleButMissing : AbsenceAuditQuestion
  whoWasExcludedByDesign : AbsenceAuditQuestion
  whoCouldNotAccessParticipation : AbsenceAuditQuestion
  whoHadToDiscloseToBeCounted : AbsenceAuditQuestion
  whoWasAffectedButUnsampled : AbsenceAuditQuestion
  whichIntersectionsWereUnreported : AbsenceAuditQuestion
  whoDefinedTheCategories : AbsenceAuditQuestion
  whoInterpretedTheEvidence : AbsenceAuditQuestion
  whoHadDecisionAuthority : AbsenceAuditQuestion
  whoseFutureOptionsWereAffected : AbsenceAuditQuestion

absenceAuditQuestions : List AbsenceAuditQuestion
absenceAuditQuestions =
  whoWasSampled
  ∷ whoWasEligibleButMissing
  ∷ whoWasExcludedByDesign
  ∷ whoCouldNotAccessParticipation
  ∷ whoHadToDiscloseToBeCounted
  ∷ whoWasAffectedButUnsampled
  ∷ whichIntersectionsWereUnreported
  ∷ whoDefinedTheCategories
  ∷ whoInterpretedTheEvidence
  ∷ whoHadDecisionAuthority
  ∷ whoseFutureOptionsWereAffected
  ∷ []

absenceAuditQuestionCount : Nat
absenceAuditQuestionCount = 11

questionReading : AbsenceAuditQuestion → String
questionReading whoWasSampled = "who is literally represented in the analytic carrier?"
questionReading whoWasEligibleButMissing = "who could have belonged to the target population but is absent from the realised sample/corpus?"
questionReading whoWasExcludedByDesign = "which eligibility, language, platform, disclosure, location or methodological choices structurally excluded people?"
questionReading whoCouldNotAccessParticipation = "who lacked usable disability access, connectivity, device access, time, safety, language or support needed to participate?"
questionReading whoHadToDiscloseToBeCounted = "which people had to disclose disability, need or identity to become visible to the study or support system?"
questionReading whoWasAffectedButUnsampled = "which learners, families, workers, communities or future parties bear consequences without being study participants?"
questionReading whichIntersectionsWereUnreported = "which combinations of disability/access, age, place, language, care/labour, class or institutional relation remain unobserved?"
questionReading whoDefinedTheCategories = "who defined disability, engagement, success, sustainability, inclusion and outcome categories?"
questionReading whoInterpretedTheEvidence = "whose interpretation enters the analysis, and whose testimony or counter-interpretation is absent?"
questionReading whoHadDecisionAuthority = "who could change the intervention, platform, procurement, support or downstream use?"
questionReading whoseFutureOptionsWereAffected = "whose later participation, exit, repair, learning or intergenerational options are changed by the decision?"

------------------------------------------------------------------------
-- Reuse canonical situated/access and trauma authority boundaries.
------------------------------------------------------------------------

situatedCapabilityReading : String
situatedCapabilityReading = Situated.intersectionalCapabilityReading

traumaAuthorityBoundary : Trauma.TraumaMemoryHypervoxelAuthorityBoundary
traumaAuthorityBoundary = Trauma.canonicalTraumaMemoryHypervoxelAuthorityBoundary

externalityBoundary : Incidence.ExternalityIncidenceBoundary
externalityBoundary = Incidence.canonicalExternalityIncidenceBoundary

------------------------------------------------------------------------
-- Constructive collision: the same aggregate n cannot recover whether the
-- study's realised carrier captures the representation needed by its consumer.
------------------------------------------------------------------------

data RepresentationWorld : Set where
  sameNDisclosureFiltered : RepresentationWorld
  sameNAccessAndNondisclosureAudited : RepresentationWorld

data ReportedSampleSizeSurface : Set where
  sameReportedN : ReportedSampleSizeSurface

sampleSizeProjection : RepresentationWorld → ReportedSampleSizeSurface
sampleSizeProjection sameNDisclosureFiltered = sameReportedN
sampleSizeProjection sameNAccessAndNondisclosureAudited = sameReportedN

representationAdequacy : RepresentationWorld → Bool
representationAdequacy sameNDisclosureFiltered = false
representationAdequacy sameNAccessAndNondisclosureAudited = true

representationDiffers :
  representationAdequacy sameNDisclosureFiltered ≡
  representationAdequacy sameNAccessAndNondisclosureAudited → ⊥
representationDiffers ()

sampleSizeRepresentationWitness :
  Intersection.NonFactorabilityWitness sampleSizeProjection representationAdequacy
sampleSizeRepresentationWitness =
  Intersection.nonFactorabilityWitness
    sameNDisclosureFiltered
    sameNAccessAndNondisclosureAudited
    refl
    representationDiffers

sampleSizeCannotDetermineRepresentationAdequacy :
  Intersection.FactorsThrough sampleSizeProjection representationAdequacy → ⊥
sampleSizeCannotDetermineRepresentationAdequacy =
  Intersection.witnessRulesOutEveryFlatFactorisation sampleSizeRepresentationWitness

------------------------------------------------------------------------
-- Safety / authority firewalls.
------------------------------------------------------------------------

data EngagementSurfaceCreatesDisabilityOrTraumaDiagnosis : Set where
data AccessibilityChecklistCreatesRealisedAccess : Set where
data ParticipationCountCreatesEpistemicVoice : Set where
data DisabilityLabelDeterminesLearningCapacity : Set where
data OneMarginalisedAxisCreatesIntersectionalAdequacy : Set where

engagementDoesNotCreateDisabilityOrTraumaDiagnosis :
  EngagementSurfaceCreatesDisabilityOrTraumaDiagnosis → ⊥
engagementDoesNotCreateDisabilityOrTraumaDiagnosis ()

accessibilityChecklistDoesNotCreateRealisedAccess :
  AccessibilityChecklistCreatesRealisedAccess → ⊥
accessibilityChecklistDoesNotCreateRealisedAccess ()

participationCountDoesNotCreateEpistemicVoice :
  ParticipationCountCreatesEpistemicVoice → ⊥
participationCountDoesNotCreateEpistemicVoice ()

disabilityLabelDoesNotDetermineLearningCapacity :
  DisabilityLabelDeterminesLearningCapacity → ⊥
disabilityLabelDoesNotDetermineLearningCapacity ()

oneMarginalisedAxisDoesNotCreateIntersectionalAdequacy :
  OneMarginalisedAxisCreatesIntersectionalAdequacy → ⊥
oneMarginalisedAxisDoesNotCreateIntersectionalAdequacy ()

intersectionalAbsenceReading : String
intersectionalAbsenceReading =
  "Every admitted study receives a 'who is not at the table?' audit beside its design/statistical claim ceiling. Aggregate n, formal accessibility, participation or a single demographic axis cannot determine situated representation, realised access, epistemic voice or learning capacity. Disability and trauma are never inferred from engagement telemetry. Exact disabled-student sources are retained as evidence about accessibility, disclosure, stigma, flexibility and under-representation, while DASHI's finite non-factorability witnesses remain repository-owned structural mathematics."
