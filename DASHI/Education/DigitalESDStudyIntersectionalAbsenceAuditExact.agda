module DASHI.Education.DigitalESDStudyIntersectionalAbsenceAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Cognition.PNF.TraumaMemoryHypervoxelAuthorityBoundaryExact as Trauma
import DASHI.Education.DigitalESDExternalityIncidenceAuditExact as Incidence
import DASHI.Education.DigitalESDDisabilityIntersectionalityAuditExact as Disability

------------------------------------------------------------------------
-- STUDY-LEVEL INTERSECTIONAL ABSENCE AUDIT
--
-- Thin overlay over the canonical disability/intersectionality owner.  It does
-- not duplicate that source atlas or create another demographic ontology.  Its
-- one job is to ask, for every admitted study: "who is not at the table?"
--
-- The audit distinguishes realised sample/corpus membership from target
-- population, structural eligibility/access filters, disclosure visibility,
-- affected-but-unsampled parties, interpretation, authority and future options.
------------------------------------------------------------------------

disabilitySourceCount : Nat
disabilitySourceCount = Disability.primaryEmpiricalSourceCount

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
questionReading whoWasSampled = "who is literally represented in the realised analytic carrier?"
questionReading whoWasEligibleButMissing = "who belongs to the declared target population but is absent from the realised sample/corpus?"
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
-- Reuse canonical disability, situated/access, trauma and externality owners.
------------------------------------------------------------------------

disabilityBoundary : Disability.DisabilityDigitalESDBoundary
disabilityBoundary = Disability.canonicalDisabilityDigitalESDBoundary

situatedCapabilityReading : String
situatedCapabilityReading =
  "Family choice is one observation surface over a multi-actor situated capability system. Child, family, kin/community, professional and public authority remain coordinate-specific; equal transfers need not create equal reachable opportunity, and equity may require different kinds of connection rather than only more of the same scalar resource."

traumaAuthorityBoundary : Trauma.TraumaMemoryHypervoxelAuthorityBoundary
traumaAuthorityBoundary = Trauma.canonicalTraumaMemoryHypervoxelAuthorityBoundary

externalityBoundary : Incidence.ExternalityIncidenceBoundary
externalityBoundary = Incidence.canonicalExternalityIncidenceBoundary

------------------------------------------------------------------------
-- Constructive collision: the same aggregate n cannot recover whether the
-- realised carrier captures the representation needed by its consumer.
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
-- Safety / authority firewalls.  The canonical disability owner additionally
-- blocks disability<->trauma inference and political/religious analogy ->
-- disability evidence.  This overlay adds telemetry/absence-specific guards.
------------------------------------------------------------------------

data EngagementSurfaceCreatesDisabilityOrTraumaDiagnosis : Set where
data AccessibilityChecklistCreatesRealisedAccess : Set where
data ParticipationCountCreatesEpistemicVoice : Set where
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

oneMarginalisedAxisDoesNotCreateIntersectionalAdequacy :
  OneMarginalisedAxisCreatesIntersectionalAdequacy → ⊥
oneMarginalisedAxisDoesNotCreateIntersectionalAdequacy ()

intersectionalAbsenceReading : String
intersectionalAbsenceReading =
  "Every admitted study receives a 'who is not at the table?' audit beside its design/statistical claim ceiling. Aggregate n, formal accessibility, participation or a single demographic axis cannot determine situated representation, realised access or epistemic voice. The canonical disability owner retains exact disability-specific primary evidence and blocks disability<->trauma, disability->incapacity, and political/religious analogy->disability promotion. Engagement telemetry never diagnoses disability or trauma."
