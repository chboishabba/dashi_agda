module DASHI.Wikimedia.IbrahimSnowballSensibLawEvidenceObservationTestimonyCausationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballArchiveHistoriographyCausalityBidiExact as Archive
import DASHI.Governance.WitchTrialEvidenceSubjectAttributionExact as WitchTrial
import DASHI.Cognition.PNF.SensibLawLegalSourceAuthorityEvidenceExact as LegalAuthority
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as LegalElements
import DASHI.Law.LegalFactualCausationButForExact as ButFor

------------------------------------------------------------------------
-- IBRAHIM / SENSIBLAW / SNOWBALL BIDI WELD
--
-- evidence <-> observation <-> testimony <-> measurement <-> inference
--          <-> causation <-> legal causation/adjudication.
--
-- SensibLaw already makes evidence payment consumer- and system-indexed:
-- source recognition, authority, legal element proof, factual causation and
-- scope/liability are distinct stages.  This module exports those distinctions
-- back into the broader Ibrahim graph instead of introducing a parallel legal
-- epistemology.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim/SensibLaw evidence-observation-testimony-causation BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create admissibility, accuracy, corroboration, inference, causal proof, legal authority or liability")

legalEvidenceQid : Identity.ExternalIdentityDemand
legalEvidenceQid = mkQid "evidence (legal-proceeding concept)" "Q176763"

observationQid : Identity.ExternalIdentityDemand
observationQid = mkQid "observation" "Q193181"

testimonyQid : Identity.ExternalIdentityDemand
testimonyQid = mkQid "testimony" "Q1196258"

measurementQid : Identity.ExternalIdentityDemand
measurementQid = mkQid "measurement" "Q12453"

inferenceQid : Identity.ExternalIdentityDemand
inferenceQid = mkQid "inference" "Q408386"

genericCausalityQid : Identity.ExternalIdentityDemand
genericCausalityQid = mkQid "causality" "Q179289"

legalCausationQid : Identity.ExternalIdentityDemand
legalCausationQid = mkQid "causation (legal conduct-result relation)" "Q4923601"

------------------------------------------------------------------------
-- Dewey: retain inspected values only.
------------------------------------------------------------------------

testimonyDewey : Dewey.DeweyCoordinate
testimonyDewey = Dewey.mkVerifiedDewey
  "testimony"
  "347.066"
  "Wikidata Q1196258 DDC statement inspected 2026-09-11"

inferenceDewey : Dewey.DeweyCoordinate
inferenceDewey = Dewey.mkVerifiedDewey
  "inference"
  "160"
  "Wikidata Q408386 DDC statement inspected 2026-09-11"

observationDewey : Dewey.DeweyCoordinate
observationDewey = Dewey.mkUnresolvedDewey
  "observation"
  "no exact inspected DDC value promoted in this pass"

measurementDewey : Dewey.DeweyCoordinate
measurementDewey = Dewey.mkUnresolvedDewey
  "measurement"
  "no exact inspected DDC value promoted in this pass"

causalityDewey : Dewey.DeweyCoordinate
causalityDewey = Dewey.mkUnresolvedDewey
  "causality"
  "generic causal relation retained separately from legal and domain-specific causation; no DDC value promoted"

------------------------------------------------------------------------
-- Regression 1: testimony/report surface cannot recover causal mechanism.
-- Reuses the Salem/spectral-evidence stress-test as an exact concrete witness.
------------------------------------------------------------------------

spectralReportCannotFactorMechanism :
  INF.FactorsThrough WitchTrial.spectralReport WitchTrial.causalMechanism → ⊥
spectralReportCannotFactorMechanism = WitchTrial.spectralReportCannotRecoverMechanism

------------------------------------------------------------------------
-- Regression 2: evidence-source presence cannot recover legal authority.
------------------------------------------------------------------------

data SourceCase : Set where
  sameSourceCandidateNotAuthoritative sameSourceCandidateAuthoritative : SourceCase

data SourceSurface : Set where sameRecognisedSource : SourceSurface
data AuthorityStatus : Set where authorityOpen authorityPaid : AuthorityStatus

sourceSurface : SourceCase → SourceSurface
sourceSurface _ = sameRecognisedSource

authorityStatus : SourceCase → AuthorityStatus
authorityStatus sameSourceCandidateNotAuthoritative = authorityOpen
authorityStatus sameSourceCandidateAuthoritative = authorityPaid

sourceAuthorityDefect : INF.NonFactorabilityWitness sourceSurface authorityStatus
sourceAuthorityDefect = INF.nonFactorabilityWitness
  sameSourceCandidateNotAuthoritative sameSourceCandidateAuthoritative refl (λ ())

recognisedSourceCannotFactorLegalAuthority :
  INF.FactorsThrough sourceSurface authorityStatus → ⊥
recognisedSourceCannotFactorLegalAuthority =
  INF.witnessRulesOutEveryFlatFactorisation sourceAuthorityDefect

------------------------------------------------------------------------
-- Regression 3: one observation/measurement surface cannot recover inference.
------------------------------------------------------------------------

data ObservationCase : Set where
  sameObservedValueInferenceA sameObservedValueInferenceB : ObservationCase

data ObservationSurface : Set where sameObservedMeasuredSurface : ObservationSurface
data InferenceReading : Set where inferenceReadingA inferenceReadingB : InferenceReading

observationSurface : ObservationCase → ObservationSurface
observationSurface _ = sameObservedMeasuredSurface

inferenceReading : ObservationCase → InferenceReading
inferenceReading sameObservedValueInferenceA = inferenceReadingA
inferenceReading sameObservedValueInferenceB = inferenceReadingB

observationInferenceDefect :
  INF.NonFactorabilityWitness observationSurface inferenceReading
observationInferenceDefect = INF.nonFactorabilityWitness
  sameObservedValueInferenceA sameObservedValueInferenceB refl (λ ())

observationCannotFactorEveryInference :
  INF.FactorsThrough observationSurface inferenceReading → ⊥
observationCannotFactorEveryInference =
  INF.witnessRulesOutEveryFlatFactorisation observationInferenceDefect

------------------------------------------------------------------------
-- Regression 4: causal/factual receipt cannot recover scope or liability.
-- SensibLaw's exact but-for owner already holds the stronger no-promotion gates.
------------------------------------------------------------------------

data CausationCase : Set where
  sameFactualCausationScopeOpen sameFactualCausationScopePaid : CausationCase

data CausationSurface : Set where sameFactualCausationSurface : CausationSurface
data ScopeReading : Set where scopeStillOpen scopeSeparatelyPaid : ScopeReading

causationSurface : CausationCase → CausationSurface
causationSurface _ = sameFactualCausationSurface

scopeReading : CausationCase → ScopeReading
scopeReading sameFactualCausationScopeOpen = scopeStillOpen
scopeReading sameFactualCausationScopePaid = scopeSeparatelyPaid

causationScopeDefect : INF.NonFactorabilityWitness causationSurface scopeReading
causationScopeDefect = INF.nonFactorabilityWitness
  sameFactualCausationScopeOpen sameFactualCausationScopePaid refl (λ ())

factualCausationCannotFactorScopeOfLiability :
  INF.FactorsThrough causationSurface scopeReading → ⊥
factualCausationCannotFactorScopeOfLiability =
  INF.witnessRulesOutEveryFlatFactorisation causationScopeDefect

------------------------------------------------------------------------
-- Existing SensibLaw boundaries retained directly.
------------------------------------------------------------------------

legalSourceAuthorityBoundary : LegalAuthority.LegalSourceAuthorityBoundary
legalSourceAuthorityBoundary = LegalAuthority.canonicalLegalSourceAuthorityBoundary

legalButForBoundary : ButFor.LegalButForBoundary
legalButForBoundary = ButFor.canonicalLegalButForBoundary

witchTrialEvidenceBoundary : WitchTrial.WitchTrialEvidenceBoundary
witchTrialEvidenceBoundary = WitchTrial.canonicalWitchTrialEvidenceBoundary

archiveHistoriographyBoundary : Archive.ArchiveHistoriographyCausalityBoundary
archiveHistoriographyBoundary = Archive.canonicalArchiveHistoriographyCausalityBoundary

causationIsAReusableLegalElementKind : LegalElements.LegalElementKind
causationIsAReusableLegalElementKind = LegalElements.causationElement

------------------------------------------------------------------------
-- Reverse BIDI constraints into Ibrahim parent nodes.
------------------------------------------------------------------------

record SensibLawEvidenceReverseConstraint : Set where
  constructor sensiblaw-evidence-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open SensibLawEvidenceReverseConstraint public

evidenceConstraint : SensibLawEvidenceReverseConstraint
evidenceConstraint = sensiblaw-evidence-reverse-constraint
  "Evidence / knowledge"
  "source identity, testimony provenance, observation, measurement, admissibility, authority, inference and proposition status remain distinct"
  false

scienceConstraint : SensibLawEvidenceReverseConstraint
scienceConstraint = sensiblaw-evidence-reverse-constraint
  "Science / observation / measurement"
  "observed value, instrument or measurement process, uncertainty, interpretation, inference and causal identification remain distinct"
  false

lawConstraint : SensibLawEvidenceReverseConstraint
lawConstraint = sensiblaw-evidence-reverse-constraint
  "Law / evidence / causation"
  "source candidate, legal authority, element derivation, factual causation, standard of proof, scope and liability remain separately payable"
  false

anthropologyConstraint : SensibLawEvidenceReverseConstraint
anthropologyConstraint = sensiblaw-evidence-reverse-constraint
  "Anthropology / testimony / affected voice"
  "reported experience, testimony provenance, observer interpretation, mechanism attribution, subject identity and institutional adjudication remain distinct"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data TestimonyCreatesMechanism : Set where
data ObservationCreatesInference : Set where
data MeasurementCreatesCausality : Set where
data SourceCreatesAuthority : Set where
data AuthorityCreatesApplicability : Set where
data LegalElementCreatesLiability : Set where
data CausationCreatesScope : Set where
data QidCreatesEvidenceReceipt : Set where
data DeweyCreatesAdmissibility : Set where

testimonyDoesNotCreateMechanism : TestimonyCreatesMechanism → ⊥
testimonyDoesNotCreateMechanism ()

observationDoesNotCreateInference : ObservationCreatesInference → ⊥
observationDoesNotCreateInference ()

measurementDoesNotCreateCausality : MeasurementCreatesCausality → ⊥
measurementDoesNotCreateCausality ()

sourceDoesNotCreateAuthority : SourceCreatesAuthority → ⊥
sourceDoesNotCreateAuthority ()

authorityDoesNotCreateApplicability : AuthorityCreatesApplicability → ⊥
authorityDoesNotCreateApplicability ()

legalElementDoesNotCreateLiability : LegalElementCreatesLiability → ⊥
legalElementDoesNotCreateLiability ()

causationDoesNotCreateScope : CausationCreatesScope → ⊥
causationDoesNotCreateScope ()

qidDoesNotCreateEvidenceReceipt : QidCreatesEvidenceReceipt → ⊥
qidDoesNotCreateEvidenceReceipt ()

deweyDoesNotCreateAdmissibility : DeweyCreatesAdmissibility → ⊥
deweyDoesNotCreateAdmissibility ()

record SensibLawEvidenceObservationTestimonyCausationBoundary : Set where
  constructor sensiblaw-evidence-observation-testimony-causation-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    deweyRetainedAsNavigationOnly : Bool
    doiAndCanonicalSourceInheritedFromUpstream : Bool
    legalSourcesMayLegitimatelyHaveNoDOI : Bool
    testimonySeparatedFromMechanism : Bool
    observationSeparatedFromInference : Bool
    measurementSeparatedFromCausality : Bool
    sourceRecognitionSeparatedFromAuthority : Bool
    legalAuthoritySeparatedFromApplicability : Bool
    causationSeparatedFromScopeAndLiability : Bool
    sourceRoleAndAffectedVoiceRetained : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open SensibLawEvidenceObservationTestimonyCausationBoundary public

canonicalSensibLawEvidenceObservationTestimonyCausationBoundary :
  SensibLawEvidenceObservationTestimonyCausationBoundary
canonicalSensibLawEvidenceObservationTestimonyCausationBoundary =
  sensiblaw-evidence-observation-testimony-causation-boundary
    true true true true true true true true true true true true false
