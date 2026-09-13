module DASHI.Wikimedia.IbrahimSnowballTestimonyMemoryCredibilityCorroborationExpertBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballSensibLawEvidenceObservationTestimonyCausationBidiExact as Evidence
import DASHI.Governance.WitchTrialEvidenceSubjectAttributionExact as WitchTrial
import DASHI.Cognition.PNF.SensibLawLegalSourceAuthorityEvidenceExact as LegalAuthority
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as LegalElement

------------------------------------------------------------------------
-- IBRAHIM / SENSIBLAW TESTIMONY-MEMORY-CREDIBILITY BIDI
--
-- A testimony is a report carrier. Memory/perception are cognitive source
-- processes. Credibility is an assessment coordinate. Corroboration is an
-- additional-evidence relation. Expert evidence is a role-bound evidentiary
-- contribution. None alone settles proposition truth, legal authority,
-- causation, culpability, or historical reconstruction.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim testimony/memory/credibility/corroboration/expert BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create truth, reliability, independence, admissibility, expertise fit or legal authority")

memoryQid : Identity.ExternalIdentityDemand
memoryQid = mkQid "memory" "Q492"

perceptionQid : Identity.ExternalIdentityDemand
perceptionQid = mkQid "perception" "Q160402"

credibilityQid : Identity.ExternalIdentityDemand
credibilityQid = mkQid "credibility" "Q1530061"

corroboratingEvidenceQid : Identity.ExternalIdentityDemand
corroboratingEvidenceQid = mkQid "corroborating evidence" "Q4964998"

expertWitnessQid : Identity.ExternalIdentityDemand
expertWitnessQid = mkQid "expert witness" "Q663272"

testimonyQid : Identity.ExternalIdentityDemand
testimonyQid = Evidence.testimonyQid

------------------------------------------------------------------------
-- Dewey travels where inspected; unresolved coordinates stay explicit.
------------------------------------------------------------------------

testimonyDewey : Dewey.DeweyCoordinate
testimonyDewey = Dewey.mkVerifiedDewey
  "testimony"
  "347.066"
  "Wikidata Q1196258 DDC statement inspected in prior Ibrahim evidence pass"

memoryDewey : Dewey.DeweyCoordinate
memoryDewey = Dewey.mkUnresolvedDewey
  "memory"
  "no exact inspected DDC value promoted in this pass"

perceptionDewey : Dewey.DeweyCoordinate
perceptionDewey = Dewey.mkUnresolvedDewey
  "perception"
  "no exact inspected DDC value promoted in this pass"

credibilityDewey : Dewey.DeweyCoordinate
credibilityDewey = Dewey.mkUnresolvedDewey
  "credibility"
  "no exact inspected DDC value promoted in this pass"

expertEvidenceDewey : Dewey.DeweyCoordinate
expertEvidenceDewey = Dewey.mkUnresolvedDewey
  "expert witness / expert evidence"
  "no exact inspected DDC value promoted in this pass"

------------------------------------------------------------------------
-- DOI-bounded scholarship.
------------------------------------------------------------------------

puddifootEyewitnessSource : Attribution.AttributedSource
puddifootEyewitnessSource = Attribution.mkDOISource
  "Katherine Puddifoot"
  "Re-evaluating the credibility of eyewitness testimony: the misinformation effect and the overcritical juror"
  "Episteme 17(2), 255-279"
  "2020"
  "10.1017/epi.2018.42"
  "https://doi.org/10.1017/epi.2018.42"
  Attribution.academicArticleSource
  "philosophical/psychological analysis of eyewitness credibility under the misinformation effect; supports calibrated credence rather than blanket acceptance or blanket rejection"
  Attribution.publicAttribution

loftusMisinformationHistorySource : Attribution.AttributedSource
loftusMisinformationHistorySource = Attribution.mkDOISource
  "Elizabeth F. Loftus; E. S. Sutton; A. Dianat; J. P. Hoffmann"
  "The history of an idea: The misinformation effect"
  "Legal and Criminological Psychology 31"
  "2026"
  "10.1111/lcrp.70020"
  "https://doi.org/10.1111/lcrp.70020"
  Attribution.academicArticleSource
  "review/history of misinformation-effect research in eyewitness memory; memory fallibility does not imply universal witness unreliability"
  Attribution.publicAttribution

leippeExpertWitnessSource : Attribution.AttributedSource
leippeExpertWitnessSource = Attribution.mkDOISource
  "Michael R. Leippe"
  "The case for expert testimony about eyewitness memory"
  "Psychology, Public Policy, and Law 1(4), 909-959"
  "1995"
  "10.1037/1076-8971.1.4.909"
  "https://doi.org/10.1037/1076-8971.1.4.909"
  Attribution.academicArticleSource
  "evidence and argument concerning expert testimony on eyewitness memory; expert role informs evaluation but does not itself decide witness truth or legal outcome"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Regression 1: report/testimony surface cannot recover memory reliability.
------------------------------------------------------------------------

data WitnessCase : Set where
  sameReportStableMemory sameReportPostEventDistortion : WitnessCase

data ReportSurface : Set where sameWitnessReport : ReportSurface
data MemoryStatus : Set where comparativelyStableMemory distortedOrUncertainMemory : MemoryStatus

reportSurface : WitnessCase → ReportSurface
reportSurface _ = sameWitnessReport

memoryStatus : WitnessCase → MemoryStatus
memoryStatus sameReportStableMemory = comparativelyStableMemory
memoryStatus sameReportPostEventDistortion = distortedOrUncertainMemory

reportMemoryDefect : INF.NonFactorabilityWitness reportSurface memoryStatus
reportMemoryDefect = INF.nonFactorabilityWitness
  sameReportStableMemory sameReportPostEventDistortion refl (λ ())

testimonyCannotFactorMemoryReliability :
  INF.FactorsThrough reportSurface memoryStatus → ⊥
testimonyCannotFactorMemoryReliability =
  INF.witnessRulesOutEveryFlatFactorisation reportMemoryDefect

------------------------------------------------------------------------
-- Regression 2: credibility assessment cannot recover proposition truth.
------------------------------------------------------------------------

data CredibilityCase : Set where
  sameCredibilityClaimTrue sameCredibilityClaimFalse : CredibilityCase

data CredibilitySurface : Set where sameCredibilityAssessment : CredibilitySurface
data PropositionTruth : Set where propositionTrue propositionFalse : PropositionTruth

credibilitySurface : CredibilityCase → CredibilitySurface
credibilitySurface _ = sameCredibilityAssessment

propositionTruth : CredibilityCase → PropositionTruth
propositionTruth sameCredibilityClaimTrue = propositionTrue
propositionTruth sameCredibilityClaimFalse = propositionFalse

credibilityTruthDefect : INF.NonFactorabilityWitness credibilitySurface propositionTruth
credibilityTruthDefect = INF.nonFactorabilityWitness
  sameCredibilityClaimTrue sameCredibilityClaimFalse refl (λ ())

credibilityCannotFactorTruth :
  INF.FactorsThrough credibilitySurface propositionTruth → ⊥
credibilityCannotFactorTruth =
  INF.witnessRulesOutEveryFlatFactorisation credibilityTruthDefect

------------------------------------------------------------------------
-- Regression 3: number of reports cannot recover corroborative independence.
------------------------------------------------------------------------

data CorroborationCase : Set where
  sameReportCountIndependent sameReportCountGenerated : CorroborationCase

data CountSurface : Set where sameMultiplicity : CountSurface
data IndependenceStatus : Set where independentCorroboration endogenousOrGeneratedRepetition : IndependenceStatus

countSurface : CorroborationCase → CountSurface
countSurface _ = sameMultiplicity

independenceStatus : CorroborationCase → IndependenceStatus
independenceStatus sameReportCountIndependent = independentCorroboration
independenceStatus sameReportCountGenerated = endogenousOrGeneratedRepetition

corroborationIndependenceDefect : INF.NonFactorabilityWitness countSurface independenceStatus
corroborationIndependenceDefect = INF.nonFactorabilityWitness
  sameReportCountIndependent sameReportCountGenerated refl (λ ())

reportMultiplicityCannotFactorIndependence :
  INF.FactorsThrough countSurface independenceStatus → ⊥
reportMultiplicityCannotFactorIndependence =
  INF.witnessRulesOutEveryFlatFactorisation corroborationIndependenceDefect

------------------------------------------------------------------------
-- Regression 4: expert status cannot recover fit/admissibility/conclusion.
------------------------------------------------------------------------

data ExpertCase : Set where
  sameExpertIdentityDomainFit sameExpertIdentityWrongDomain : ExpertCase

data ExpertSurface : Set where sameExpertWitnessIdentity : ExpertSurface
data ExpertFit : Set where expertFitsQuestion expertDoesNotFitQuestion : ExpertFit

expertSurface : ExpertCase → ExpertSurface
expertSurface _ = sameExpertWitnessIdentity

expertFit : ExpertCase → ExpertFit
expertFit sameExpertIdentityDomainFit = expertFitsQuestion
expertFit sameExpertIdentityWrongDomain = expertDoesNotFitQuestion

expertFitDefect : INF.NonFactorabilityWitness expertSurface expertFit
expertFitDefect = INF.nonFactorabilityWitness
  sameExpertIdentityDomainFit sameExpertIdentityWrongDomain refl (λ ())

expertIdentityCannotFactorDomainFit :
  INF.FactorsThrough expertSurface expertFit → ⊥
expertIdentityCannotFactorDomainFit =
  INF.witnessRulesOutEveryFlatFactorisation expertFitDefect

------------------------------------------------------------------------
-- Exact reuse of existing SensibLaw / witch-trial boundaries.
------------------------------------------------------------------------

witchEvidenceBoundary : WitchTrial.WitchTrialEvidenceBoundary
witchEvidenceBoundary = WitchTrial.canonicalWitchTrialEvidenceBoundary

legalSourceAuthorityBoundary : LegalAuthority.LegalSourceAuthorityBoundary
legalSourceAuthorityBoundary = LegalAuthority.canonicalLegalSourceAuthorityBoundary

-- Merely naming an element/reference still does not prove the legal element.
legalElementReferenceDoesNotBecomeProof :
  LegalElement.ElementStringReferenceIsElementProof → ⊥
legalElementReferenceDoesNotBecomeProof = LegalElement.stringReferenceDoesNotProveElement

------------------------------------------------------------------------
-- Reverse BIDI constraints into the Ibrahim parents.
------------------------------------------------------------------------

record TestimonyReverseConstraint : Set where
  constructor testimony-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open TestimonyReverseConstraint public

psychologyConstraint : TestimonyReverseConstraint
psychologyConstraint = testimony-reverse-constraint
  "Memory / perception / cognition"
  "experienced event, perception, encoding, retention, post-event information, retrieval and report remain distinct"
  false

lawConstraint : TestimonyReverseConstraint
lawConstraint = testimony-reverse-constraint
  "Evidence / testimony / expert evidence"
  "report content, provenance, independence, credibility, admissibility, expert-domain fit, element proof and legal authority remain distinct"
  false

historyConstraint : TestimonyReverseConstraint
historyConstraint = testimony-reverse-constraint
  "History / archives"
  "multiple surviving reports do not become independent corroboration without provenance; conviction and historical reconstruction remain distinct"
  false

scienceConstraint : TestimonyReverseConstraint
scienceConstraint = testimony-reverse-constraint
  "Observation / measurement / inference"
  "observer report, instrument measurement, expert interpretation, uncertainty and proposition truth remain distinct"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data CredibleWitnessMeansTrueClaim : Set where
data FallibleMemoryMeansWitnessUnreliable : Set where
data MultipleReportsMeanIndependentCorroboration : Set where
data ExpertStatusMeansDomainFit : Set where
data ExpertEvidenceCreatesLegalAuthority : Set where
data QidCreatesCredibility : Set where

aCredibleWitnessDoesNotMakeEveryClaimTrue : CredibleWitnessMeansTrueClaim → ⊥
aCredibleWitnessDoesNotMakeEveryClaimTrue ()

memoryFallibilityDoesNotMakeEveryWitnessUnreliable : FallibleMemoryMeansWitnessUnreliable → ⊥
memoryFallibilityDoesNotMakeEveryWitnessUnreliable ()

multipleReportsDoNotCreateIndependence : MultipleReportsMeanIndependentCorroboration → ⊥
multipleReportsDoNotCreateIndependence ()

expertStatusDoesNotCreateDomainFit : ExpertStatusMeansDomainFit → ⊥
expertStatusDoesNotCreateDomainFit ()

expertEvidenceDoesNotCreateLegalAuthority : ExpertEvidenceCreatesLegalAuthority → ⊥
expertEvidenceDoesNotCreateLegalAuthority ()

qidDoesNotCreateCredibility : QidCreatesCredibility → ⊥
qidDoesNotCreateCredibility ()

record TestimonyMemoryCredibilityBoundary : Set where
  constructor testimony-memory-credibility-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    deweyUnresolvedStateRetained : Bool
    doiSourceRoleRetained : Bool
    testimonySeparatedFromMemoryReliability : Bool
    credibilitySeparatedFromTruth : Bool
    multiplicitySeparatedFromIndependentCorroboration : Bool
    expertIdentitySeparatedFromDomainFit : Bool
    legalAuthorityAndExpertEvidenceSeparated : Bool
    witchTrialGeneratedTestimonyProvenanceReused : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open TestimonyMemoryCredibilityBoundary public

canonicalTestimonyMemoryCredibilityBoundary : TestimonyMemoryCredibilityBoundary
canonicalTestimonyMemoryCredibilityBoundary =
  testimony-memory-credibility-boundary
    true true true true true true true true true true false
