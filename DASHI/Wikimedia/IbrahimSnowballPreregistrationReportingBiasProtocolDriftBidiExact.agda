module DASHI.Wikimedia.IbrahimSnowballPreregistrationReportingBiasProtocolDriftBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballSystematicReviewMetaAnalysisPublicationBiasBidiExact as Review
import DASHI.Wikimedia.IbrahimSnowballProofSearchExperimentalDesignBidiExact as Design

------------------------------------------------------------------------
-- IBRAHIM / PROTOCOL -> PREREGISTRATION -> PUBLICATION BIDI
--
-- A protocol/preregistration records a plan. A publication reports realised
-- conduct/results. Registered Reports alter review/publication timing. None of
-- these identities proves adherence, adequate design, unbiased reporting or
-- proposition truth. Deviations may be legitimate but must remain visible.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim preregistration/reporting-bias/protocol-drift BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create adherence, transparency, methodological adequacy or truth")

researchProtocolQid : Identity.ExternalIdentityDemand
researchProtocolQid = mkQid "research / experimental protocol" "Q367158"

clinicalTrialRegistrationQid : Identity.ExternalIdentityDemand
clinicalTrialRegistrationQid = mkQid "clinical trial registration / application" "Q104774766"

preregistrationQid : Identity.ExternalIdentityDemand
preregistrationQid = Identity.mkOptionalIdentityDemand
  "Ibrahim preregistration/reporting-bias/protocol-drift BIDI"
  "external concept identity"
  "research preregistration"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact general preregistration concept QID safely promoted in this pass; research protocol Q367158 and clinical-trial registration Q104774766 remain distinct")

registeredReportQid : Identity.ExternalIdentityDemand
registeredReportQid = Identity.mkOptionalIdentityDemand
  "Ibrahim preregistration/reporting-bias/protocol-drift BIDI"
  "external concept identity"
  "Registered Report publication format"
  Identity.wikidataQid
  (Identity.unresolved
    "Wikidata contains works about Registered Reports, but no exact concept QID was safely promoted in this pass")

reportingBiasQid : Identity.ExternalIdentityDemand
reportingBiasQid = Identity.mkOptionalIdentityDemand
  "Ibrahim preregistration/reporting-bias/protocol-drift BIDI"
  "external concept identity"
  "outcome/selective reporting bias"
  Identity.wikidataQid
  (Identity.unresolved
    "publication bias Q919364 is explicitly different from reporting bias; no exact reporting-bias QID safely promoted in this pass")

protocolDewey : Dewey.DeweyCoordinate
protocolDewey = Dewey.mkUnresolvedDewey
  "research protocol / preregistration"
  "no exact inspected DDC value promoted in this pass"

registeredReportDewey : Dewey.DeweyCoordinate
registeredReportDewey = Dewey.mkUnresolvedDewey
  "Registered Report"
  "no exact inspected DDC value promoted in this pass"

reportingBiasDewey : Dewey.DeweyCoordinate
reportingBiasDewey = Dewey.mkUnresolvedDewey
  "selective/outcome reporting bias"
  "no exact inspected DDC value promoted in this pass"

------------------------------------------------------------------------
-- Primary methodological / empirical source objects.
------------------------------------------------------------------------

chanSelectiveReportingSource : Attribution.AttributedSource
chanSelectiveReportingSource = Attribution.mkDOISource
  "An-Wen Chan; Asbjørn Hróbjartsson; Mette T. Haahr; Peter C. Gøtzsche; Douglas G. Altman"
  "Empirical Evidence for Selective Reporting of Outcomes in Randomized Trials: Comparison of Protocols to Published Articles"
  "JAMA 291(20), 2457-2465"
  "2004"
  "10.1001/jama.291.20.2457"
  "https://doi.org/10.1001/jama.291.20.2457"
  Attribution.academicArticleSource
  "primary empirical comparison of trial protocols with publications showing incomplete/selective outcome reporting; bounded to the sampled trials and does not imply every protocol-publication difference is misconduct"
  Attribution.publicAttribution

chambersRegisteredReportsSource : Attribution.AttributedSource
chambersRegisteredReportsSource = Attribution.mkDOISource
  "Christopher D. Chambers"
  "Registered Reports: a new publishing initiative at Cortex"
  "Cortex 49(3), 609-610"
  "2013"
  "10.1016/j.cortex.2012.12.016"
  "https://doi.org/10.1016/j.cortex.2012.12.016"
  Attribution.academicArticleSource
  "primary editorial launching/describing the Cortex Registered Reports format; publication model identity does not establish adherence, study quality or truth"
  Attribution.publicAttribution

chambersRealigningIncentivesSource : Attribution.AttributedSource
chambersRealigningIncentivesSource = Attribution.mkDOISource
  "Christopher D. Chambers; Zoltan Dienes; Robert D. McIntosh; Pia Rotshtein; Klaus Willmes"
  "Registered reports: realigning incentives in scientific publishing"
  "Cortex 66, A1-A2"
  "2015"
  "10.1016/j.cortex.2015.03.022"
  "https://doi.org/10.1016/j.cortex.2015.03.022"
  Attribution.academicArticleSource
  "methodological/editorial argument concerning incentives and result-independent publication; not evidence that every Registered Report is valid"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Regression 1: same registered/preregistered surface cannot recover adherence.
------------------------------------------------------------------------

data RegistrationCase : Set where
  sameRegistrationAdhered sameRegistrationMaterialDeviation : RegistrationCase

data RegistrationSurface : Set where samePreregisteredLabel : RegistrationSurface
data AdherenceStatus : Set where planSubstantiallyFollowed materialDeviationPresent : AdherenceStatus

registrationSurface : RegistrationCase → RegistrationSurface
registrationSurface _ = samePreregisteredLabel

adherenceStatus : RegistrationCase → AdherenceStatus
adherenceStatus sameRegistrationAdhered = planSubstantiallyFollowed
adherenceStatus sameRegistrationMaterialDeviation = materialDeviationPresent

registrationAdherenceDefect : INF.NonFactorabilityWitness registrationSurface adherenceStatus
registrationAdherenceDefect = INF.nonFactorabilityWitness
  sameRegistrationAdhered sameRegistrationMaterialDeviation refl (λ ())

preregistrationCannotFactorAdherence :
  INF.FactorsThrough registrationSurface adherenceStatus → ⊥
preregistrationCannotFactorAdherence =
  INF.witnessRulesOutEveryFlatFactorisation registrationAdherenceDefect

------------------------------------------------------------------------
-- Regression 2: protocol/publication difference cannot recover legitimacy.
------------------------------------------------------------------------

data DriftCase : Set where
  sameProtocolDriftTransparentJustified sameProtocolDriftSelectiveUndisclosed : DriftCase

data DriftSurface : Set where sameProtocolPublicationDifference : DriftSurface
data DriftRole : Set where justifiedTransparentDeviation selectiveUndisclosedDeviation : DriftRole

driftSurface : DriftCase → DriftSurface
driftSurface _ = sameProtocolPublicationDifference

driftRole : DriftCase → DriftRole
driftRole sameProtocolDriftTransparentJustified = justifiedTransparentDeviation
driftRole sameProtocolDriftSelectiveUndisclosed = selectiveUndisclosedDeviation

protocolDriftDefect : INF.NonFactorabilityWitness driftSurface driftRole
protocolDriftDefect = INF.nonFactorabilityWitness
  sameProtocolDriftTransparentJustified sameProtocolDriftSelectiveUndisclosed refl (λ ())

protocolDriftCannotFactorSelectiveReporting :
  INF.FactorsThrough driftSurface driftRole → ⊥
protocolDriftCannotFactorSelectiveReporting =
  INF.witnessRulesOutEveryFlatFactorisation protocolDriftDefect

------------------------------------------------------------------------
-- Regression 3: Registered Report format cannot recover study truth.
------------------------------------------------------------------------

data RegisteredReportCase : Set where
  sameRegisteredFormatClaimTrue sameRegisteredFormatClaimFalse : RegisteredReportCase

data RegisteredFormatSurface : Set where sameRegisteredReportFormat : RegisteredFormatSurface
data ClaimTruth : Set where claimTrue claimFalse : ClaimTruth

registeredFormatSurface : RegisteredReportCase → RegisteredFormatSurface
registeredFormatSurface _ = sameRegisteredReportFormat

claimTruth : RegisteredReportCase → ClaimTruth
claimTruth sameRegisteredFormatClaimTrue = claimTrue
claimTruth sameRegisteredFormatClaimFalse = claimFalse

registeredTruthDefect : INF.NonFactorabilityWitness registeredFormatSurface claimTruth
registeredTruthDefect = INF.nonFactorabilityWitness
  sameRegisteredFormatClaimTrue sameRegisteredFormatClaimFalse refl (λ ())

registeredReportFormatCannotFactorTruth :
  INF.FactorsThrough registeredFormatSurface claimTruth → ⊥
registeredReportFormatCannotFactorTruth =
  INF.witnessRulesOutEveryFlatFactorisation registeredTruthDefect

------------------------------------------------------------------------
-- Existing review/design owners reused.
------------------------------------------------------------------------

reviewBoundary : Review.SystematicReviewMetaAnalysisBoundary
reviewBoundary = Review.canonicalSystematicReviewMetaAnalysisBoundary

designBoundary : Design.ProofSearchExperimentalDesignBoundary
designBoundary = Design.canonicalProofSearchExperimentalDesignBoundary

------------------------------------------------------------------------
-- Reverse BIDI constraints.
------------------------------------------------------------------------

record RegistrationReverseConstraint : Set where
  constructor registration-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open RegistrationReverseConstraint public

designConstraint : RegistrationReverseConstraint
designConstraint = registration-reverse-constraint
  "Experimental design"
  "planned hypotheses/outcomes/analysis, timestamps, amendments, deviations, realised conduct and exploratory analyses remain distinct"
  false

publicationConstraint : RegistrationReverseConstraint
publicationConstraint = registration-reverse-constraint
  "Publication / evidence synthesis"
  "protocol identity, preregistration, Registered Report format, publication manifestation, outcome selection, reporting completeness and truth remain distinct"
  false

snowballConstraint : RegistrationReverseConstraint
snowballConstraint = registration-reverse-constraint
  "Snowball provenance"
  "earlier plan state must remain append-only alongside later amendments/publications; later publication cannot silently rewrite historical protocol state"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data PreregisteredMeansAdherent : Set where
data ProtocolDifferenceMeansMisconduct : Set where
data RegisteredReportMeansTrue : Set where
data RegistrationMeansAdequateDesign : Set where
data QidMeansTransparency : Set where
data DeweyMeansMethodQuality : Set where

preregisteredDoesNotMeanAdherent : PreregisteredMeansAdherent → ⊥
preregisteredDoesNotMeanAdherent ()

protocolDifferenceDoesNotMeanMisconduct : ProtocolDifferenceMeansMisconduct → ⊥
protocolDifferenceDoesNotMeanMisconduct ()

registeredReportDoesNotMeanTrue : RegisteredReportMeansTrue → ⊥
registeredReportDoesNotMeanTrue ()

registrationDoesNotMeanAdequateDesign : RegistrationMeansAdequateDesign → ⊥
registrationDoesNotMeanAdequateDesign ()

qidDoesNotCreateTransparency : QidMeansTransparency → ⊥
qidDoesNotCreateTransparency ()

deweyDoesNotCreateMethodQuality : DeweyMeansMethodQuality → ⊥
deweyDoesNotCreateMethodQuality ()

record PreregistrationReportingBiasBoundary : Set where
  constructor preregistration-reporting-bias-boundary
  field
    safeQidsAttached : Bool
    unresolvedExactConceptQidsRetained : Bool
    deweyUnresolvedRetained : Bool
    doiCanonicalPrimarySourcesRetained : Bool
    registrationSeparatedFromAdherence : Bool
    protocolDriftSeparatedFromSelectiveReporting : Bool
    registeredFormatSeparatedFromTruth : Bool
    protocolHistoryAppendOnly : Bool
    reviewAndExperimentalDesignOwnersReused : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open PreregistrationReportingBiasBoundary public

canonicalPreregistrationReportingBiasBoundary : PreregistrationReportingBiasBoundary
canonicalPreregistrationReportingBiasBoundary =
  preregistration-reporting-bias-boundary
    true true true true true true true true true true false
