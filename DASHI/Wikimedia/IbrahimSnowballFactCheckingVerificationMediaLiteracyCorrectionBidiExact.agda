module DASHI.Wikimedia.IbrahimSnowballFactCheckingVerificationMediaLiteracyCorrectionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSkepticismExpertiseTrustPropagandaBidiExact as Skepticism
import DASHI.Wikimedia.IbrahimSnowballConspiracyDistrustAlternativeMediaBidiExact as Distrust
import DASHI.Wikimedia.IbrahimScienceKnowledgePluralityBridgeExact as ScienceKnowledge

------------------------------------------------------------------------
-- IBRAHIM / SNOWBALL BIDI CONTINUATION:
-- fact-checking / verification / source criticism / credibility / media literacy
--      <-> correction / uncertainty communication / retraction
--      <-> skepticism / expertise / trust / misinformation.
--
-- A verification process, fact-check verdict, source-credibility judgment,
-- correction, audience uptake and proposition truth are different consumers.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim fact-checking/verification/media-literacy/correction BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid "Wikidata identity inspected 2026-09-10; identity does not promote proposition truth, correction uptake, trust or authority")

factCheckingQid : Identity.ExternalIdentityDemand
factCheckingQid = mkQid "fact-checking" "Q59555084"

verificationQid : Identity.ExternalIdentityDemand
verificationQid = mkQid "verification" "Q953429"

sourceCriticismQid : Identity.ExternalIdentityDemand
sourceCriticismQid = mkQid "source criticism" "Q2122746"

mediaLiteracyQid : Identity.ExternalIdentityDemand
mediaLiteracyQid = mkQid "media literacy" "Q1507246"

credibilityQid : Identity.ExternalIdentityDemand
credibilityQid = mkQid "credibility" "Q1530061"

uncertaintyQid : Identity.ExternalIdentityDemand
uncertaintyQid = mkQid "uncertainty" "Q13649246"

retractionQid : Identity.ExternalIdentityDemand
retractionQid = mkQid "academic/scientific retraction" "Q45203135"

retractionNoticeQid : Identity.ExternalIdentityDemand
retractionNoticeQid = mkQid "retraction notice" "Q7316896"

correctionQid : Identity.ExternalIdentityDemand
correctionQid = Identity.mkOptionalIdentityDemand
  "Ibrahim fact-checking/verification/media-literacy/correction BIDI"
  "external concept identity"
  "correction / corrective information"
  Identity.wikidataQid
  (Identity.unresolved "no exact broad correction concept QID safely promoted in this pass; journal correction, misinformation correction, retraction and rectification remain separate")

debunkingQid : Identity.ExternalIdentityDemand
debunkingQid = Identity.mkOptionalIdentityDemand
  "Ibrahim fact-checking/verification/media-literacy/correction BIDI"
  "external concept identity"
  "debunking"
  Identity.wikidataQid
  (Identity.unresolved "no exact same-concept QID safely promoted in this pass")

------------------------------------------------------------------------
-- Attributed empirical/review sources.
------------------------------------------------------------------------

huangMediaLiteracySource : Attribution.AttributedSource
huangMediaLiteracySource = Attribution.mkDOISource
  "Guanxiong Huang; Wufan Jia; Wenting Yu"
  "Media Literacy Interventions Improve Resilience to Misinformation: A Meta-Analytic Investigation of Overall Effect and Moderating Factors"
  "Communication Research"
  "2024"
  "10.1177/00936502241288103"
  "https://doi.org/10.1177/00936502241288103"
  Attribution.academicArticleSource
  "meta-analysis of 49 experimental studies and 81,155 participants finding an overall positive media-literacy effect; does not guarantee correct judgment for every learner, claim or domain"
  Attribution.publicAttribution

choMediaLiteracySource : Attribution.AttributedSource
choMediaLiteracySource = Attribution.mkDOISource
  "HyunYi Cho; Christopher J. Carpenter; Wenbo Li"
  "Media literacy interventions: meta-analytic review of 40 years of research"
  "Human Communication Research 51(2):57-79"
  "2025"
  "10.1093/hcr/hqaf004"
  "https://doi.org/10.1093/hcr/hqaf004"
  Attribution.academicArticleSource
  "meta-analysis of 160 interventions across four decades reporting generally positive but outcome- and context-varying effects; not a universal discernment theorem"
  Attribution.publicAttribution

walterCorrectionSource : Attribution.AttributedSource
walterCorrectionSource = Attribution.mkDOISource
  "Nathan Walter; Riva Tukachinsky"
  "A Meta-Analytic Examination of the Continued Influence of Misinformation in the Face of Correction"
  "Communication Research 47(2)"
  "2020"
  "10.1177/0093650219854600"
  "https://doi.org/10.1177/0093650219854600"
  Attribution.academicArticleSource
  "meta-analysis showing correction does not necessarily eliminate continued influence and that correction effectiveness varies; correction exposure is not correction uptake"
  Attribution.publicAttribution

vanDerBlesUncertaintySource : Attribution.AttributedSource
vanDerBlesUncertaintySource = Attribution.mkDOISource
  "Anne Marthe van der Bles; Sander van der Linden; Alexandra L. J. Freeman; James Mitchell; Ana B. Galvao; Lisa Zaval; David J. Spiegelhalter"
  "Communicating uncertainty about facts, numbers and science"
  "Royal Society Open Science 6:181870"
  "2019"
  "10.1098/rsos.181870"
  "https://doi.org/10.1098/rsos.181870"
  Attribution.academicArticleSource
  "interdisciplinary review distinguishing objects and forms of epistemic uncertainty communication; uncertainty disclosure is not equivalent to falsehood or incompetence"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Regression 1: a fact-check verdict/process cannot replace independent
-- proposition-level evidence identity and audit.
------------------------------------------------------------------------

data FactCheckCase : Set where
  sameFactCheckLabelEvidencePaid sameFactCheckLabelEvidenceUninspected : FactCheckCase

data FactCheckSurface : Set where sameFactCheckVerdictSurface : FactCheckSurface
data PropositionAudit : Set where propositionEvidencePaid propositionEvidenceOpen : PropositionAudit

factCheckSurface : FactCheckCase → FactCheckSurface
factCheckSurface _ = sameFactCheckVerdictSurface

propositionAudit : FactCheckCase → PropositionAudit
propositionAudit sameFactCheckLabelEvidencePaid = propositionEvidencePaid
propositionAudit sameFactCheckLabelEvidenceUninspected = propositionEvidenceOpen

factCheckAuditDefect : INF.NonFactorabilityWitness factCheckSurface propositionAudit
factCheckAuditDefect = INF.nonFactorabilityWitness sameFactCheckLabelEvidencePaid sameFactCheckLabelEvidenceUninspected refl (λ ())

factCheckLabelCannotFactorIndependentEvidenceAudit :
  INF.FactorsThrough factCheckSurface propositionAudit → ⊥
factCheckLabelCannotFactorIndependentEvidenceAudit =
  INF.witnessRulesOutEveryFlatFactorisation factCheckAuditDefect

------------------------------------------------------------------------
-- Regression 2: source credibility cannot determine proposition truth.
------------------------------------------------------------------------

data CredibilityCase : Set where
  sameCredibilitySupportedClaim sameCredibilityUnsupportedClaim : CredibilityCase

data CredibilitySurface : Set where sameSourceCredibility : CredibilitySurface
data ClaimStatus : Set where supportedClaim unsupportedClaim : ClaimStatus

credibilitySurface : CredibilityCase → CredibilitySurface
credibilitySurface _ = sameSourceCredibility

claimStatus : CredibilityCase → ClaimStatus
claimStatus sameCredibilitySupportedClaim = supportedClaim
claimStatus sameCredibilityUnsupportedClaim = unsupportedClaim

credibilityTruthDefect : INF.NonFactorabilityWitness credibilitySurface claimStatus
credibilityTruthDefect = INF.nonFactorabilityWitness sameCredibilitySupportedClaim sameCredibilityUnsupportedClaim refl (λ ())

sourceCredibilityCannotFactorClaimTruth : INF.FactorsThrough credibilitySurface claimStatus → ⊥
sourceCredibilityCannotFactorClaimTruth = INF.witnessRulesOutEveryFlatFactorisation credibilityTruthDefect

------------------------------------------------------------------------
-- Regression 3: correction exposure cannot determine belief update.
------------------------------------------------------------------------

data CorrectionCase : Set where
  sameCorrectionExposureUpdated sameCorrectionExposureContinuedInfluence : CorrectionCase

data CorrectionSurface : Set where sameCorrectionSeen : CorrectionSurface
data CorrectionOutcome : Set where beliefUpdated continuedInfluenceRemains : CorrectionOutcome

correctionSurface : CorrectionCase → CorrectionSurface
correctionSurface _ = sameCorrectionSeen

correctionOutcome : CorrectionCase → CorrectionOutcome
correctionOutcome sameCorrectionExposureUpdated = beliefUpdated
correctionOutcome sameCorrectionExposureContinuedInfluence = continuedInfluenceRemains

correctionUptakeDefect : INF.NonFactorabilityWitness correctionSurface correctionOutcome
correctionUptakeDefect = INF.nonFactorabilityWitness sameCorrectionExposureUpdated sameCorrectionExposureContinuedInfluence refl (λ ())

correctionExposureCannotFactorBeliefUpdate : INF.FactorsThrough correctionSurface correctionOutcome → ⊥
correctionExposureCannotFactorBeliefUpdate = INF.witnessRulesOutEveryFlatFactorisation correctionUptakeDefect

------------------------------------------------------------------------
-- Regression 4: media-literacy intervention participation cannot determine
-- successful claim discernment for every learner or item.
------------------------------------------------------------------------

data LiteracyCase : Set where
  sameTrainingDiscerned sameTrainingDidNotEstablishDiscernment : LiteracyCase

data LiteracySurface : Set where sameMediaLiteracyTraining : LiteracySurface
data DiscernmentOutcome : Set where discernmentPaid discernmentNotEstablished : DiscernmentOutcome

literacySurface : LiteracyCase → LiteracySurface
literacySurface _ = sameMediaLiteracyTraining

discernmentOutcome : LiteracyCase → DiscernmentOutcome
discernmentOutcome sameTrainingDiscerned = discernmentPaid
discernmentOutcome sameTrainingDidNotEstablishDiscernment = discernmentNotEstablished

literacyDiscernmentDefect : INF.NonFactorabilityWitness literacySurface discernmentOutcome
literacyDiscernmentDefect = INF.nonFactorabilityWitness sameTrainingDiscerned sameTrainingDidNotEstablishDiscernment refl (λ ())

mediaLiteracyTrainingCannotFactorEveryDiscernmentOutcome :
  INF.FactorsThrough literacySurface discernmentOutcome → ⊥
mediaLiteracyTrainingCannotFactorEveryDiscernmentOutcome =
  INF.witnessRulesOutEveryFlatFactorisation literacyDiscernmentDefect

------------------------------------------------------------------------
-- Regression 5: communicated uncertainty cannot determine falsehood.
------------------------------------------------------------------------

data UncertaintyCase : Set where
  sameUncertaintySupportedEstimate sameUncertaintyUnsupportedClaim : UncertaintyCase

data UncertaintySurface : Set where sameUncertaintyDisclosure : UncertaintySurface
data EvidenceStatus : Set where uncertaintyWithEvidence uncertaintyWithoutSupport : EvidenceStatus

uncertaintySurface : UncertaintyCase → UncertaintySurface
uncertaintySurface _ = sameUncertaintyDisclosure

evidenceStatus : UncertaintyCase → EvidenceStatus
evidenceStatus sameUncertaintySupportedEstimate = uncertaintyWithEvidence
evidenceStatus sameUncertaintyUnsupportedClaim = uncertaintyWithoutSupport

uncertaintyEvidenceDefect : INF.NonFactorabilityWitness uncertaintySurface evidenceStatus
uncertaintyEvidenceDefect = INF.nonFactorabilityWitness sameUncertaintySupportedEstimate sameUncertaintyUnsupportedClaim refl (λ ())

uncertaintyCommunicationCannotFactorEvidenceStatus :
  INF.FactorsThrough uncertaintySurface evidenceStatus → ⊥
uncertaintyCommunicationCannotFactorEvidenceStatus =
  INF.witnessRulesOutEveryFlatFactorisation uncertaintyEvidenceDefect

------------------------------------------------------------------------
-- Regression 6: document-level retraction status cannot determine the status
-- of every proposition, dataset or downstream claim without a scoped audit.
------------------------------------------------------------------------

data RetractionCase : Set where
  sameRetractedDocumentAffectedClaim sameRetractedDocumentUnauditedOtherClaim : RetractionCase

data RetractionSurface : Set where sameDocumentRetraction : RetractionSurface
data ScopedClaimReading : Set where affectedClaimWithdrawn otherClaimNeedsAudit : ScopedClaimReading

retractionSurface : RetractionCase → RetractionSurface
retractionSurface _ = sameDocumentRetraction

scopedClaimReading : RetractionCase → ScopedClaimReading
scopedClaimReading sameRetractedDocumentAffectedClaim = affectedClaimWithdrawn
scopedClaimReading sameRetractedDocumentUnauditedOtherClaim = otherClaimNeedsAudit

retractionScopeDefect : INF.NonFactorabilityWitness retractionSurface scopedClaimReading
retractionScopeDefect = INF.nonFactorabilityWitness sameRetractedDocumentAffectedClaim sameRetractedDocumentUnauditedOtherClaim refl (λ ())

retractionCannotFactorEveryContainedClaimStatus :
  INF.FactorsThrough retractionSurface scopedClaimReading → ⊥
retractionCannotFactorEveryContainedClaimStatus =
  INF.witnessRulesOutEveryFlatFactorisation retractionScopeDefect

------------------------------------------------------------------------
-- Existing parent surfaces are inherited rather than rebuilt.
------------------------------------------------------------------------

skepticismBoundary : Skepticism.SkepticismExpertiseTrustPropagandaBoundary
skepticismBoundary = Skepticism.canonicalSkepticismExpertiseTrustPropagandaBoundary

distrustBoundary : Distrust.ConspiracyDistrustAlternativeMediaBoundary
distrustBoundary = Distrust.canonicalConspiracyDistrustAlternativeMediaBoundary

scienceKnowledgeBoundary : ScienceKnowledge.ScienceKnowledgePluralityReceipt
scienceKnowledgeBoundary = ScienceKnowledge.canonicalScienceKnowledgePluralityReceipt

------------------------------------------------------------------------
-- Reverse BIDI constraints.
------------------------------------------------------------------------

record VerificationReverseConstraint : Set where
  constructor verification-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open VerificationReverseConstraint public

knowledgeConstraint : VerificationReverseConstraint
knowledgeConstraint = verification-reverse-constraint
  "Knowledge"
  "claim identity, evidence, source credibility, verification process, uncertainty, confidence and correction history remain separate"
  false

scienceConstraint : VerificationReverseConstraint
scienceConstraint = verification-reverse-constraint
  "Science"
  "measurement/evidence, expertise, peer or external verification, uncertainty communication, correction and retraction are distinct coordinates"
  false

mediaConstraint : VerificationReverseConstraint
mediaConstraint = verification-reverse-constraint
  "Media"
  "fact-checking carrier, source criticism, verdict, evidence link, correction exposure, audience uptake and information status remain separate"
  false

pedagogyConstraint : VerificationReverseConstraint
pedagogyConstraint = verification-reverse-constraint
  "Media literacy / pedagogy"
  "intervention participation, learned skill, item-level discernment, agency, retention and transfer remain separately payable"
  false

------------------------------------------------------------------------
-- No-promotion firewalls.
------------------------------------------------------------------------

data FactCheckerCreatesTruth : Set where
data VerificationQidCreatesVerificationReceipt : Set where
data CredibilityCreatesTruth : Set where
data CorrectionCreatesBeliefChange : Set where
data MediaLiteracyCreatesCorrectJudgment : Set where
data UncertaintyCreatesFalsehood : Set where
data RetractionCreatesEveryClaimFalse : Set where

factCheckerDoesNotCreateTruth : FactCheckerCreatesTruth → ⊥
factCheckerDoesNotCreateTruth ()

verificationQidDoesNotCreateVerificationReceipt : VerificationQidCreatesVerificationReceipt → ⊥
verificationQidDoesNotCreateVerificationReceipt ()

credibilityDoesNotCreateTruth : CredibilityCreatesTruth → ⊥
credibilityDoesNotCreateTruth ()

correctionDoesNotCreateBeliefChange : CorrectionCreatesBeliefChange → ⊥
correctionDoesNotCreateBeliefChange ()

mediaLiteracyDoesNotCreateCorrectJudgment : MediaLiteracyCreatesCorrectJudgment → ⊥
mediaLiteracyDoesNotCreateCorrectJudgment ()

uncertaintyDoesNotCreateFalsehood : UncertaintyCreatesFalsehood → ⊥
uncertaintyDoesNotCreateFalsehood ()

retractionDoesNotCreateEveryClaimFalse : RetractionCreatesEveryClaimFalse → ⊥
retractionDoesNotCreateEveryClaimFalse ()

record FactCheckingVerificationMediaLiteracyCorrectionBoundary : Set where
  constructor fact-checking-verification-media-literacy-correction-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    unresolvedCorrectionAndDebunkingRetained : Bool
    factCheckVerdictDoesNotReplaceEvidenceAudit : Bool
    sourceCredibilityDoesNotDetermineTruth : Bool
    correctionExposureDoesNotDetermineUptake : Bool
    mediaLiteracyDoesNotGuaranteeDiscernment : Bool
    uncertaintyDoesNotMeanFalsehood : Bool
    retractionRemainsClaimScopeSensitive : Bool
    verificationIsClaimSourceMethodAndDateIndexed : Bool
    attributionLinksTravelWithVerdictsAndCorrections : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open FactCheckingVerificationMediaLiteracyCorrectionBoundary public

canonicalFactCheckingVerificationMediaLiteracyCorrectionBoundary :
  FactCheckingVerificationMediaLiteracyCorrectionBoundary
canonicalFactCheckingVerificationMediaLiteracyCorrectionBoundary =
  fact-checking-verification-media-literacy-correction-boundary
    true true true true true true true true true true true false
