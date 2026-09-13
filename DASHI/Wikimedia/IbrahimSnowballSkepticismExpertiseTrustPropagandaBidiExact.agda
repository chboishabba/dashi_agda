module DASHI.Wikimedia.IbrahimSnowballSkepticismExpertiseTrustPropagandaBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimScienceKnowledgePluralityBridgeExact as ScienceKnowledge
import DASHI.Wikimedia.IbrahimSnowballConspiracyDistrustAlternativeMediaBidiExact as DistrustMedia

------------------------------------------------------------------------
-- IBRAHIM / SNOWBALL BIDI CONTINUATION:
--
-- skepticism / scientific skepticism / critical thinking / expertise
--      <-> trust in science / trust in scientists
--      <-> misinformation / disinformation / propaganda.
--
-- Methodological scrutiny, generalized distrust, source expertise, source
-- credibility, proposition truth, institutional trust, propaganda intent,
-- misinformation status and disinformation status are distinct consumers.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim skepticism/expertise/trust/propaganda BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid "Wikidata identity inspected 2026-09-10; identity does not promote truth, authority, trustworthiness, intent or causal influence")

skepticismQid : Identity.ExternalIdentityDemand
skepticismQid = mkQid "skepticism" "Q1395219"

scientificSkepticismQid : Identity.ExternalIdentityDemand
scientificSkepticismQid = mkQid "scientific skepticism" "Q929771"

criticalThinkingQid : Identity.ExternalIdentityDemand
criticalThinkingQid = mkQid "critical thinking" "Q843894"

expertiseQid : Identity.ExternalIdentityDemand
expertiseQid = mkQid "expertise" "Q644238"

propagandaQid : Identity.ExternalIdentityDemand
propagandaQid = mkQid "propaganda" "Q7281"

misinformationQid : Identity.ExternalIdentityDemand
misinformationQid = mkQid "misinformation" "Q13579947"

disinformationQid : Identity.ExternalIdentityDemand
disinformationQid = mkQid "disinformation" "Q189656"

trustInScienceQid : Identity.ExternalIdentityDemand
trustInScienceQid = Identity.mkOptionalIdentityDemand
  "Ibrahim skepticism/expertise/trust/propaganda BIDI"
  "external concept identity"
  "trust in science"
  Identity.wikidataQid
  (Identity.unresolved "no exact trust-in-science concept QID safely promoted in this pass; trust in claims, scientists, institutions and domains remain distinct")

trustInScientistsQid : Identity.ExternalIdentityDemand
trustInScientistsQid = Identity.mkOptionalIdentityDemand
  "Ibrahim skepticism/expertise/trust/propaganda BIDI"
  "external concept identity"
  "trust in scientists"
  Identity.wikidataQid
  (Identity.unresolved "no exact same-concept QID safely promoted in this pass; person/source credibility and confidence in scientific claims remain distinct")

------------------------------------------------------------------------
-- Source-bounded scholarship.
------------------------------------------------------------------------

lyonsExpertiseSource : Attribution.AttributedSource
lyonsExpertiseSource = Attribution.mkDOISource
  "Benjamin A. Lyons"
  "How orientations to expertise condition the acceptance of (mis)information"
  "Current Opinion in Psychology 54, 101714"
  "2023"
  "10.1016/j.copsyc.2023.101714"
  "https://doi.org/10.1016/j.copsyc.2023.101714"
  Attribution.academicArticleSource
  "review of anti-expert sentiment, institutional distrust, epistemic overconfidence, anti-establishment orientation, science populism and conspiracist worldviews as distinct orientations relevant to misinformation acceptance; does not identify skepticism with anti-expertise"
  Attribution.publicAttribution

vanAntwerpenExpertiseSource : Attribution.AttributedSource
vanAntwerpenExpertiseSource = Attribution.mkDOISource
  "Natasha van Antwerpen; Estelle B. Green; Daniel Sturman; Rachel A. Searston"
  "The impacts of expertise, conflict, and scientific literacy on trust and belief in scientific disagreements"
  "Scientific Reports 15, 11869"
  "2025"
  "10.1038/s41598-025-96333-8"
  "https://doi.org/10.1038/s41598-025-96333-8"
  Attribution.academicArticleSource
  "three factorial experiments manipulating disagreeing-source subject-matter expertise and vested interest; expertise cues affected trust/belief, while conflict and literacy effects varied by sample"
  Attribution.publicAttribution

youngerKhanTrustSource : Attribution.AttributedSource
youngerKhanTrustSource = Attribution.mkDOISource
  "Sukayna Younger-Khan"
  "Mapping patterns of trust in science and scientists"
  "Current Opinion in Psychology 67, 102203"
  "2026"
  "10.1016/j.copsyc.2025.102203"
  "https://doi.org/10.1016/j.copsyc.2025.102203"
  Attribution.academicArticleSource
  "review distinguishing trust in science from trust in scientists and emphasizing domain, sociocultural and political variation; does not treat science or trust as monolithic"
  Attribution.publicAttribution

hoesMisinformationTrustSource : Attribution.AttributedSource
hoesMisinformationTrustSource = Attribution.mkDOISource
  "Emma Hoes; Bernhard Clemm; Theresa Gessler; Sijia Qian; Magdalena Wojcieszak et al."
  "(Media Attention to) Misinformation Can Undermine Trust in Scientists"
  "Political Behavior"
  "2025"
  "10.1007/s11109-025-10090-y"
  "https://doi.org/10.1007/s11109-025-10090-y"
  Attribution.academicArticleSource
  "multi-method US evidence distinguishing misinformation exposure from journalistic coverage of misinformation and reporting outcome/method-dependent effects on misperceptions and trust; coverage is not itself misinformation"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Regression 1: skepticism label cannot determine epistemic method/status.
------------------------------------------------------------------------

data SkepticismCase : Set where
  sameSkepticismMethodologicalScrutiny sameSkepticismGeneralizedRejection : SkepticismCase

data SkepticismSurface : Set where sameSkepticismLabel : SkepticismSurface
data SkepticismRole : Set where evidenceResponsiveScrutiny blanketRejectionRole : SkepticismRole

skepticismSurface : SkepticismCase → SkepticismSurface
skepticismSurface _ = sameSkepticismLabel

skepticismRole : SkepticismCase → SkepticismRole
skepticismRole sameSkepticismMethodologicalScrutiny = evidenceResponsiveScrutiny
skepticismRole sameSkepticismGeneralizedRejection = blanketRejectionRole

skepticismRoleDefect : INF.NonFactorabilityWitness skepticismSurface skepticismRole
skepticismRoleDefect = INF.nonFactorabilityWitness
  sameSkepticismMethodologicalScrutiny sameSkepticismGeneralizedRejection refl (λ ())

skepticismLabelCannotFactorEpistemicRole :
  INF.FactorsThrough skepticismSurface skepticismRole → ⊥
skepticismLabelCannotFactorEpistemicRole =
  INF.witnessRulesOutEveryFlatFactorisation skepticismRoleDefect

------------------------------------------------------------------------
-- Regression 2: expertise does not determine truth or trustworthiness.
------------------------------------------------------------------------

data ExpertiseCase : Set where
  sameExpertiseSupportedClaim sameExpertiseUnsupportedClaim : ExpertiseCase

data ExpertiseSurface : Set where sameDomainExpertise : ExpertiseSurface
data ClaimAudit : Set where claimSupported claimNotSupported : ClaimAudit

expertiseSurface : ExpertiseCase → ExpertiseSurface
expertiseSurface _ = sameDomainExpertise

claimAudit : ExpertiseCase → ClaimAudit
claimAudit sameExpertiseSupportedClaim = claimSupported
claimAudit sameExpertiseUnsupportedClaim = claimNotSupported

expertiseClaimDefect : INF.NonFactorabilityWitness expertiseSurface claimAudit
expertiseClaimDefect = INF.nonFactorabilityWitness
  sameExpertiseSupportedClaim sameExpertiseUnsupportedClaim refl (λ ())

expertiseCannotFactorClaimTruth :
  INF.FactorsThrough expertiseSurface claimAudit → ⊥
expertiseCannotFactorClaimTruth =
  INF.witnessRulesOutEveryFlatFactorisation expertiseClaimDefect

------------------------------------------------------------------------
-- Regression 3: trust in scientists and trust in scientific claims differ.
------------------------------------------------------------------------

data ScienceTrustCase : Set where
  sameScientistTrustClaimAccepted sameScientistTrustClaimQuestioned : ScienceTrustCase

data ScientistTrustSurface : Set where sameTrustInScientist : ScientistTrustSurface
data ScientificClaimTrust : Set where scientificClaimAccepted scientificClaimQuestioned : ScientificClaimTrust

scientistTrustSurface : ScienceTrustCase → ScientistTrustSurface
scientistTrustSurface _ = sameTrustInScientist

scientificClaimTrust : ScienceTrustCase → ScientificClaimTrust
scientificClaimTrust sameScientistTrustClaimAccepted = scientificClaimAccepted
scientificClaimTrust sameScientistTrustClaimQuestioned = scientificClaimQuestioned

scienceTrustDefect : INF.NonFactorabilityWitness scientistTrustSurface scientificClaimTrust
scienceTrustDefect = INF.nonFactorabilityWitness
  sameScientistTrustClaimAccepted sameScientistTrustClaimQuestioned refl (λ ())

trustInScientistCannotFactorTrustInEveryClaim :
  INF.FactorsThrough scientistTrustSurface scientificClaimTrust → ⊥
trustInScientistCannotFactorTrustInEveryClaim =
  INF.witnessRulesOutEveryFlatFactorisation scienceTrustDefect

------------------------------------------------------------------------
-- Regression 4: propaganda intent and information truth/status differ.
------------------------------------------------------------------------

data PropagandaCase : Set where
  samePersuasiveIntentFactuallySupported samePersuasiveIntentFalseOrMisleading : PropagandaCase

data PropagandaSurface : Set where sameInfluenceIntent : PropagandaSurface
data InformationTruthStatus : Set where factuallySupportedInformation falseOrMisleadingInformation : InformationTruthStatus

propagandaSurface : PropagandaCase → PropagandaSurface
propagandaSurface _ = sameInfluenceIntent

informationTruthStatus : PropagandaCase → InformationTruthStatus
informationTruthStatus samePersuasiveIntentFactuallySupported = factuallySupportedInformation
informationTruthStatus samePersuasiveIntentFalseOrMisleading = falseOrMisleadingInformation

propagandaTruthDefect : INF.NonFactorabilityWitness propagandaSurface informationTruthStatus
propagandaTruthDefect = INF.nonFactorabilityWitness
  samePersuasiveIntentFactuallySupported samePersuasiveIntentFalseOrMisleading refl (λ ())

propagandaIntentCannotFactorTruthStatus :
  INF.FactorsThrough propagandaSurface informationTruthStatus → ⊥
propagandaIntentCannotFactorTruthStatus =
  INF.witnessRulesOutEveryFlatFactorisation propagandaTruthDefect

------------------------------------------------------------------------
-- Regression 5: misinformation and disinformation remain intent-distinct.
------------------------------------------------------------------------

data FalseInformationCase : Set where
  sameFalseContentNoIntentPaid sameFalseContentDeliberateDeceptionPaid : FalseInformationCase

data FalseContentSurface : Set where sameFalseContent : FalseContentSurface
data IntentionReading : Set where deceptiveIntentNotPaid deliberateDeceptionPaid : IntentionReading

falseContentSurface : FalseInformationCase → FalseContentSurface
falseContentSurface _ = sameFalseContent

intentionReading : FalseInformationCase → IntentionReading
intentionReading sameFalseContentNoIntentPaid = deceptiveIntentNotPaid
intentionReading sameFalseContentDeliberateDeceptionPaid = deliberateDeceptionPaid

misinformationDisinformationDefect : INF.NonFactorabilityWitness falseContentSurface intentionReading
misinformationDisinformationDefect = INF.nonFactorabilityWitness
  sameFalseContentNoIntentPaid sameFalseContentDeliberateDeceptionPaid refl (λ ())

falseContentCannotFactorDeceptiveIntent :
  INF.FactorsThrough falseContentSurface intentionReading → ⊥
falseContentCannotFactorDeceptiveIntent =
  INF.witnessRulesOutEveryFlatFactorisation misinformationDisinformationDefect

------------------------------------------------------------------------
-- Existing parent owners are reused rather than duplicated.
------------------------------------------------------------------------

scienceKnowledgeBoundary : ScienceKnowledge.ScienceKnowledgePluralityReceipt
scienceKnowledgeBoundary = ScienceKnowledge.canonicalScienceKnowledgePluralityReceipt

distrustMediaBoundary : DistrustMedia.ConspiracyDistrustAlternativeMediaBoundary
distrustMediaBoundary = DistrustMedia.canonicalConspiracyDistrustAlternativeMediaBoundary

------------------------------------------------------------------------
-- Reverse constraints back into Ibrahim/Snowball parent nodes.
------------------------------------------------------------------------

record SkepticismExpertiseReverseConstraint : Set where
  constructor skepticism-expertise-reverse-constraint
  field
    parentNode : String
    childWitness : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open SkepticismExpertiseReverseConstraint public

scienceConstraint : SkepticismExpertiseReverseConstraint
scienceConstraint = skepticism-expertise-reverse-constraint
  "Science"
  "trust/expertise/skepticism cases"
  "methodological scrutiny, domain expertise, claim evidence, scientist credibility, institutional trust, replication and disagreement remain distinct"
  false

knowledgeConstraint : SkepticismExpertiseReverseConstraint
knowledgeConstraint = skepticism-expertise-reverse-constraint
  "Knowledge"
  "critical-thinking and misinformation cases"
  "reasoning procedure, source role, proposition truth, confidence, uncertainty and authority remain distinct"
  false

mediaConstraint : SkepticismExpertiseReverseConstraint
mediaConstraint = skepticism-expertise-reverse-constraint
  "Media / information"
  "misinformation coverage and propaganda cases"
  "carrier, content truth, corrective framing, persuasive intent, deceptive intent and audience effect remain distinct"
  false

expertiseConstraint : SkepticismExpertiseReverseConstraint
expertiseConstraint = skepticism-expertise-reverse-constraint
  "Expertise"
  "expert disagreement and pseudo/unreliable-expert problem"
  "credential/competence, domain match, conflict, evidence quality, reliability, trustworthiness and proposition truth remain separately payable"
  false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SkepticismCreatesAntiExpertise : Set where
data ScientificSkepticismCreatesScienceDenial : Set where
data CriticalThinkingCreatesTruth : Set where
data ExpertiseCreatesTruth : Set where
data ExpertIdentityCreatesAuthority : Set where
data TrustInScientistCreatesTrustInClaim : Set where
data DistrustCreatesFalsehood : Set where
data PropagandaCreatesFalsehood : Set where
data MisinformationCreatesDeceptiveIntent : Set where
data DisinformationQidPaysIntent : Set where

skepticismDoesNotCreateAntiExpertise : SkepticismCreatesAntiExpertise → ⊥
skepticismDoesNotCreateAntiExpertise ()

scientificSkepticismDoesNotCreateScienceDenial : ScientificSkepticismCreatesScienceDenial → ⊥
scientificSkepticismDoesNotCreateScienceDenial ()

criticalThinkingDoesNotCreateTruth : CriticalThinkingCreatesTruth → ⊥
criticalThinkingDoesNotCreateTruth ()

expertiseDoesNotCreateTruth : ExpertiseCreatesTruth → ⊥
expertiseDoesNotCreateTruth ()

expertIdentityDoesNotCreateAuthority : ExpertIdentityCreatesAuthority → ⊥
expertIdentityDoesNotCreateAuthority ()

trustInScientistDoesNotCreateTrustInClaim : TrustInScientistCreatesTrustInClaim → ⊥
trustInScientistDoesNotCreateTrustInClaim ()

distrustDoesNotCreateFalsehood : DistrustCreatesFalsehood → ⊥
distrustDoesNotCreateFalsehood ()

propagandaDoesNotCreateFalsehood : PropagandaCreatesFalsehood → ⊥
propagandaDoesNotCreateFalsehood ()

misinformationDoesNotCreateDeceptiveIntent : MisinformationCreatesDeceptiveIntent → ⊥
misinformationDoesNotCreateDeceptiveIntent ()

disinformationQidDoesNotPayIntent : DisinformationQidPaysIntent → ⊥
disinformationQidDoesNotPayIntent ()

record SkepticismExpertiseTrustPropagandaBoundary : Set where
  constructor skepticism-expertise-trust-propaganda-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    unresolvedTrustIdentitiesRetained : Bool
    scientificSkepticismSeparatedFromGeneralSkepticism : Bool
    skepticismDoesNotDetermineAntiExpertise : Bool
    expertiseDoesNotDetermineClaimTruth : Bool
    trustInScientistsSeparatedFromTrustInScience : Bool
    trustDoesNotReplaceEvidenceAudit : Bool
    propagandaIntentSeparatedFromTruthStatus : Bool
    misinformationSeparatedFromDisinformationByIntent : Bool
    qidDoesNotPayTruthIntentOrAuthority : Bool
    sourceDateRoleMethodAndPopulationTravel : Bool
    twoEyedComparisonRetainsInstitutionalAndPublicPerspectives : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open SkepticismExpertiseTrustPropagandaBoundary public

canonicalSkepticismExpertiseTrustPropagandaBoundary : SkepticismExpertiseTrustPropagandaBoundary
canonicalSkepticismExpertiseTrustPropagandaBoundary =
  skepticism-expertise-trust-propaganda-boundary
    true true true true true true true true true true true true true false
