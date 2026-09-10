module DASHI.Wikimedia.IbrahimSnowballConspiracyDistrustAlternativeMediaBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballManosphereIDWOnlineInfluenceBidiExact as Online
import DASHI.Wikimedia.IbrahimSnowballManosphereReligionNationalismClimateBidiExact as Prior

------------------------------------------------------------------------
-- BIDI continuation:
-- conspiracy theory / epistemic distrust / alternative media
-- <-> media diet / online influence <-> climate and political discourse.
--
-- Classification, truth, source credibility, institutional trust, dissent,
-- media carrier, ideology and private belief are different consumers.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim conspiracy/distrust/alternative-media BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid "Wikidata identity inspected 2026-09-10; no truth, membership, motive or causation promotion")

conspiracyTheoryQid : Identity.ExternalIdentityDemand
conspiracyTheoryQid = mkQid "conspiracy theory" "Q159535"

alternativeMediaQid : Identity.ExternalIdentityDemand
alternativeMediaQid = mkQid "alternative media" "Q192855"

disinformationQid : Identity.ExternalIdentityDemand
disinformationQid = mkQid "disinformation" "Q189656"

joeRoganQid : Identity.ExternalIdentityDemand
joeRoganQid = mkQid "Joe Rogan" "Q2718421"

institutionalDistrustQid : Identity.ExternalIdentityDemand
institutionalDistrustQid = Identity.mkOptionalIdentityDemand
  "Ibrahim conspiracy/distrust/alternative-media BIDI"
  "external concept identity"
  "institutional distrust"
  Identity.wikidataQid
  (Identity.unresolved "no exact concept QID safely promoted in this pass; distrust of a specific institution and generalized distrust remain separate")

epistemicDistrustQid : Identity.ExternalIdentityDemand
epistemicDistrustQid = Identity.mkOptionalIdentityDemand
  "Ibrahim conspiracy/distrust/alternative-media BIDI"
  "external concept identity"
  "epistemic distrust / skeptical epistemic orientation"
  Identity.wikidataQid
  (Identity.unresolved "no exact same-concept QID safely promoted in this pass")

------------------------------------------------------------------------
-- Source-bounded current scholarship.
------------------------------------------------------------------------

ottoClimateDistrustSource : Attribution.AttributedSource
ottoClimateDistrustSource = Attribution.mkDOISource
  "Otto et al."
  "Narratives of distrust: climate change, disinformation, and the dynamics of right-wing media"
  "Humanities and Social Sciences Communications"
  "2026"
  "10.1057/s41599-026-08597-8"
  "https://doi.org/10.1057/s41599-026-08597-8"
  Attribution.academicArticleSource
  "bounded thematic analysis of one right-wing Telegram media case and its distrust/climate/disinformation narratives; not a universal model of right-wing or alternative media"
  Attribution.publicAttribution

noethZanderSource : Attribution.AttributedSource
noethZanderSource = Attribution.mkDOISource
  "Nöth; Zander"
  "How Epistemic Beliefs about Climate Change Predict Climate Change Conspiracy Beliefs"
  "Frontiers in Psychology 16"
  "2025"
  "10.3389/fpsyg.2025.1523143"
  "https://doi.org/10.3389/fpsyg.2025.1523143"
  Attribution.academicArticleSource
  "one correlational and one preregistered experimental study; association/mediation results do not establish a simple causal route from epistemic belief or distrust to conspiracy belief"
  Attribution.publicAttribution

jreEpistemicStyleSource : Attribution.AttributedSource
jreEpistemicStyleSource = Attribution.mkDOISource
  "Communication research authors"
  "The Joe Rogan Experience: Epistemic Style Over Ideological Extremity in the Manosphere"
  "Political Communication"
  "2026"
  "10.1080/10584609.2026.2690998"
  "https://doi.org/10.1080/10584609.2026.2690998"
  Attribution.academicArticleSource
  "two US probability samples examining correlates of JRE listening, media diet, skeptical epistemic orientation, conspiracism and institutional distrust; listening does not determine ideology, belief or causal persuasion"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Regression 1: institutional distrust does not determine conspiracy belief.
------------------------------------------------------------------------

data DistrustCase : Set where
  sameDistrustEvidenceSeekingDissent sameDistrustConspiracyEndorsement : DistrustCase

data DistrustSurface : Set where sameInstitutionalDistrust : DistrustSurface
data ConspiracyReading : Set where heterodoxEvidenceSeeking conspiracyBeliefPaid : ConspiracyReading

distrustSurface : DistrustCase → DistrustSurface
distrustSurface _ = sameInstitutionalDistrust

conspiracyReading : DistrustCase → ConspiracyReading
conspiracyReading sameDistrustEvidenceSeekingDissent = heterodoxEvidenceSeeking
conspiracyReading sameDistrustConspiracyEndorsement = conspiracyBeliefPaid

distrustConspiracyDefect : INF.NonFactorabilityWitness distrustSurface conspiracyReading
distrustConspiracyDefect = INF.nonFactorabilityWitness
  sameDistrustEvidenceSeekingDissent sameDistrustConspiracyEndorsement refl (λ ())

institutionalDistrustCannotFactorConspiracyBelief :
  INF.FactorsThrough distrustSurface conspiracyReading → ⊥
institutionalDistrustCannotFactorConspiracyBelief =
  INF.witnessRulesOutEveryFlatFactorisation distrustConspiracyDefect

------------------------------------------------------------------------
-- Regression 2: alternative-media carrier does not determine truth/status.
------------------------------------------------------------------------

data AlternativeMediaCase : Set where
  sameAlternativeCarrierSourcePaidReporting sameAlternativeCarrierDisinformation : AlternativeMediaCase

data AlternativeMediaSurface : Set where sameAlternativeMediaCarrier : AlternativeMediaSurface
data InformationStatus : Set where evidenceBearingReporting disinformationPaid : InformationStatus

alternativeMediaSurface : AlternativeMediaCase → AlternativeMediaSurface
alternativeMediaSurface _ = sameAlternativeMediaCarrier

informationStatus : AlternativeMediaCase → InformationStatus
informationStatus sameAlternativeCarrierSourcePaidReporting = evidenceBearingReporting
informationStatus sameAlternativeCarrierDisinformation = disinformationPaid

alternativeMediaStatusDefect : INF.NonFactorabilityWitness alternativeMediaSurface informationStatus
alternativeMediaStatusDefect = INF.nonFactorabilityWitness
  sameAlternativeCarrierSourcePaidReporting sameAlternativeCarrierDisinformation refl (λ ())

alternativeMediaCannotFactorInformationStatus :
  INF.FactorsThrough alternativeMediaSurface informationStatus → ⊥
alternativeMediaCannotFactorInformationStatus =
  INF.witnessRulesOutEveryFlatFactorisation alternativeMediaStatusDefect

------------------------------------------------------------------------
-- Regression 3: a conspiracy-theory classification does not itself pay the
-- proposition-level truth/evidence adjudication that justified the label.
------------------------------------------------------------------------

data ClassifiedClaimCase : Set where
  sameClassificationEvidenceInspected sameClassificationEvidenceUninspected : ClassifiedClaimCase

data ClassificationSurface : Set where sameConspiracyClassification : ClassificationSurface
data EvidenceAuditReading : Set where evidenceAuditPaid evidenceAuditStillOpen : EvidenceAuditReading

classificationSurface : ClassifiedClaimCase → ClassificationSurface
classificationSurface _ = sameConspiracyClassification

evidenceAuditReading : ClassifiedClaimCase → EvidenceAuditReading
evidenceAuditReading sameClassificationEvidenceInspected = evidenceAuditPaid
evidenceAuditReading sameClassificationEvidenceUninspected = evidenceAuditStillOpen

classificationEvidenceDefect : INF.NonFactorabilityWitness classificationSurface evidenceAuditReading
classificationEvidenceDefect = INF.nonFactorabilityWitness
  sameClassificationEvidenceInspected sameClassificationEvidenceUninspected refl (λ ())

conspiracyLabelCannotFactorEvidenceAudit :
  INF.FactorsThrough classificationSurface evidenceAuditReading → ⊥
conspiracyLabelCannotFactorEvidenceAudit =
  INF.witnessRulesOutEveryFlatFactorisation classificationEvidenceDefect

------------------------------------------------------------------------
-- Regression 4: media consumption/listening cannot determine ideology/belief.
------------------------------------------------------------------------

data ListeningCase : Set where
  sameListeningPositionA sameListeningPositionB : ListeningCase

data ListeningSurface : Set where sameMediaListening : ListeningSurface
data IdeologicalReading : Set where ideologicalPositionA ideologicalPositionB : IdeologicalReading

listeningSurface : ListeningCase → ListeningSurface
listeningSurface _ = sameMediaListening

ideologicalReading : ListeningCase → IdeologicalReading
ideologicalReading sameListeningPositionA = ideologicalPositionA
ideologicalReading sameListeningPositionB = ideologicalPositionB

listeningIdeologyDefect : INF.NonFactorabilityWitness listeningSurface ideologicalReading
listeningIdeologyDefect = INF.nonFactorabilityWitness
  sameListeningPositionA sameListeningPositionB refl (λ ())

mediaConsumptionCannotFactorIdeology :
  INF.FactorsThrough listeningSurface ideologicalReading → ⊥
mediaConsumptionCannotFactorIdeology =
  INF.witnessRulesOutEveryFlatFactorisation listeningIdeologyDefect

------------------------------------------------------------------------
-- Existing graph owners reused.
------------------------------------------------------------------------

onlineBoundary : Online.ManosphereIDWOnlineInfluenceBoundary
onlineBoundary = Online.canonicalManosphereIDWOnlineInfluenceBoundary

priorBoundary : Prior.ManosphereReligionNationalismClimateBoundary
priorBoundary = Prior.canonicalManosphereReligionNationalismClimateBoundary

------------------------------------------------------------------------
-- Reverse constraints.
------------------------------------------------------------------------

record EpistemicMediaReverseConstraint : Set where
  constructor epistemic-media-reverse-constraint
  field
    parentNode : String
    childWitness : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open EpistemicMediaReverseConstraint public

knowledgeConstraint : EpistemicMediaReverseConstraint
knowledgeConstraint = epistemic-media-reverse-constraint
  "Knowledge / epistemic evaluation"
  "distrust and conspiracy-classification cases"
  "source credibility, institutional trust, proposition truth, evidence quality and dissent remain separate"
  false

mediaConstraint : EpistemicMediaReverseConstraint
mediaConstraint = epistemic-media-reverse-constraint
  "Media"
  "alternative-media cases"
  "carrier, source role, content status, audience use and truth adjudication remain separate"
  false

socialInfluenceConstraint : EpistemicMediaReverseConstraint
socialInfluenceConstraint = epistemic-media-reverse-constraint
  "Social influence"
  "JRE/media-diet case"
  "listening, exposure, trust, adoption, assent, ideology and causal persuasion remain separate"
  false

climateConstraint : EpistemicMediaReverseConstraint
climateConstraint = epistemic-media-reverse-constraint
  "Climate-denial discourse"
  "climate conspiracy/distrust research"
  "physical proposition, institutional trust, conspiracy framing, ideology, media source and historical genealogy remain distinct"
  false

------------------------------------------------------------------------
-- WrongType / no-promotion firewalls.
------------------------------------------------------------------------

data InstitutionalDistrustCreatesConspiracyBelief : Set where
data AlternativeMediaCreatesDisinformationStatus : Set where
data ConspiracyQidCreatesFalsehood : Set where
data DissentCreatesMisinformation : Set where
data JoeRoganListeningCreatesManosphereMembership : Set where
data MediaConsumptionCreatesPrivateBelief : Set where
data CorrelationCreatesCausalPersuasion : Set where

institutionalDistrustDoesNotCreateConspiracyBelief : InstitutionalDistrustCreatesConspiracyBelief → ⊥
institutionalDistrustDoesNotCreateConspiracyBelief ()

alternativeMediaDoesNotCreateDisinformationStatus : AlternativeMediaCreatesDisinformationStatus → ⊥
alternativeMediaDoesNotCreateDisinformationStatus ()

conspiracyQidDoesNotCreateFalsehood : ConspiracyQidCreatesFalsehood → ⊥
conspiracyQidDoesNotCreateFalsehood ()

dissentDoesNotCreateMisinformation : DissentCreatesMisinformation → ⊥
dissentDoesNotCreateMisinformation ()

joeRoganListeningDoesNotCreateManosphereMembership : JoeRoganListeningCreatesManosphereMembership → ⊥
joeRoganListeningDoesNotCreateManosphereMembership ()

mediaConsumptionDoesNotCreatePrivateBelief : MediaConsumptionCreatesPrivateBelief → ⊥
mediaConsumptionDoesNotCreatePrivateBelief ()

correlationDoesNotCreateCausalPersuasion : CorrelationCreatesCausalPersuasion → ⊥
correlationDoesNotCreateCausalPersuasion ()

record ConspiracyDistrustAlternativeMediaBoundary : Set where
  constructor conspiracy-distrust-alternative-media-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    unresolvedDistrustIdentitiesRetained : Bool
    institutionalDistrustDoesNotDetermineConspiracism : Bool
    alternativeMediaDoesNotDetermineDisinformation : Bool
    conspiracyClassificationDoesNotPayTruthAudit : Bool
    dissentDoesNotCollapseToMisinformation : Bool
    epistemicStyleDoesNotCollapseToIdeologicalContent : Bool
    mediaConsumptionDoesNotDetermineAssent : Bool
    correlationDoesNotCreateDeterministicCausation : Bool
    sourceDateRoleAndMethodTravelWithClassification : Bool
    twoEyedComparisonRetainsInstitutionalAndParticipantPerspectives : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open ConspiracyDistrustAlternativeMediaBoundary public

canonicalConspiracyDistrustAlternativeMediaBoundary : ConspiracyDistrustAlternativeMediaBoundary
canonicalConspiracyDistrustAlternativeMediaBoundary =
  conspiracy-distrust-alternative-media-boundary
    true true true true true true true true true true true true false
