module DASHI.Education.DigitalESDPrincipleSurvivalAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact as Digital
import DASHI.Education.DigitalESDEfSIndependentChallengeExact as EfS
import DASHI.Education.DigitalESDEvidenceBraidTensionExact as Braid

-- A conceptual comparison is not a completed corpus adjudication. A source
-- register names potentially relevant papers; it does not prove source spans,
-- independent effect, representativeness, or admitted review inclusion.
data SurvivalVerdict : Set where
  provisionallyRetain : SurvivalVerdict
  provisionalRevisionNeeded : SurvivalVerdict
  provisionalSplitCandidate : SurvivalVerdict
  empiricalStatusUnresolved : SurvivalVerdict

data ReviewStage : Set where
  attributedPreSearchSynthesis : ReviewStage
  fullTextSpanReviewed : ReviewStage
  sourceAuditAdmitted : ReviewStage
  crossCorpusAdjudicated : ReviewStage

record PrincipleSurvivalReceipt : Set where
  constructor survival
  field
    principle : Digital.TransferablePedagogicalPrinciple
    sourceScope : String
    existingSupport : String
    counterEvidenceOrBlindSpot : String
    relevantContexts : String
    candidateVerdict : SurvivalVerdict
    currentReviewStage : ReviewStage
    nextDiscriminator : String
    actualCorpusAdjudicationObserved : Bool
    notYetAdjudicated : actualCorpusAdjudicationObserved ≡ true → ⊥
open PrincipleSurvivalReceipt public

engagement : PrincipleSurvivalReceipt
engagement = survival Digital.situatedRelationalEngagement
  "Online higher education, teacher-education support, humour pedagogy, ecology of data"
  "Source-attributed digital corpus supports the need to distinguish access from relational engagement; EfS educator-practice critique provides a challenge to mere topic coverage."
  "Engagement does not establish systems learning, ecological concern or collective action."
  "Higher education and regional teacher education; Norwegian ECE is a non-transferred challenge context."
  provisionalRevisionNeeded attributedPreSearchSynthesis
  "Retain situated engagement as mechanism, separately measure EfS understanding and transformative enactment."
  false (λ ())

feedback : PrincipleSurvivalReceipt
feedback = survival Digital.feedbackAsRevisableSignal
  "OEF/AI feedback feasibility and higher-education student voice"
  "Classification feasibility plus voice/agency and data-ecology critiques support provisional interpretive revisability."
  "Algorithmic feedback is not values reflection, ecological evaluation, student authority or outcome improvement."
  "Higher education; sustainability normative conflict still requires independent evidence."
  provisionalRevisionNeeded attributedPreSearchSynthesis
  "Find source spans for contested sustainability-value discussions and compare feedback-only versus deliberative activities."
  false (λ ())

agency : PrincipleSurvivalReceipt
agency = survival Digital.constitutiveLearnerAgency
  "Student-voice scholarship and student-identified online supports"
  "Epistemic expansion arguments support involving learners in interpretation and educational design."
  "Individual agency does not guarantee consequential collective decision rights or political efficacy."
  "Higher-education student voice; ECE collective action needs explicit context transfer."
  provisionalSplitCandidate attributedPreSearchSynthesis
  "Discriminate individual voice, co-design, group deliberation, decision authority and realised collective action."
  false (λ ())

support : PrincipleSurvivalReceipt
support = survival Digital.adaptiveSupportWithLocalChoice
  "Regional Australian teacher education: 584 student responses; feedback-support cross-paper inference"
  "Five candidate support families with locally selectable many-to-many routing."
  "No causal universal strategy table; personalisation could weaken or enable collective inquiry."
  "Australian regional teacher education; transfer to other cohorts and EfS projects remains open."
  provisionalRevisionNeeded attributedPreSearchSynthesis
  "Compare inclusive adaptive supports with sustained collective EfS participation and learner choice."
  false (λ ())

observers : PrincipleSurvivalReceipt
observers = survival Digital.pluralSituatedObservers
  "Disability allyship, parent-school partnerships, student voice and ecological observer formalism"
  "Distinct observers and different knowledge histories cannot be silently flattened."
  "Parent voice cannot replace child voice; scientific ecological indicators cannot impersonate non-human testimony or Indigenous authority."
  "Disability and student-voice contexts; ecological contexts require source-specific scope."
  provisionalRevisionNeeded attributedPreSearchSynthesis
  "Audit observer provenance, relevant non-human observations and community-specific authority."
  false (λ ())

custodianship : PrincipleSurvivalReceipt
custodianship = survival Digital.contextualCustodianship
  "Ecology-of-data qualitative methodology and situated cross-domain caution"
  "Person-place, value-flow, affordance and data-curation responsibilities motivate context-rich interpretation."
  "Context representation is not demonstrated systems-thinking competence or complete ecological interpretation."
  "Situated qualitative research; transfer to EfS field cases remains to be observed."
  provisionalRevisionNeeded attributedPreSearchSynthesis
  "Test when omitting ecological, intergenerational or authority coordinates changes the educational conclusion."
  false (λ ())

revision : PrincipleSurvivalReceipt
revision = survival Digital.iterativeEvidenceReturnAndRecharting
  "Cross-paper digital feedback, student voice, support and data ecology"
  "Evidence return and contestable revision form an attributable synthesis hypothesis."
  "Revision of interpretations is not futures literacy, longitudinal transformation or actual collective action."
  "Online higher education; future-oriented sustainability teaching requires separate outcome data."
  provisionalRevisionNeeded attributedPreSearchSynthesis
  "Compare counterfactual futures reasoning and observed institutional change across follow-up periods."
  false (λ ())

canonicalSurvivalReceipts : List PrincipleSurvivalReceipt
canonicalSurvivalReceipts =
  engagement ∷ feedback ∷ agency ∷ support ∷ observers ∷ custodianship ∷ revision ∷ []

-- Review-stage separation: none of the seven is marked as independently
-- screened, fully extracted and cross-corpus adjudicated on this source ledger.
data SevenPrinciplesEmpiricallyValidated : Set where
data SevenPrinciplesDefeatedByEfS : Set where
noPrematureValidation : SevenPrinciplesEmpiricallyValidated → ⊥
noPrematureValidation ()
noPrematureDefeat : SevenPrinciplesDefeatedByEfS → ⊥
noPrematureDefeat ()
