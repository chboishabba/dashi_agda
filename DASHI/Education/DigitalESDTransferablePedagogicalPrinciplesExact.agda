module DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.EducationCorpusSourceRegistry as Sources
import DASHI.Biology.AliceBrownCorpusLoom as Loom
import DASHI.Biology.CrossPaperDialecticalDevelopment as Development
import DASHI.Biology.OEFAIFeedbackFormalisationFull as Feedback
import DASHI.Biology.StudentVoiceEpistemicAgencyBridge as Voice
import DASHI.Biology.StudentIdentifiedSupportStrategiesBridge as Support
import DASHI.Biology.EcologyOfDataHyperfabricBridge as Ecology
import DASHI.Biology.ParentAllyshipMultiObserverBridge as Allyship
import DASHI.Biology.ParentalFearIntegratedFormalismExact as Situated

------------------------------------------------------------------------
-- SOURCE-ATTRIBUTED TRANSFERABLE PEDAGOGICAL PRINCIPLES
--
-- This owner recovers the generative centre of the digital-ESD manuscript:
-- established insights from the Alice Brown / colleague education corpus are
-- synthesised into candidate principles that may be transferred into a
-- transformative-ESD question.
--
-- The principles are DASHI cross-paper synthesis. They are not attributed back
-- to any one source as an empirical finding, and they do not themselves create
-- sustainability evidence. Sustainability constraints are applied downstream
-- in a separate matrix owner.
------------------------------------------------------------------------

aliceCorpus : Loom.AliceBrownCorpusLoom
aliceCorpus = Loom.canonicalAliceBrownCorpusLoom

sourceRegistry : Sources.EducationCorpusSourceRegistry
sourceRegistry = Sources.canonicalEducationCorpusSourceRegistry

developmentBraid : Development.CrossPaperDialecticalDevelopment
developmentBraid = Development.canonicalCrossPaperDialecticalDevelopment

feedbackFormalisation : Feedback.OEFAIFeedbackFormalisationFull
feedbackFormalisation = Feedback.canonicalOEFAIFeedbackFormalisationFull

voiceBridge : Voice.StudentVoiceEpistemicAgencyBridge
voiceBridge = Voice.canonicalStudentVoiceEpistemicAgencyBridge

supportBridge : Support.StudentIdentifiedSupportStrategiesBridge
supportBridge = Support.canonicalStudentIdentifiedSupportStrategiesBridge

ecologyBridge : Ecology.EcologyOfDataHyperfabricBridge
ecologyBridge = Ecology.canonicalEcologyOfDataHyperfabricBridge

allyshipBridge : Allyship.ParentAllyshipMultiObserverBridge
allyshipBridge = Allyship.canonicalParentAllyshipMultiObserverBridge

situatedConsumerBridge : Situated.ParentalFearIntegratedFormalism
situatedConsumerBridge = Situated.canonicalParentalFearIntegratedFormalism

data TransferablePedagogicalPrinciple : Set where
  situatedRelationalEngagement : TransferablePedagogicalPrinciple
  feedbackAsRevisableSignal : TransferablePedagogicalPrinciple
  constitutiveLearnerAgency : TransferablePedagogicalPrinciple
  adaptiveSupportWithLocalChoice : TransferablePedagogicalPrinciple
  pluralSituatedObservers : TransferablePedagogicalPrinciple
  contextualCustodianship : TransferablePedagogicalPrinciple
  iterativeEvidenceReturnAndRecharting : TransferablePedagogicalPrinciple

principleName : TransferablePedagogicalPrinciple → String
principleName situatedRelationalEngagement =
  "design for situated relational engagement, not access or presence alone"
principleName feedbackAsRevisableSignal =
  "treat feedback and machine classifications as revisable signals, not semantic or pedagogical authority"
principleName constitutiveLearnerAgency =
  "enable learners to shape questions, categories, interpretation, design and evidence return"
principleName adaptiveSupportWithLocalChoice =
  "route support adaptively through local context and learner choice rather than universal intervention tables"
principleName pluralSituatedObservers =
  "retain plural situated observer perspectives; no single projection is the whole educational system"
principleName contextualCustodianship =
  "retain person-place context, affordances, effort and value flows when interpreting educational data"
principleName iterativeEvidenceReturnAndRecharting =
  "return evidence for contestation and revise the educational chart rather than freezing first-pass classifications"

canonicalTransferablePrinciples : List TransferablePedagogicalPrinciple
canonicalTransferablePrinciples =
  situatedRelationalEngagement
  ∷ feedbackAsRevisableSignal
  ∷ constitutiveLearnerAgency
  ∷ adaptiveSupportWithLocalChoice
  ∷ pluralSituatedObservers
  ∷ contextualCustodianship
  ∷ iterativeEvidenceReturnAndRecharting
  ∷ []

transferablePrincipleCount : Nat
transferablePrincipleCount = 7

record TransferablePrincipleRow : Set where
  constructor transferable-principle-row
  field
    principle : TransferablePedagogicalPrinciple
    sourceSupports : List Sources.PaperReference
    claimRegister : Development.ClaimRegister
    sourceBound : Bool
    sourceBoundIsTrue : sourceBound ≡ true
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    transferReading : String
    nonPromotionBoundary : String

open TransferablePrincipleRow public

situatedRelationalEngagementRow : TransferablePrincipleRow
situatedRelationalEngagementRow =
  transferable-principle-row
    situatedRelationalEngagement
    ( Sources.humourFrameworkPaper
    ∷ Sources.onlineSupportStrategiesPaper
    ∷ Sources.ecologyOfDataPaper
    ∷ [] )
    Development.crossPaperInference
    true refl
    true refl
    "The humour framework's audience/context and feedback considerations, the student-identified interaction/scaffolding themes, and the ecology-of-data person-place account jointly motivate engagement as a situated relational design problem rather than a count of logins, access or tool presence."
    "This is a DASHI cross-paper synthesis. The three source papers do not jointly test a sustainability intervention, and engagement does not by itself establish learning or system transformation."

feedbackAsRevisableSignalRow : TransferablePrincipleRow
feedbackAsRevisableSignalRow =
  transferable-principle-row
    feedbackAsRevisableSignal
    ( Sources.aiFeedbackPaper
    ∷ Sources.voiceAgencyPaper
    ∷ Sources.ecologyOfDataPaper
    ∷ [] )
    Development.crossPaperInference
    true refl
    true refl
    "The OEF/AI paper supplies a scalable proxy-classification surface; the later voice/agency and ecology papers bound that surface by retaining human interpretation, participant contestability and hidden context. Feedback can therefore inform adaptive inquiry without becoming student meaning or pedagogical authority."
    "Classifier feasibility does not create semantic truth, causal redesign effect or authority. Later corpus papers govern use of the proxy without retroactively changing the empirical claims of the 2024 source."

constitutiveLearnerAgencyRow : TransferablePrincipleRow
constitutiveLearnerAgencyRow =
  transferable-principle-row
    constitutiveLearnerAgency
    ( Sources.voiceAgencyPaper
    ∷ Sources.onlineSupportStrategiesPaper
    ∷ Sources.humourFrameworkPaper
    ∷ [] )
    Development.crossPaperInference
    true refl
    true refl
    "Student voice is strengthened when learners can shape questions, contest coding frames, co-interpret outputs, choose or reject proposed handles and review returned evidence. Student-identified support and the humour framework provide practical surfaces against which that governance correction can be applied."
    "Survey response, feedback provision, invitation, consultation or co-design alone do not automatically constitute epistemic agency, representation or justice."

adaptiveSupportWithLocalChoiceRow : TransferablePrincipleRow
adaptiveSupportWithLocalChoiceRow =
  transferable-principle-row
    adaptiveSupportWithLocalChoice
    ( Sources.onlineSupportStrategiesPaper
    ∷ Sources.aiFeedbackPaper
    ∷ Sources.voiceAgencyPaper
    ∷ Sources.parentalFearIndependentMobilityPaper
    ∷ [] )
    Development.crossPaperInference
    true refl
    true refl
    "The five student-identified support families are many-to-many candidate handles rather than fixed interventions. The feedback and voice fibres require human review and learner choice, while the situated fear/independent-mobility work supplies a broader warning that a coarse state label can conceal different contextual intervention needs."
    "No source establishes a universal category-to-intervention table. The parental-fear transfer is a cross-domain DASHI analogy, not a claim that its empirical findings directly concern digital education or ESD."

pluralSituatedObserversRow : TransferablePrincipleRow
pluralSituatedObserversRow =
  transferable-principle-row
    pluralSituatedObservers
    ( Sources.parentalAllyshipLensPaper
    ∷ Sources.advocacyAllyshipPaper
    ∷ Sources.partnershipBarriersPaper
    ∷ Sources.voiceAgencyPaper
    ∷ [] )
    Development.crossPaperInference
    true refl
    true refl
    "The dyslexia allyship/partnership corpus distinguishes child, parent, teacher, institution and researcher perspectives and proximity to experience; the voice paper adds a direct epistemic-participation correction. Educational transformation should therefore preserve multiple situated observer fibres rather than treating one administrative, researcher or model projection as complete."
    "Parent or institutional perspectives do not substitute for learner voice; situated testimony does not automatically prove institutional intent, prevalence or universal system behaviour."

contextualCustodianshipRow : TransferablePrincipleRow
contextualCustodianshipRow =
  transferable-principle-row
    contextualCustodianship
    ( Sources.ecologyOfDataPaper
    ∷ Sources.aiFeedbackPaper
    ∷ Sources.parentalFearIndependentMobilityPaper
    ∷ [] )
    Development.crossPaperInference
    true refl
    true refl
    "The ecology-of-data work requires attention to system edges, affordances, minutiae, effort and value flows; feedback classification and the fear/independent-mobility case show why flat projections can be consumer-insufficient. Educational data should therefore remain embedded in person-place and institutional context."
    "Context-rich interpretation is not infallible and omitted context cannot be reconstructed from a comment or coarse proxy alone. The transfer to digital-ESD is a synthesis hypothesis requiring context-sensitive testing."

iterativeEvidenceReturnAndRechartingRow : TransferablePrincipleRow
iterativeEvidenceReturnAndRechartingRow =
  transferable-principle-row
    iterativeEvidenceReturnAndRecharting
    ( Sources.voiceAgencyPaper
    ∷ Sources.aiFeedbackPaper
    ∷ Sources.ecologyOfDataPaper
    ∷ Sources.onlineSupportStrategiesPaper
    ∷ [] )
    Development.crossPaperInference
    true refl
    true refl
    "The corpus-level developmental braid culminates in co-designed local enactment, evidence return and revision. Digital-education interventions should therefore be treated as revisable hypotheses whose classifications, support choices and interpretations can be contested and recharted as new evidence appears."
    "This developmental sequence is a DASHI corpus synthesis, not an empirical longitudinal finding reported by any one paper. Revision does not imply that earlier source contributions were false or should be erased."

canonicalTransferablePrincipleRows : List TransferablePrincipleRow
canonicalTransferablePrincipleRows =
  situatedRelationalEngagementRow
  ∷ feedbackAsRevisableSignalRow
  ∷ constitutiveLearnerAgencyRow
  ∷ adaptiveSupportWithLocalChoiceRow
  ∷ pluralSituatedObserversRow
  ∷ contextualCustodianshipRow
  ∷ iterativeEvidenceReturnAndRechartingRow
  ∷ []

------------------------------------------------------------------------
-- Transfer/promotion firewalls.
------------------------------------------------------------------------

data CrossPaperPrincipleIsAliceEmpiricalFinding : Set where
data PrincipleCreatesSustainabilityEvidence : Set where
data PrincipleCreatesUniversalPrescription : Set where
data CoarseProxyDeterminesContextAdequateIntervention : Set where

crossPaperPrincipleIsNotAliceEmpiricalFinding :
  CrossPaperPrincipleIsAliceEmpiricalFinding → ⊥
crossPaperPrincipleIsNotAliceEmpiricalFinding ()

principleDoesNotCreateSustainabilityEvidence :
  PrincipleCreatesSustainabilityEvidence → ⊥
principleDoesNotCreateSustainabilityEvidence ()

principleDoesNotCreateUniversalPrescription :
  PrincipleCreatesUniversalPrescription → ⊥
principleDoesNotCreateUniversalPrescription ()

coarseProxyDoesNotDetermineContextAdequateIntervention :
  CoarseProxyDeterminesContextAdequateIntervention → ⊥
coarseProxyDoesNotDetermineContextAdequateIntervention ()

record TransferablePrinciplesBoundary : Set where
  constructor transferable-principles-boundary
  field
    sourceFibresRetained : Bool
    sourceFibresRetainedIsTrue : sourceFibresRetained ≡ true
    developmentalBraidRetained : Bool
    developmentalBraidRetainedIsTrue : developmentalBraidRetained ≡ true
    localChoiceRetained : Bool
    localChoiceRetainedIsTrue : localChoiceRetained ≡ true
    pluralObserversRetained : Bool
    pluralObserversRetainedIsTrue : pluralObserversRetained ≡ true
    contextualInterpretationRetained : Bool
    contextualInterpretationRetainedIsTrue : contextualInterpretationRetained ≡ true
    evidenceReturnAndRevisionRetained : Bool
    evidenceReturnAndRevisionRetainedIsTrue : evidenceReturnAndRevisionRetained ≡ true
    crossPaperPrinciplesAreAliceEmpiricalFindings : Bool
    crossPaperPrinciplesAreAliceEmpiricalFindingsIsFalse :
      crossPaperPrinciplesAreAliceEmpiricalFindings ≡ false
    principlesCreateSustainabilityEvidence : Bool
    principlesCreateSustainabilityEvidenceIsFalse :
      principlesCreateSustainabilityEvidence ≡ false
    principlesCreateUniversalPrescriptions : Bool
    principlesCreateUniversalPrescriptionsIsFalse :
      principlesCreateUniversalPrescriptions ≡ false
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

open TransferablePrinciplesBoundary public

canonicalTransferablePrinciplesBoundary : TransferablePrinciplesBoundary
canonicalTransferablePrinciplesBoundary =
  transferable-principles-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl

transferablePrinciplesReading : String
transferablePrinciplesReading =
  "The Alice Brown / colleague corpus supports a candidate seven-principle cross-paper synthesis: situated relational engagement; feedback as revisable signal; constitutive learner agency; adaptive support with local choice; plural situated observers; contextual custodianship; and iterative evidence return/recharting. Each principle preserves its source fibres and non-promotion boundaries. The principles are not attributed back to the source papers as empirical findings and do not yet create sustainability evidence; downstream digital-ESD cross-pollination must add independent sustainability constraints and evidence."
