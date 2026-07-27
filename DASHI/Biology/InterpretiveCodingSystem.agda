module DASHI.Biology.InterpretiveCodingSystem where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.EducationCorpusSourceRegistry as Sources
import DASHI.Biology.HumanCodingMachineCompilationBridge as MachineCoding

------------------------------------------------------------------------
-- General interpretive-coding interface.
--
-- Manual thematic/content analysis and supervised machine classification are
-- not treated as opposites.  Both transform a source surface through a coding
-- frame and an interpreter.  The key governance questions are where the
-- interpretation lives, what uncertainty is retained, and who may contest it.

data InterpretiveMethod : Set where
  thematicAnalysisMethod : InterpretiveMethod
  qualitativeContentAnalysisMethod : InterpretiveMethod
  supervisedMachineClassificationMethod : InterpretiveMethod
  studentCoAnalysisMethod : InterpretiveMethod
  ecologyOfDataCustodianshipMethod : InterpretiveMethod

canonicalInterpretiveMethods : List InterpretiveMethod
canonicalInterpretiveMethods =
  thematicAnalysisMethod
  ∷ qualitativeContentAnalysisMethod
  ∷ supervisedMachineClassificationMethod
  ∷ studentCoAnalysisMethod
  ∷ ecologyOfDataCustodianshipMethod
  ∷ []

methodName : InterpretiveMethod → String
methodName thematicAnalysisMethod = "thematic analysis"
methodName qualitativeContentAnalysisMethod = "qualitative content analysis"
methodName supervisedMachineClassificationMethod = "supervised machine classification"
methodName studentCoAnalysisMethod = "student co-analysis"
methodName ecologyOfDataCustodianshipMethod = "ecology-of-data custodianship"

record InterpretiveCodingRow : Set where
  constructor mkInterpretiveCodingRow
  field
    method : InterpretiveMethod
    sourceSurface : String
    codingFrame : String
    interpreterLocation : String
    producedCodes : String
    uncertaintySurface : String
    reflexivityReceipt : String
    missingnessReceipt : String
    contestabilityRoute : String
    interpretationExplicit : Bool
    interpretationExplicitIsTrue : interpretationExplicit ≡ true
    outputCandidateOnly : Bool
    outputCandidateOnlyIsTrue : outputCandidateOnly ≡ true
    outputNotSemanticIdentity : Bool
    outputNotSemanticIdentityIsTrue : outputNotSemanticIdentity ≡ true

open InterpretiveCodingRow public

canonicalThematicAnalysisRow : InterpretiveCodingRow
canonicalThematicAnalysisRow =
  mkInterpretiveCodingRow
    thematicAnalysisMethod
    "qualitative participant material"
    "researcher-developed or theory-informed coding frame"
    "researcher judgement throughout coding and theme construction"
    "themes and interpretive relationships"
    "ambiguity, coding disagreement and alternative theme structures"
    "researcher positionality and analytic decisions"
    "silences, absent cases and unrepresented context"
    "participant, peer and methodological review"
    true refl true refl true refl

canonicalQualitativeContentAnalysisRow : InterpretiveCodingRow
canonicalQualitativeContentAnalysisRow =
  mkInterpretiveCodingRow
    qualitativeContentAnalysisMethod
    "textual source material"
    "inductive or deductive category frame"
    "human coding decisions and category rules"
    "category assignments, frequencies and interpretations"
    "category ambiguity, coder variation and context loss"
    "stepwise coding-rule and decision record"
    "uncoded, ambiguous and absent material"
    "coder reconciliation and participant/contextual review"
    true refl true refl true refl

canonicalSupervisedMachineClassificationRow : InterpretiveCodingRow
canonicalSupervisedMachineClassificationRow =
  mkInterpretiveCodingRow
    supervisedMachineClassificationMethod
    "preprocessed feedback text"
    "human-labelled training frame"
    "human labels compiled through training procedure and model parameters"
    "predicted labels, scores and aggregate visualisations"
    "classification metrics, class imbalance and out-of-distribution cases"
    "label provenance, model version and evaluation receipt"
    "non-response, omitted context, low-recall classes and silent cohorts"
    "human and participant review of labels and downstream use"
    true refl true refl true refl

canonicalStudentCoAnalysisRow : InterpretiveCodingRow
canonicalStudentCoAnalysisRow =
  mkInterpretiveCodingRow
    studentCoAnalysisMethod
    "student-generated and institutionally held evidence surfaces"
    "co-developed questions, codes and relevance criteria"
    "students and researchers as plural situated interpreters"
    "co-interpreted themes, disagreements and action candidates"
    "differences among students and limits of representation"
    "record of participation, disagreement and decision power"
    "non-participating, marginalised and dissenting student positions"
    "ongoing opt-in, contestation and evidence-return review"
    true refl true refl true refl

canonicalEcologyCustodianshipRow : InterpretiveCodingRow
canonicalEcologyCustodianshipRow =
  mkInterpretiveCodingRow
    ecologyOfDataCustodianshipMethod
    "person-place ecology of qualitative material"
    "eco-behavioural attention to systems, affordances, minutiae and value flows"
    "researcher as responsible custodian learning with data"
    "context-rich pathways and relational findings"
    "unseen system edges, value flows and alternative ecological readings"
    "custodianship, context and value-flow audit"
    "lost places, silenced agencies and flattened context"
    "participant and community contestation of curation"
    true refl true refl true refl

canonicalInterpretiveCodingRows : List InterpretiveCodingRow
canonicalInterpretiveCodingRows =
  canonicalThematicAnalysisRow
  ∷ canonicalQualitativeContentAnalysisRow
  ∷ canonicalSupervisedMachineClassificationRow
  ∷ canonicalStudentCoAnalysisRow
  ∷ canonicalEcologyCustodianshipRow
  ∷ []

record InterpretiveCodingSystem : Set where
  constructor mkInterpretiveCodingSystem
  field
    sourceRegistry : Sources.EducationCorpusSourceRegistry
    sourceRegistryIsCanonical :
      sourceRegistry ≡ Sources.canonicalEducationCorpusSourceRegistry
    machineCompilationBridge : MachineCoding.HumanCodingMachineCompilationBridge
    machineCompilationBridgeIsCanonical :
      machineCompilationBridge ≡
      MachineCoding.canonicalHumanCodingMachineCompilationBridge
    methods : List InterpretiveMethod
    methodsAreCanonical : methods ≡ canonicalInterpretiveMethods
    rows : List InterpretiveCodingRow
    rowsAreCanonical : rows ≡ canonicalInterpretiveCodingRows
    machineDoesNotRemoveInterpretation : Bool
    machineDoesNotRemoveInterpretationIsTrue :
      machineDoesNotRemoveInterpretation ≡ true
    manualDoesNotGuaranteeTruth : Bool
    manualDoesNotGuaranteeTruthIsTrue : manualDoesNotGuaranteeTruth ≡ true
    participantContestabilityRequired : Bool
    participantContestabilityRequiredIsTrue :
      participantContestabilityRequired ≡ true
    methodOutputsRemainCandidates : Bool
    methodOutputsRemainCandidatesIsTrue :
      methodOutputsRemainCandidates ≡ true
    reading : String

open InterpretiveCodingSystem public

canonicalInterpretiveCodingSystem : InterpretiveCodingSystem
canonicalInterpretiveCodingSystem =
  mkInterpretiveCodingSystem
    Sources.canonicalEducationCorpusSourceRegistry refl
    MachineCoding.canonicalHumanCodingMachineCompilationBridge refl
    canonicalInterpretiveMethods refl
    canonicalInterpretiveCodingRows refl
    true refl
    true refl
    true refl
    true refl
    "Manual thematic/content analysis and supervised machine classification are typed as related interpretive systems. The machine compiles a human coding frame; manual interpretation also remains situated. Both require uncertainty, reflexivity, missingness and contestability receipts before downstream promotion."
