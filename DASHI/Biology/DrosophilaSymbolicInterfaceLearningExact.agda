module DASHI.Biology.DrosophilaSymbolicInterfaceLearningExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.AnimalexicDrosophilaEmbodiedBridge as Animalexic
import DASHI.Biology.DrosophilaMaleCNSEffectorObservationBridge as Fly
import DASHI.Cognition.PNF.DecisionOutcomeLearningFeedbackExact as Feedback
import DASHI.Cognition.PNF.JamesSensorimotorDecisionActionExact as James
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.IntersectionalNonFactorability as NF

------------------------------------------------------------------------
-- VIRAL DROSOPHILA -> SYMBOLIC-INTERFACE FORMALISATION
--
-- This owner formalises the interface/evaluation geometry of the current
-- "fruit fly writes Python" demo wave. It does not identify a connectome map
-- with executable dynamics, a software simulation with living-fly cognition,
-- emitted symbols with semantic understanding, or one FizzBuzz success with
-- general programming competence.
------------------------------------------------------------------------

socialDemoSource : Source.AttributedSource
socialDemoSource = Source.mkNoDOISource
  "social/demo account (display name/identity not promoted)"
  "fruit fly writes Python / FizzBuzz demonstration"
  "viral social-media demonstration"
  "2026"
  "https://www.instagram.com/p/DdLhMMaJFdV/"
  (Source.namedSourceKind "social demo")
  "demo/claim locator only; does not by itself pay hidden implementation details, biological authority, or person identity"
  Source.publicAttribution

socialDemoCitationImportsNoProof :
  Source.citationImportsProof socialDemoSource ≡ false
socialDemoCitationImportsNoProof = Source.citationImportsProofIsFalse socialDemoSource

socialDemoCitationCreatesNoAuthority :
  Source.citationCreatesAuthority socialDemoSource ≡ false
socialDemoCitationCreatesNoAuthority = Source.citationCreatesAuthorityIsFalse socialDemoSource

------------------------------------------------------------------------
-- Implementation-recovery debt.
------------------------------------------------------------------------

record PythonDemoImplementationDebt : Set where
  constructor pythonDemoImplementationDebt
  field
    viralClaimLocatorPresent : Bool
    viralClaimLocatorPresentIsTrue : viralClaimLocatorPresent ≡ true
    primaryImplementationLocated : Bool
    dynamicsReceiptPresent : Bool
    decoderReceiptPresent : Bool
    trainingRuleReceiptPresent : Bool
    evaluatorReceiptPresent : Bool
    exactFizzBuzzArtifactPresent : Bool
    personIdentityWeldPresent : Bool
    recoveryReading : String

open PythonDemoImplementationDebt public

canonicalPythonDemoImplementationDebt : PythonDemoImplementationDebt
canonicalPythonDemoImplementationDebt = pythonDemoImplementationDebt
  true
  refl
  false
  false
  false
  false
  false
  false
  false
  "viral claim located; first-party Python demo code/config, exact dynamics, neural-to-key decoder, training rule, evaluator, emitted artifact, and same-object person identity remain unpaid"

primaryImplementationStillUnpaid :
  primaryImplementationLocated canonicalPythonDemoImplementationDebt ≡ false
primaryImplementationStillUnpaid = refl

exactFizzBuzzArtifactStillUnpaid :
  exactFizzBuzzArtifactPresent canonicalPythonDemoImplementationDebt ≡ false
exactFizzBuzzArtifactStillUnpaid = refl

------------------------------------------------------------------------
-- Object-indexed social/demo evidence.
--
-- Current public evidence says the adjacent Capy Tetris object used "1 prompt
-- and Slack".  That assistance fact is useful, but it belongs to a different
-- run.  It cannot be copied across to the Python/FizzBuzz object without a
-- same-object receipt.
------------------------------------------------------------------------

data DemoObject : Set where
  pythonFizzBuzzDemo : DemoObject
  capyTetrisDemo : DemoObject

data AssistanceFact : DemoObject → Set where
  tetrisOnePromptAndSlack : AssistanceFact capyTetrisDemo

data AdjacentDemoAssistanceTransferPermission : Set where

adjacentDemoAssistanceDoesNotTransferToPythonRun :
  AdjacentDemoAssistanceTransferPermission → ⊥
adjacentDemoAssistanceDoesNotTransferToPythonRun ()

------------------------------------------------------------------------
-- Identity evidence is also stratified.  We can retain strong cross-platform
-- corroboration without silently upgrading it to a strict same-object receipt
-- for the exact social-demo account/run.
------------------------------------------------------------------------

record IdentityCorroboration : Set where
  constructor identityCorroboration
  field
    xHandleStatesCapyCofounder : Bool
    ycNamesNalinSemwalCapyFounder : Bool
    huggingFaceLordsplineNamesNalinSemwal : Bool
    sameObjectReceiptPresent : Bool

open IdentityCorroboration public

canonicalIdentityCorroboration : IdentityCorroboration
canonicalIdentityCorroboration = identityCorroboration true true true false

data CorroboratedIdentityPromotionPermission : Set where

stronglyCorroboratedIdentityStillIsNotSameObjectReceipt :
  CorroboratedIdentityPromotionPermission → ⊥
stronglyCorroboratedIdentityStillIsNotSameObjectReceipt ()

sameObjectIdentityStillUnpaid :
  sameObjectReceiptPresent canonicalIdentityCorroboration ≡ false
sameObjectIdentityStillUnpaid = refl

------------------------------------------------------------------------
-- Typed carrier layers.
------------------------------------------------------------------------

data ConnectomeState : Set where
  structuralConnectomeState : ConnectomeState

data ExecutableState : Set where
  quiescentExecutableState : ExecutableState
  activeExecutableState : ExecutableState

data NeuralObservation : Set where
  noObservedActivation : NeuralObservation
  tokenDriveObserved : NeuralObservation

data ActuatorKind : Set where
  biologicalEffector : ActuatorKind
  artificialSymbolicActuator : ActuatorKind

data Symbol : Set where
  symbolF : Symbol
  symbolI : Symbol
  symbolZ : Symbol
  symbolB : Symbol
  symbolU : Symbol
  symbolColon : Symbol
  symbolNewline : Symbol
  symbolOther : Symbol

data ProgramText : Set where
  emptyProgram : ProgramText
  candidateFizzBuzzProgram : ProgramText

data ParseResult : Set where
  parseFailure : ParseResult
  parseSuccess : ParseResult

data RuntimeResult : Set where
  runtimeFailure : RuntimeResult
  runtimeSuccess : RuntimeResult

data TaskFeedback : Set where
  noTaskCredit : TaskFeedback
  taskCredit : TaskFeedback

data LearningStatus : Set where
  noLearningReceipt : LearningStatus
  updateApplied : LearningStatus

data CompetenceLevel : Set where
  neuralActivityOnly : CompetenceLevel
  mappedTokenEmission : CompetenceLevel
  nonemptyProgramText : CompetenceLevel
  pythonParses : CompetenceLevel
  pythonExecutes : CompetenceLevel
  fizzBuzzDeclaredCases : CompetenceLevel
  fizzBuzzHeldOutCases : CompetenceLevel
  crossTaskTransfer : CompetenceLevel
  generalProgrammingCompetence : CompetenceLevel

record AssistanceBudget : Set where
  constructor assistanceBudget
  field
    inputEncoding : String
    dynamicsRule : String
    initialStateOrSeed : String
    decoderMapping : String
    updateRule : String
    rewardOrEvaluator : String
    promptOrScaffold : String
    parserRuntime : String
    attemptBudget : Nat
    selectionPolicy : String

open AssistanceBudget public

record SymbolicInterfaceExperiment : Set where
  constructor symbolicInterfaceExperiment
  field
    connectomeReceipt : Fly.ScientificSourceReceipt
    connectomeState : ConnectomeState
    executableState : ExecutableState
    actuatorKind : ActuatorKind
    assistance : AssistanceBudget

    neuralStep : ExecutableState → ExecutableState
    observeNeural : ExecutableState → NeuralObservation
    decodeSymbol : ExecutableState → Symbol
    renderProgram : List Symbol → ProgramText
    parseProgram : ProgramText → ParseResult
    runProgram : ProgramText → RuntimeResult
    evaluateFeedback : ProgramText → TaskFeedback
    learningStatus : LearningStatus
    competence : CompetenceLevel

open SymbolicInterfaceExperiment public

------------------------------------------------------------------------
-- Minimal finite symbolic interface witness.
------------------------------------------------------------------------

canonicalAssistanceBudget : AssistanceBudget
canonicalAssistanceBudget = assistanceBudget
  "external sensory/task encoding"
  "connectome-constrained executable dynamics must be separately specified"
  "declared initialization required"
  "neural-state to keyboard/token decoder is external interface semantics"
  "declared update/training rule required"
  "declared FizzBuzz evaluator/reward required"
  "prompt/template/scaffold must be disclosed if used"
  "Python parser/runtime is external evaluator infrastructure"
  1
  "no cherry-picking claim without an explicit selection receipt"

canonicalSocialDemoExperiment : SymbolicInterfaceExperiment
canonicalSocialDemoExperiment = symbolicInterfaceExperiment
  Fly.maleCNSSource
  structuralConnectomeState
  activeExecutableState
  artificialSymbolicActuator
  canonicalAssistanceBudget
  (λ state → state)
  (λ _ → tokenDriveObserved)
  (λ _ → symbolOther)
  (λ _ → candidateFizzBuzzProgram)
  (λ _ → parseSuccess)
  (λ _ → runtimeSuccess)
  (λ _ → taskCredit)
  noLearningReceipt
  mappedTokenEmission

------------------------------------------------------------------------
-- Output nonfactorability: the same emitted program text can coexist with
-- different executable/neural states. Recharting the program text cannot
-- recover neural information erased by that projection.
------------------------------------------------------------------------

programTextProjection : ExecutableState → ProgramText
programTextProjection _ = candidateFizzBuzzProgram

neuralObservationProjection : ExecutableState → NeuralObservation
neuralObservationProjection quiescentExecutableState = noObservedActivation
neuralObservationProjection activeExecutableState = tokenDriveObserved

sameProgramTextAcrossExecutableStates :
  programTextProjection quiescentExecutableState
  ≡ programTextProjection activeExecutableState
sameProgramTextAcrossExecutableStates = refl

neuralObservationsStillDiffer :
  neuralObservationProjection quiescentExecutableState
  ≡ neuralObservationProjection activeExecutableState → ⊥
neuralObservationsStillDiffer ()

programTextNeuralNonFactorabilityWitness :
  NF.NonFactorabilityWitness programTextProjection neuralObservationProjection
programTextNeuralNonFactorabilityWitness =
  NF.nonFactorabilityWitness
    quiescentExecutableState
    activeExecutableState
    sameProgramTextAcrossExecutableStates
    neuralObservationsStillDiffer

programTextDoesNotRecoverNeuralObservation :
  NF.FactorsThrough programTextProjection neuralObservationProjection → ⊥
programTextDoesNotRecoverNeuralObservation =
  NF.witnessRulesOutEveryFlatFactorisation
    programTextNeuralNonFactorabilityWitness

------------------------------------------------------------------------
-- Learning/update lane is distinct from interface success.
------------------------------------------------------------------------

learningUpdateWitness : Memory.MemoryFibre → Memory.MemoryFibre
learningUpdateWitness = Feedback.learnFromOutcome Feedback.reinforcingOutcome

jamesActiveSensingBoundary : James.JamesWrongTypeBoundary
jamesActiveSensingBoundary = James.canonicalJamesWrongTypeBoundary

------------------------------------------------------------------------
-- Explicit WrongType / no-promotion boundaries.
------------------------------------------------------------------------

data ConnectomeExecutableCollapsePermission : Set where

data SimulatedLivingFlyCollapsePermission : Set where

data ArtificialBiologicalActuatorCollapsePermission : Set where

data EmittedCharactersPythonKnowledgePermission : Set where

data SyntaxTaskCorrectnessPermission : Set where

data FizzBuzzGeneralProgrammingPermission : Set where

data SuccessfulRunLearnedPolicyPermission : Set where

data LearningBiologicalPlasticityPermission : Set where

data SocialCaptionTechnicalReceiptPermission : Set where

data SecondaryPrimaryImplementationPermission : Set where

data SharedDisplayNamePersonIdentityPermission : Set where

data ConnectomeCausalAdvantagePermission : Set where

connectomeDoesNotDetermineExecutableDynamics :
  ConnectomeExecutableCollapsePermission → ⊥
connectomeDoesNotDetermineExecutableDynamics ()

simulatedDynamicsDoNotEstablishLivingFlyCognition :
  SimulatedLivingFlyCollapsePermission → ⊥
simulatedDynamicsDoNotEstablishLivingFlyCognition ()

artificialActuatorDoesNotEqualBiologicalEffector :
  ArtificialBiologicalActuatorCollapsePermission → ⊥
artificialActuatorDoesNotEqualBiologicalEffector ()

emittedCharactersDoNotEstablishPythonKnowledge :
  EmittedCharactersPythonKnowledgePermission → ⊥
emittedCharactersDoNotEstablishPythonKnowledge ()

validSyntaxDoesNotEstablishTaskCorrectness :
  SyntaxTaskCorrectnessPermission → ⊥
validSyntaxDoesNotEstablishTaskCorrectness ()

fizzBuzzDoesNotEstablishGeneralProgrammingCompetence :
  FizzBuzzGeneralProgrammingPermission → ⊥
fizzBuzzDoesNotEstablishGeneralProgrammingCompetence ()

successfulRunDoesNotEstablishLearnedPolicy :
  SuccessfulRunLearnedPolicyPermission → ⊥
successfulRunDoesNotEstablishLearnedPolicy ()

learningUpdateDoesNotEstablishBiologicalPlasticity :
  LearningBiologicalPlasticityPermission → ⊥
learningUpdateDoesNotEstablishBiologicalPlasticity ()

socialCaptionDoesNotPayTechnicalImplementation :
  SocialCaptionTechnicalReceiptPermission → ⊥
socialCaptionDoesNotPayTechnicalImplementation ()

secondaryReportDoesNotPayPrimaryImplementation :
  SecondaryPrimaryImplementationPermission → ⊥
secondaryReportDoesNotPayPrimaryImplementation ()

sharedDisplayNameDoesNotEstablishPersonIdentity :
  SharedDisplayNamePersonIdentityPermission → ⊥
sharedDisplayNameDoesNotEstablishPersonIdentity ()

------------------------------------------------------------------------
-- Null-model obligations for any stronger "biological topology advantage"
-- claim.
------------------------------------------------------------------------

data NullModelKind : Set where
  degreePreservingRewire : NullModelKind
  shuffledNeuronIdentity : NullModelKind
  matchedGenericRecurrentNetwork : NullModelKind
  identicalDecoderNoLearning : NullModelKind
  alternateInitialization : NullModelKind

record NullComparisonObligation : Set where
  constructor nullComparisonObligation
  field
    requiredNulls : List NullModelKind
    sameTaskInterfaceBudgetRequired : Bool
    sameTaskInterfaceBudgetRequiredIsTrue :
      sameTaskInterfaceBudgetRequired ≡ true
    empiricalNullReceiptPresent : Bool

open NullComparisonObligation public

canonicalNullComparisonObligation : NullComparisonObligation
canonicalNullComparisonObligation = nullComparisonObligation
  (degreePreservingRewire
    ∷ shuffledNeuronIdentity
    ∷ matchedGenericRecurrentNetwork
    ∷ identicalDecoderNoLearning
    ∷ alternateInitialization
    ∷ [])
  true
  refl
  false

connectomeAdvantageRequiresNullComparison :
  ConnectomeCausalAdvantagePermission → ⊥
connectomeAdvantageRequiresNullComparison ()

------------------------------------------------------------------------
-- Cross-pollination with Animalexic.
------------------------------------------------------------------------

animalexicBoundary : Animalexic.DrosophilaAnimalexicBoundary
animalexicBoundary = Animalexic.noNeuralStateEqualsBehaviourMotif

record SymbolicInterfaceBoundarySummary : Set where
  constructor symbolicInterfaceBoundarySummary
  field
    keyboardIsBiologicalEffector : Bool
    emittedTextIsPythonKnowledge : Bool
    fizzBuzzIsGeneralProgramming : Bool
    oneRunProvesLearning : Bool
    connectomeTopologyAdvantagePaid : Bool
    metaphysicalDeterminismPaid : Bool
    libertarianFreeWillPaid : Bool

open SymbolicInterfaceBoundarySummary public

canonicalSymbolicInterfaceBoundarySummary : SymbolicInterfaceBoundarySummary
canonicalSymbolicInterfaceBoundarySummary = symbolicInterfaceBoundarySummary
  false false false false false false false

jamesDeterminismBoundaryPreserved :
  metaphysicalDeterminismPaid canonicalSymbolicInterfaceBoundarySummary ≡ false
jamesDeterminismBoundaryPreserved = refl

jamesFreeWillBoundaryPreserved :
  libertarianFreeWillPaid canonicalSymbolicInterfaceBoundarySummary ≡ false
jamesFreeWillBoundaryPreserved = refl
