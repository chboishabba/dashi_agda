module DASHI.Reasoning.MetaphorAlignmentMisunderstanding where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Metaphor, succinct communication, and misunderstanding.
--
-- This is a theorem-thin surface for the thread content.  It names the
-- carriers and receipts needed to talk about:
--
--   * metaphor / simile correctness as partial operator-equivalence
--     alignment;
--   * communicative succinctness as MDL-style preservation of intended
--     invariants under an observer context;
--   * interpersonal misunderstanding as failed manifold / invariant
--     alignment across observer quotients.
--
-- It is intentionally not a theory of perfect understanding, qualia
-- recovery, universal exact translation, or context-free communication
-- optimality.

data AnalogyForm : Set where
  metaphorForm :
    AnalogyForm

  simileForm :
    AnalogyForm

data AlignmentStatus : Set where
  alignedOnDeclaredSlice :
    AlignmentStatus

  partialAlignmentOnly :
    AlignmentStatus

  failedAlignment :
    AlignmentStatus

  receiptMissing :
    AlignmentStatus

data MisunderstandingFailureMode : Set where
  vocabularyMismatch :
    MisunderstandingFailureMode

  ontologyMismatch :
    MisunderstandingFailureMode

  contextMismatch :
    MisunderstandingFailureMode

  emotionalStateMismatch :
    MisunderstandingFailureMode

  scopeMismatch :
    MisunderstandingFailureMode

  intentProjectionMismatch :
    MisunderstandingFailureMode

canonicalMisunderstandingFailureModes :
  List MisunderstandingFailureMode
canonicalMisunderstandingFailureModes =
  vocabularyMismatch
  ∷ ontologyMismatch
  ∷ contextMismatch
  ∷ emotionalStateMismatch
  ∷ scopeMismatch
  ∷ intentProjectionMismatch
  ∷ []

data CommunicationNonClaimGuard : Set where
  noGuaranteedPerfectUnderstanding :
    CommunicationNonClaimGuard

  noQualiaRecovery :
    CommunicationNonClaimGuard

  noUniversalExactTranslation :
    CommunicationNonClaimGuard

  noCommunicationOptimalityWithoutAudienceContextReceipts :
    CommunicationNonClaimGuard

canonicalCommunicationNonClaimGuards :
  List CommunicationNonClaimGuard
canonicalCommunicationNonClaimGuards =
  noGuaranteedPerfectUnderstanding
  ∷ noQualiaRecovery
  ∷ noUniversalExactTranslation
  ∷ noCommunicationOptimalityWithoutAudienceContextReceipts
  ∷ []

------------------------------------------------------------------------
-- Observer quotient and context carriers.

record ObserverQuotient : Set₁ where
  field
    LatentExperience :
      Set

    ObservableSurface :
      Set

    ManifoldChart :
      Set

    Invariant :
      Set

    quotient :
      LatentExperience →
      ObservableSurface

    chart :
      ObservableSurface →
      ManifoldChart

    invariant :
      ManifoldChart →
      Invariant

    quotientReading :
      String

    quotientBoundary :
      String

open ObserverQuotient public

record ObserverContext (Q : ObserverQuotient) : Set₁ where
  field
    Vocabulary :
      Set

    Ontology :
      Set

    ContextFrame :
      Set

    EmotionalState :
      Set

    Scope :
      Set

    IntentProjection :
      Set

    vocabulary :
      Vocabulary

    ontology :
      Ontology

    contextFrame :
      ContextFrame

    emotionalState :
      EmotionalState

    scope :
      Scope

    intentProjection :
      IntentProjection

    contextReceipt :
      Set

    contextReading :
      String

open ObserverContext public

------------------------------------------------------------------------
-- Metaphor / simile correctness as partial operator-equivalence alignment.

record PartialOperatorEquivalenceAlignment
    (source target : ObserverQuotient) : Set₁ where
  field
    SourceSlice :
      Set

    TargetSlice :
      Set

    SharedInvariant :
      Set

    sourceOperator :
      SourceSlice →
      SourceSlice

    targetOperator :
      TargetSlice →
      TargetSlice

    sourceInvariant :
      SourceSlice →
      SharedInvariant

    targetInvariant :
      TargetSlice →
      SharedInvariant

    aligned :
      SourceSlice →
      TargetSlice →
      Set

    operatorEquivalenceOnAlignedSlice :
      (sourcePoint : SourceSlice) →
      (targetPoint : TargetSlice) →
      aligned sourcePoint targetPoint →
      sourceInvariant (sourceOperator sourcePoint) ≡
      targetInvariant (targetOperator targetPoint)

    declaredScope :
      String

    alignmentStatus :
      AlignmentStatus

    alignmentReceipt :
      Set

    alignmentReading :
      String

open PartialOperatorEquivalenceAlignment public

record AnalogyCorrectness
    (source target : ObserverQuotient) : Set₁ where
  field
    analogyForm :
      AnalogyForm

    alignment :
      PartialOperatorEquivalenceAlignment source target

    intendedInvariantPreserved :
      alignmentReceipt alignment

    correctnessBoundary :
      String

open AnalogyCorrectness public

analogy-preserves-operator-invariant :
  {source target : ObserverQuotient} →
  (A : AnalogyCorrectness source target) →
  (sourcePoint :
    PartialOperatorEquivalenceAlignment.SourceSlice
      (AnalogyCorrectness.alignment A)) →
  (targetPoint :
    PartialOperatorEquivalenceAlignment.TargetSlice
      (AnalogyCorrectness.alignment A)) →
  PartialOperatorEquivalenceAlignment.aligned
    (AnalogyCorrectness.alignment A)
    sourcePoint
    targetPoint →
  PartialOperatorEquivalenceAlignment.sourceInvariant
    (AnalogyCorrectness.alignment A)
    (PartialOperatorEquivalenceAlignment.sourceOperator
      (AnalogyCorrectness.alignment A)
      sourcePoint)
    ≡
  PartialOperatorEquivalenceAlignment.targetInvariant
    (AnalogyCorrectness.alignment A)
    (PartialOperatorEquivalenceAlignment.targetOperator
      (AnalogyCorrectness.alignment A)
      targetPoint)
analogy-preserves-operator-invariant A sourcePoint targetPoint aligned-v =
  PartialOperatorEquivalenceAlignment.operatorEquivalenceOnAlignedSlice
    (AnalogyCorrectness.alignment A)
    sourcePoint
    targetPoint
    aligned-v

------------------------------------------------------------------------
-- Communicative succinctness as MDL-style invariant preservation.

record MDLStyleSuccinctCommunication
    (audience : ObserverQuotient)
    (context : ObserverContext audience) : Set₁ where
  field
    Message :
      Set

    IntendedInvariant :
      Set

    DecodedMeaning :
      Set

    messageCost :
      Message →
      Nat

    baselineCost :
      Nat

    decodeUnderContext :
      Message →
      ObserverContext.ContextFrame context →
      DecodedMeaning

    intendedInvariants :
      List IntendedInvariant

    preservesIntendedInvariant :
      Message →
      IntendedInvariant →
      Set

    succinctRelativeToBaseline :
      Message →
      Set

    costWithinBaseline :
      Message →
      Set

    costBoundReceipt :
      (message : Message) →
      succinctRelativeToBaseline message →
      costWithinBaseline message

    preservationReceipt :
      (message : Message) →
      (invariant : IntendedInvariant) →
      preservesIntendedInvariant message invariant

    audienceContextReceipt :
      ObserverContext.contextReceipt context

    succinctnessReading :
      String

open MDLStyleSuccinctCommunication public

succinct-message-preserves-invariant :
  {audience : ObserverQuotient} →
  {context : ObserverContext audience} →
  (C : MDLStyleSuccinctCommunication audience context) →
  (message : MDLStyleSuccinctCommunication.Message C) →
  (invariant : MDLStyleSuccinctCommunication.IntendedInvariant C) →
  MDLStyleSuccinctCommunication.preservesIntendedInvariant
    C
    message
    invariant
succinct-message-preserves-invariant C message invariant =
  MDLStyleSuccinctCommunication.preservationReceipt C message invariant

------------------------------------------------------------------------
-- Misunderstanding as failed manifold / invariant alignment.

record InterpersonalAlignmentAttempt : Set₁ where
  field
    speakerQuotient :
      ObserverQuotient

    listenerQuotient :
      ObserverQuotient

    speakerContext :
      ObserverContext speakerQuotient

    listenerContext :
      ObserverContext listenerQuotient

    ManifoldAlignment :
      Set

    InvariantAlignment :
      Set

    Message :
      Set

    speakerIntendedInvariant :
      Message →
      ObserverQuotient.Invariant speakerQuotient

    listenerRecoveredInvariant :
      Message →
      ObserverQuotient.Invariant listenerQuotient

    manifoldAlignmentReceipt :
      ManifoldAlignment →
      Set

    invariantAlignmentReceipt :
      InvariantAlignment →
      Set

    failureModes :
      List MisunderstandingFailureMode

    misunderstandingStatus :
      AlignmentStatus

    misunderstandingReading :
      String

open InterpersonalAlignmentAttempt public

record MisunderstandingWitness
    (attempt : InterpersonalAlignmentAttempt) : Set₁ where
  field
    message :
      InterpersonalAlignmentAttempt.Message attempt

    failedManifoldAlignment :
      Set

    failedInvariantAlignment :
      Set

    activeFailureModes :
      List MisunderstandingFailureMode

    residualReceipt :
      Set

    witnessReading :
      String

open MisunderstandingWitness public

record CommunicationClaimBoundary : Set₁ where
  field
    guards :
      List CommunicationNonClaimGuard

    failureCatalogue :
      List MisunderstandingFailureMode

    allGuardsDeclared :
      guards ≡ canonicalCommunicationNonClaimGuards

    allFailureModesDeclared :
      failureCatalogue ≡ canonicalMisunderstandingFailureModes

    perfectUnderstandingClaim :
      Bool

    perfectUnderstandingClaimIsFalse :
      perfectUnderstandingClaim ≡ false

    qualiaRecoveryClaim :
      Bool

    qualiaRecoveryClaimIsFalse :
      qualiaRecoveryClaim ≡ false

    universalExactTranslationClaim :
      Bool

    universalExactTranslationClaimIsFalse :
      universalExactTranslationClaim ≡ false

    contextFreeCommunicationOptimalityClaim :
      Bool

    contextFreeCommunicationOptimalityClaimIsFalse :
      contextFreeCommunicationOptimalityClaim ≡ false

    boundaryReading :
      String

open CommunicationClaimBoundary public

canonicalCommunicationClaimBoundary :
  String →
  CommunicationClaimBoundary
canonicalCommunicationClaimBoundary reading =
  record
    { guards =
        canonicalCommunicationNonClaimGuards
    ; failureCatalogue =
        canonicalMisunderstandingFailureModes
    ; allGuardsDeclared =
        refl
    ; allFailureModesDeclared =
        refl
    ; perfectUnderstandingClaim =
        false
    ; perfectUnderstandingClaimIsFalse =
        refl
    ; qualiaRecoveryClaim =
        false
    ; qualiaRecoveryClaimIsFalse =
        refl
    ; universalExactTranslationClaim =
        false
    ; universalExactTranslationClaimIsFalse =
        refl
    ; contextFreeCommunicationOptimalityClaim =
        false
    ; contextFreeCommunicationOptimalityClaimIsFalse =
        refl
    ; boundaryReading =
        reading
    }

trivialCommunicationBoundaryReceipt : ⊤
trivialCommunicationBoundaryReceipt = tt

------------------------------------------------------------------------
-- Canonical toy inhabitants for aggregate discharge.

data ToyCommunicationAtom : Set where
  toySpeakerState :
    ToyCommunicationAtom

  toyObservableMessage :
    ToyCommunicationAtom

  toyManifoldChart :
    ToyCommunicationAtom

  toyInvariant :
    ToyCommunicationAtom

toyObserverQuotient :
  ObserverQuotient
toyObserverQuotient =
  record
    { LatentExperience =
        ToyCommunicationAtom
    ; ObservableSurface =
        ToyCommunicationAtom
    ; ManifoldChart =
        ToyCommunicationAtom
    ; Invariant =
        ToyCommunicationAtom
    ; quotient =
        λ _ → toyObservableMessage
    ; chart =
        λ _ → toyManifoldChart
    ; invariant =
        λ _ → toyInvariant
    ; quotientReading =
        "toy observer quotient for semantic alignment"
    ; quotientBoundary =
        "many-to-one observer quotient; no latent-state recovery"
    }

toyObserverContext :
  ObserverContext toyObserverQuotient
toyObserverContext =
  record
    { Vocabulary =
        ToyCommunicationAtom
    ; Ontology =
        ToyCommunicationAtom
    ; ContextFrame =
        ToyCommunicationAtom
    ; EmotionalState =
        ToyCommunicationAtom
    ; Scope =
        ToyCommunicationAtom
    ; IntentProjection =
        ToyCommunicationAtom
    ; vocabulary =
        toyObservableMessage
    ; ontology =
        toyManifoldChart
    ; contextFrame =
        toyManifoldChart
    ; emotionalState =
        toySpeakerState
    ; scope =
        toyObservableMessage
    ; intentProjection =
        toyInvariant
    ; contextReceipt =
        ⊤
    ; contextReading =
        "toy audience/context receipt for succinct communication"
    }

toySuccinctCommunication :
  MDLStyleSuccinctCommunication toyObserverQuotient toyObserverContext
toySuccinctCommunication =
  record
    { Message =
        ToyCommunicationAtom
    ; IntendedInvariant =
        ToyCommunicationAtom
    ; DecodedMeaning =
        ToyCommunicationAtom
    ; messageCost =
        λ _ → zero
    ; baselineCost =
        zero
    ; decodeUnderContext =
        λ message _ → message
    ; intendedInvariants =
        toyInvariant
        ∷ []
    ; preservesIntendedInvariant =
        λ _ _ → ⊤
    ; succinctRelativeToBaseline =
        λ _ → ⊤
    ; costWithinBaseline =
        λ _ → ⊤
    ; costBoundReceipt =
        λ _ _ → tt
    ; preservationReceipt =
        λ _ _ → tt
    ; audienceContextReceipt =
        tt
    ; succinctnessReading =
        "toy succinctness witness: message cost and invariant preservation are context-receipted"
    }
