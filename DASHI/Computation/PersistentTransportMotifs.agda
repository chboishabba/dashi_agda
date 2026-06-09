module DASHI.Computation.PersistentTransportMotifs where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Programs and machines as persistent constrained transport motifs.
--
-- This is a bounded computation-lane surface.  It records the thread claim
-- that many source-level artifacts collapse, at execution/component level,
-- into a small basis of persistent constrained transport motifs.
--
-- It does not prove compiler optimality, semantic equivalence, or hardware
-- closure.

data ProgramArtifactClass : Set where
  sourceProgramArtifact : ProgramArtifactClass
  rendererArtifact : ProgramArtifactClass
  databaseArtifact : ProgramArtifactClass
  codecArtifact : ProgramArtifactClass
  physicsEngineArtifact : ProgramArtifactClass
  compilerArtifact : ProgramArtifactClass
  networkStackArtifact : ProgramArtifactClass
  spreadsheetArtifact : ProgramArtifactClass

data ExecutionLayer : Set where
  sourceLevelLayer : ExecutionLayer
  componentLevelLayer : ExecutionLayer
  instructionLevelLayer : ExecutionLayer
  persistentFabricLayer : ExecutionLayer
  committedArtifactLayer : ExecutionLayer

data TransportMotif : Set where
  loadFetchMotif : TransportMotif
  transportMotif : TransportMotif
  mixTransformMotif : TransportMotif
  compareMotif : TransportMotif
  maskGateMotif : TransportMotif
  branchMotif : TransportMotif
  shuffleMotif : TransportMotif
  accumulateReduceMotif : TransportMotif
  storeCommitMotif : TransportMotif
  synchronizeMotif : TransportMotif
  dispatchMotif : TransportMotif

canonicalTransportMotifBasis : List TransportMotif
canonicalTransportMotifBasis =
  loadFetchMotif
  ∷ transportMotif
  ∷ mixTransformMotif
  ∷ compareMotif
  ∷ maskGateMotif
  ∷ branchMotif
  ∷ shuffleMotif
  ∷ accumulateReduceMotif
  ∷ storeCommitMotif
  ∷ synchronizeMotif
  ∷ dispatchMotif
  ∷ []

data MotifNonPromotionGuard : Set where
  noOptimalCompilerClaim : MotifNonPromotionGuard
  noSemanticEquivalenceProofClaim : MotifNonPromotionGuard
  noHardwareClosureClaim : MotifNonPromotionGuard
  noWholeProgramRecoveryClaim : MotifNonPromotionGuard
  noPerformanceUniversalityClaim : MotifNonPromotionGuard
  noSourceIdentityFromTraceClaim : MotifNonPromotionGuard

canonicalMotifNonPromotionGuards : List MotifNonPromotionGuard
canonicalMotifNonPromotionGuards =
  noOptimalCompilerClaim
  ∷ noSemanticEquivalenceProofClaim
  ∷ noHardwareClosureClaim
  ∷ noWholeProgramRecoveryClaim
  ∷ noPerformanceUniversalityClaim
  ∷ noSourceIdentityFromTraceClaim
  ∷ []

------------------------------------------------------------------------
-- Persistent typed fibre fabric.

record PersistentTypedFibreFabric : Set₁ where
  field
    SourceArtifact : Set
    Component : Set
    RuntimeState : Set
    TypedFibre : Set
    LocalCarrier : Set
    Constraint : Set
    Receipt : Set
    CommittedArtifact : Set

    artifactClass :
      SourceArtifact →
      ProgramArtifactClass

    componentOf :
      SourceArtifact →
      List Component

    fibreOf :
      RuntimeState →
      TypedFibre

    carrierAt :
      RuntimeState →
      LocalCarrier

    constraintAt :
      TypedFibre →
      Constraint

    receiptFor :
      SourceArtifact →
      Component →
      Receipt

    commit :
      RuntimeState →
      Receipt →
      CommittedArtifact

    fabricReading :
      String

open PersistentTypedFibreFabric public

record MotifRewrite
    (fabric : PersistentTypedFibreFabric) : Set₁ where
  field
    inputState :
      RuntimeState fabric

    outputState :
      RuntimeState fabric

    motif :
      TransportMotif

    localRewrite :
      LocalCarrier fabric →
      Constraint fabric →
      LocalCarrier fabric

    inputFibre :
      TypedFibre fabric

    outputFibre :
      TypedFibre fabric

    fibreInputMatches :
      inputFibre ≡ fibreOf fabric inputState

    fibreOutputMatches :
      outputFibre ≡ fibreOf fabric outputState

    admissibleRewrite :
      Set

    rewriteReading :
      String

open MotifRewrite public

record CPUInstructionAsLocalTransportRewrite
    (fabric : PersistentTypedFibreFabric) : Set₁ where
  field
    Instruction : Set
    MicroOperand : Set
    MicroResult : Set

    decodeInstruction :
      Instruction →
      TransportMotif

    operandCarrier :
      Instruction →
      MicroOperand →
      LocalCarrier fabric

    executeInstruction :
      Instruction →
      MicroOperand →
      MicroResult

    resultCarrier :
      Instruction →
      MicroResult →
      LocalCarrier fabric

    instructionRewrite :
      Instruction →
      MotifRewrite fabric

    localOnly :
      Bool

    localOnlyIsTrue :
      localOnly ≡ true

    cpuReading :
      String

open CPUInstructionAsLocalTransportRewrite public

record ComponentCollapse
    (fabric : PersistentTypedFibreFabric) : Set₁ where
  field
    sourceArtifact :
      SourceArtifact fabric

    components :
      List (Component fabric)

    componentProjectionMatches :
      components ≡ componentOf fabric sourceArtifact

    componentMotifs :
      Component fabric →
      List TransportMotif

    motifsAreFromBasis :
      Component fabric →
      Set

    collapseLayer :
      ExecutionLayer

    collapseReading :
      String

open ComponentCollapse public

record PersistentTransportMotifSurface : Set₁ where
  field
    fabric :
      PersistentTypedFibreFabric

    cpuInstructionSurface :
      CPUInstructionAsLocalTransportRewrite fabric

    motifBasis :
      List TransportMotif

    motifBasisIsCanonical :
      motifBasis ≡ canonicalTransportMotifBasis

    sourceProgramCollapse :
      ComponentCollapse fabric

    rendererCollapse :
      ComponentCollapse fabric

    databaseCollapse :
      ComponentCollapse fabric

    codecCollapse :
      ComponentCollapse fabric

    physicsEngineCollapse :
      ComponentCollapse fabric

    compilerCollapse :
      ComponentCollapse fabric

    networkStackCollapse :
      ComponentCollapse fabric

    spreadsheetCollapse :
      ComponentCollapse fabric

    persistentFabricConstraint :
      String

    surfaceReading :
      String

open PersistentTransportMotifSurface public

record MotifNonPromotionCertificate
    (surface : PersistentTransportMotifSurface) : Set where
  field
    guards :
      List MotifNonPromotionGuard

    guardsAreCanonical :
      guards ≡ canonicalMotifNonPromotionGuards

    optimalCompilerClaim :
      Bool

    optimalCompilerClaimIsFalse :
      optimalCompilerClaim ≡ false

    semanticEquivalenceProofClaim :
      Bool

    semanticEquivalenceProofClaimIsFalse :
      semanticEquivalenceProofClaim ≡ false

    hardwareClosureClaim :
      Bool

    hardwareClosureClaimIsFalse :
      hardwareClosureClaim ≡ false

    wholeProgramRecoveryClaim :
      Bool

    wholeProgramRecoveryClaimIsFalse :
      wholeProgramRecoveryClaim ≡ false

    certificateReading :
      String

open MotifNonPromotionCertificate public

------------------------------------------------------------------------
-- Canonical toy inhabitants.

data ToyArtifact : Set where
  toySourceProgram : ToyArtifact
  toyRenderer : ToyArtifact
  toyDatabase : ToyArtifact
  toyCodec : ToyArtifact
  toyPhysicsEngine : ToyArtifact
  toyCompiler : ToyArtifact
  toyNetworkStack : ToyArtifact
  toySpreadsheet : ToyArtifact

toyArtifactClass : ToyArtifact → ProgramArtifactClass
toyArtifactClass toySourceProgram = sourceProgramArtifact
toyArtifactClass toyRenderer = rendererArtifact
toyArtifactClass toyDatabase = databaseArtifact
toyArtifactClass toyCodec = codecArtifact
toyArtifactClass toyPhysicsEngine = physicsEngineArtifact
toyArtifactClass toyCompiler = compilerArtifact
toyArtifactClass toyNetworkStack = networkStackArtifact
toyArtifactClass toySpreadsheet = spreadsheetArtifact

canonicalPersistentTypedFibreFabric :
  PersistentTypedFibreFabric
canonicalPersistentTypedFibreFabric =
  record
    { SourceArtifact = ToyArtifact
    ; Component = ⊤
    ; RuntimeState = ⊤
    ; TypedFibre = ⊤
    ; LocalCarrier = ⊤
    ; Constraint = ⊤
    ; Receipt = ⊤
    ; CommittedArtifact = ⊤
    ; artifactClass = toyArtifactClass
    ; componentOf = λ _ → tt ∷ []
    ; fibreOf = λ _ → tt
    ; carrierAt = λ _ → tt
    ; constraintAt = λ _ → tt
    ; receiptFor = λ _ _ → tt
    ; commit = λ _ _ → tt
    ; fabricReading =
        "Toy persistent typed fibre fabric: components execute as local constrained transports over stable fibres."
    }

canonicalMotifRewrite :
  TransportMotif →
  MotifRewrite canonicalPersistentTypedFibreFabric
canonicalMotifRewrite motif =
  record
    { inputState = tt
    ; outputState = tt
    ; motif = motif
    ; localRewrite = λ _ _ → tt
    ; inputFibre = tt
    ; outputFibre = tt
    ; fibreInputMatches = refl
    ; fibreOutputMatches = refl
    ; admissibleRewrite = ⊤
    ; rewriteReading =
        "Toy local rewrite for one persistent transport motif."
    }

canonicalCPUInstructionAsLocalTransportRewrite :
  CPUInstructionAsLocalTransportRewrite canonicalPersistentTypedFibreFabric
canonicalCPUInstructionAsLocalTransportRewrite =
  record
    { Instruction = TransportMotif
    ; MicroOperand = ⊤
    ; MicroResult = ⊤
    ; decodeInstruction = λ motif → motif
    ; operandCarrier = λ _ _ → tt
    ; executeInstruction = λ _ _ → tt
    ; resultCarrier = λ _ _ → tt
    ; instructionRewrite = canonicalMotifRewrite
    ; localOnly = true
    ; localOnlyIsTrue = refl
    ; cpuReading =
        "A CPU instruction is represented only as one local transport rewrite inside the fabric."
    }

canonicalComponentMotifs : ⊤ → List TransportMotif
canonicalComponentMotifs _ =
  loadFetchMotif
  ∷ transportMotif
  ∷ mixTransformMotif
  ∷ compareMotif
  ∷ maskGateMotif
  ∷ branchMotif
  ∷ shuffleMotif
  ∷ accumulateReduceMotif
  ∷ storeCommitMotif
  ∷ synchronizeMotif
  ∷ dispatchMotif
  ∷ []

canonicalComponentCollapse :
  ToyArtifact →
  ComponentCollapse canonicalPersistentTypedFibreFabric
canonicalComponentCollapse artifact =
  record
    { sourceArtifact = artifact
    ; components = tt ∷ []
    ; componentProjectionMatches = refl
    ; componentMotifs = canonicalComponentMotifs
    ; motifsAreFromBasis = λ _ → ⊤
    ; collapseLayer = componentLevelLayer
    ; collapseReading =
        "At component/execution level this artifact is represented by the canonical transport motif basis."
    }

canonicalPersistentTransportMotifSurface :
  PersistentTransportMotifSurface
canonicalPersistentTransportMotifSurface =
  record
    { fabric =
        canonicalPersistentTypedFibreFabric
    ; cpuInstructionSurface =
        canonicalCPUInstructionAsLocalTransportRewrite
    ; motifBasis =
        canonicalTransportMotifBasis
    ; motifBasisIsCanonical =
        refl
    ; sourceProgramCollapse =
        canonicalComponentCollapse toySourceProgram
    ; rendererCollapse =
        canonicalComponentCollapse toyRenderer
    ; databaseCollapse =
        canonicalComponentCollapse toyDatabase
    ; codecCollapse =
        canonicalComponentCollapse toyCodec
    ; physicsEngineCollapse =
        canonicalComponentCollapse toyPhysicsEngine
    ; compilerCollapse =
        canonicalComponentCollapse toyCompiler
    ; networkStackCollapse =
        canonicalComponentCollapse toyNetworkStack
    ; spreadsheetCollapse =
        canonicalComponentCollapse toySpreadsheet
    ; persistentFabricConstraint =
        "Execution preserves typed fibres, local constraints, receipts, and commit boundaries."
    ; surfaceReading =
        "Programs and machines are modeled as persistent constrained transport motifs over a typed fibre fabric."
    }

canonicalMotifNonPromotionCertificate :
  MotifNonPromotionCertificate canonicalPersistentTransportMotifSurface
canonicalMotifNonPromotionCertificate =
  record
    { guards =
        canonicalMotifNonPromotionGuards
    ; guardsAreCanonical =
        refl
    ; optimalCompilerClaim =
        false
    ; optimalCompilerClaimIsFalse =
        refl
    ; semanticEquivalenceProofClaim =
        false
    ; semanticEquivalenceProofClaimIsFalse =
        refl
    ; hardwareClosureClaim =
        false
    ; hardwareClosureClaimIsFalse =
        refl
    ; wholeProgramRecoveryClaim =
        false
    ; wholeProgramRecoveryClaimIsFalse =
        refl
    ; certificateReading =
        "The motif surface is non-promoting: no optimal compiler, semantic equivalence proof, hardware closure, or whole-program recovery follows."
    }
