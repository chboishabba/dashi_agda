{-# OPTIONS --safe #-}
module DASHI.Interop.VerifiedFractranCrankPipeline where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (_≤_; _<_)

------------------------------------------------------------------------
-- 1. Source and target transition semantics
------------------------------------------------------------------------

record TransitionSystem : Set₁ where
  field
    State       : Set
    Observation : Set
    initial     : State → Set
    step        : State → State → Set
    observe     : State → Observation

open TransitionSystem public

record CompilerSimulation
  (source target : TransitionSystem) : Set₁ where
  field
    encode : State source → State target
    decode : State target → Maybe (State source)

    initialization-correct :
      ∀ s → decode (encode s) ≡ just s

    forward-simulation :
      ∀ {s s'} →
      step source s s' →
      Σ (State target)
        (λ t →
          step target (encode s) t ×
          decode t ≡ just s')

    boundaryState : State target → Set

    backward-simulation :
      ∀ {s t} →
      boundaryState t →
      step target (encode s) t →
      Σ (State source)
        (λ s' →
          step source s s' ×
          decode t ≡ just s')

open CompilerSimulation public

------------------------------------------------------------------------
-- 2. FRACTRAN as guarded exponent-vector transport
------------------------------------------------------------------------

record FractionVector (Lane : Set) : Set₁ where
  field
    numerator   : Lane → Nat
    denominator : Lane → Nat

open FractionVector public

record FractranMachine : Set₁ where
  field
    Lane        : Set
    State       : Set
    Program     : Set

    exponent    : State → Lane → Nat
    instruction : Program → Nat → Maybe (FractionVector Lane)

    enabled : FractionVector Lane → State → Set
    apply   : FractionVector Lane → State → State

    firstEnabled : Program → State → Maybe (FractionVector Lane)

    deterministic-first-enabled :
      ∀ P s f g →
      firstEnabled P s ≡ just f →
      firstEnabled P s ≡ just g →
      f ≡ g

    guarded-update :
      ∀ f s →
      enabled f s →
      ∀ lane →
      exponent (apply f s) lane + denominator f lane
        ≡ exponent s lane + numerator f lane

open FractranMachine public

------------------------------------------------------------------------
-- 3. Micro-operation normalization
------------------------------------------------------------------------

data MicroOp : Set where
  load store add sub mul compare branch allocate emit halt : MicroOp

record ArchitectureLowering : Set₁ where
  field
    Instruction : Set
    lower       : Instruction → List MicroOp

open ArchitectureLowering public

record MicroOpToFractran (F : FractranMachine) : Set₁ where
  field
    compileMicroOps : List MicroOp → Program F
    microSemantics  : TransitionSystem
    fractranSemantics : Program F → TransitionSystem

    compilerCorrect :
      ∀ ops →
      CompilerSimulation
        microSemantics
        (fractranSemantics (compileMicroOps ops))

open MicroOpToFractran public

------------------------------------------------------------------------
-- 4. Candidate cranks: proposals are not authority
------------------------------------------------------------------------

record CostVector : Set where
  field
    cycles instructions memory cacheMisses branchMisses proofBytes : Nat

open CostVector public

record MDLVector : Set where
  field
    modelBits residualBits proofBits decoderBits : Nat

  total : Nat
  total = modelBits + residualBits + proofBits + decoderBits

open MDLVector public

record ArtifactIdentity : Set where
  field
    cid payloadHash toolchainCid traceCid proofCid : String

open ArtifactIdentity public

record CrankCandidate : Set₁ where
  field
    SourceProgram TargetProgram Input Output : Set

    sourceRun : SourceProgram → Input → Maybe Output
    targetRun : TargetProgram → Input → Maybe Output

    source : SourceProgram
    target : TargetProgram

    Domain : Input → Set

    observationallyEquivalent :
      ∀ x → Domain x → sourceRun source x ≡ targetRun target x

    compilerWitnessPresent : Bool
    proofCheckerAccepted    : Bool
    receiptReplayAccepted   : Bool

    physicalCost : CostVector
    descriptionCost : MDLVector
    identity : ArtifactIdentity

open CrankCandidate public

record VerifiedCrank (candidate : CrankCandidate) : Set where
  field
    compilerWitnessPresentIsTrue :
      compilerWitnessPresent candidate ≡ true

    proofCheckerAcceptedIsTrue :
      proofCheckerAccepted candidate ≡ true

    receiptReplayAcceptedIsTrue :
      receiptReplayAccepted candidate ≡ true

open VerifiedCrank public

------------------------------------------------------------------------
-- 5. Evolutionary discovery remains outside the trusted kernel
------------------------------------------------------------------------

record CrankProposalEngine : Set₁ where
  field
    Candidate : Set
    Population : Set

    seedPopulation : Population
    mutate         : Candidate → Candidate
    recombine      : Candidate → Candidate → Candidate
    anneal         : Nat → Candidate → Candidate → Candidate
    llmSuggest     : String → List Candidate
    evolve         : Nat → Population → Population

open CrankProposalEngine public

record ProposalAuthorityBoundary : Set where
  field
    proposalsMayComeFromGA            : Bool
    proposalsMayComeFromArtificialLife : Bool
    proposalsMayComeFromAnnealing     : Bool
    proposalsMayComeFromLLM           : Bool

    proposalsEstablishCorrectness : Bool
    proposalsEstablishCorrectnessIsFalse :
      proposalsEstablishCorrectness ≡ false

canonicalProposalAuthorityBoundary : ProposalAuthorityBoundary
canonicalProposalAuthorityBoundary =
  record
    { proposalsMayComeFromGA = true
    ; proposalsMayComeFromArtificialLife = true
    ; proposalsMayComeFromAnnealing = true
    ; proposalsMayComeFromLLM = true
    ; proposalsEstablishCorrectness = false
    ; proposalsEstablishCorrectnessIsFalse = refl
    }

------------------------------------------------------------------------
-- 6. Corpus-relative post-entropy scoring
------------------------------------------------------------------------

record PostEntropyScore : Set where
  field
    corpusBefore corpusAfter : MDLVector
    deltaModel deltaResidual deltaProof : Nat

    additiveAccounting :
      total corpusAfter + total corpusBefore
        ≡ total corpusBefore + total corpusAfter

open PostEntropyScore public

record CandidateOrdering (Candidate : Set) : Set₁ where
  field
    verified : Candidate → Set
    strongerScope : Candidate → Candidate → Set
    lowerMDL : Candidate → Candidate → Set
    lowerPhysicalCost : Candidate → Candidate → Set
    preferred : Candidate → Candidate → Set

    verified-first :
      ∀ {x y} → verified x → preferred x y

    scope-before-compression :
      ∀ {x y} →
      verified x → verified y → strongerScope x y → preferred x y

    compression-before-runtime :
      ∀ {x y} →
      verified x → verified y → lowerMDL x y → preferred x y

    runtime-tiebreak :
      ∀ {x y} →
      verified x → verified y → lowerPhysicalCost x y → preferred x y

open CandidateOrdering public

------------------------------------------------------------------------
-- 7. Bounded optimality, never metaphysical cycle necessity
------------------------------------------------------------------------

record BoundedSearchCertificate : Set₁ where
  field
    Candidate : Set
    SearchMember : Candidate → Set
    Equivalent   : Candidate → Candidate → Set
    Cheaper      : Candidate → Candidate → Set

    selected : Candidate
    selectedInSearch : SearchMember selected

    noCheaperEquivalentInsideSearch :
      ∀ candidate →
      SearchMember candidate →
      Equivalent candidate selected →
      Cheaper candidate selected →
      ⊥

open BoundedSearchCertificate public

------------------------------------------------------------------------
-- 8. Zero-knowledge receipt boundary
------------------------------------------------------------------------

record ZKCrankStatement : Set where
  field
    sourceCid candidateCid traceHash specificationId : String
    publicCostBound : CostVector

open ZKCrankStatement public

record ZKCrankWitness : Set₁ where
  field
    Candidate : CrankCandidate
    verification : VerifiedCrank Candidate

open ZKCrankWitness public

record ZKCrankRelation : Set₁ where
  field
    proves : ZKCrankStatement → ZKCrankWitness → Set

    bindsSourceArtifact :
      ∀ statement witness →
      proves statement witness →
      sourceCid statement ≡ cid (identity (Candidate witness))

    bindsCandidateArtifact :
      ∀ statement witness →
      proves statement witness →
      candidateCid statement ≡ cid (identity (Candidate witness))

open ZKCrankRelation public

------------------------------------------------------------------------
-- 9. Complete fused contract
------------------------------------------------------------------------

record VerifiedFractranCrankPipeline : Set₂ where
  field
    Source Target : TransitionSystem
    compiler : CompilerSimulation Source Target

    crank : CrankCandidate
    crankVerified : VerifiedCrank crank

    postEntropy : PostEntropyScore
    artifact : ArtifactIdentity

    boundedOptimality : BoundedSearchCertificate
    zkRelation : ZKCrankRelation

open VerifiedFractranCrankPipeline public

------------------------------------------------------------------------
-- 10. Honest promotion boundary
------------------------------------------------------------------------

record VerifiedFractranCrankBoundary : Set where
  field
    arbitraryBinaryTranslatorImplementedHere : Bool
    arbitraryBinaryTranslatorImplementedHereIsFalse :
      arbitraryBinaryTranslatorImplementedHere ≡ false

    globalProgramMinimalityProved : Bool
    globalProgramMinimalityProvedIsFalse :
      globalProgramMinimalityProved ≡ false

    literalCycleNecessityProved : Bool
    literalCycleNecessityProvedIsFalse :
      literalCycleNecessityProved ≡ false

    boundedSearchMinimalitySupported : Bool
    boundedSearchMinimalitySupportedIsTrue :
      boundedSearchMinimalitySupported ≡ true

    llmIsProposalOnly : Bool
    llmIsProposalOnlyIsTrue :
      llmIsProposalOnly ≡ true

    notes : List String

open VerifiedFractranCrankBoundary public

canonicalVerifiedFractranCrankBoundary : VerifiedFractranCrankBoundary
canonicalVerifiedFractranCrankBoundary =
  record
    { arbitraryBinaryTranslatorImplementedHere = false
    ; arbitraryBinaryTranslatorImplementedHereIsFalse = refl
    ; globalProgramMinimalityProved = false
    ; globalProgramMinimalityProvedIsFalse = refl
    ; literalCycleNecessityProved = false
    ; literalCycleNecessityProvedIsFalse = refl
    ; boundedSearchMinimalitySupported = true
    ; boundedSearchMinimalitySupportedIsTrue = refl
    ; llmIsProposalOnly = true
    ; llmIsProposalOnlyIsTrue = refl
    ; notes =
        "Machine code to FRACTRAN must be a deterministic semantics-preserving compiler lane"
        ∷ "Genetic algorithms, artificial life, annealing, and LLMs may propose candidates but do not establish correctness"
        ∷ "DASHI post-entropy scores verified candidates relative to the current corpus"
        ∷ "CID/MASL/ZKP layers bind identity, provenance, replay, and bounded cost claims"
        ∷ "Only bounded no-cheaper-equivalent claims are supported; global metaphysical cycle necessity is not promoted"
        ∷ []
    }
