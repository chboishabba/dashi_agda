module DASHI.Core.HistoricalMechanismCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- HISTORICAL MECHANISM COMPILER
--
-- A historical mechanism is not produced from a narrative, source list,
-- chronology or causal hypothesis alone.  Closure requires four independent,
-- proof-relevant receipts:
--
--   1. source-totality / no-orphan receipt
--   2. reviewed event/claim join receipt
--   3. dual-chronology receipt
--   4. causal/mechanism receipt
--
-- Every missing premise remains an explicit abstention residual.
------------------------------------------------------------------------

record SourceTotalReceipt : Set where
  constructor source-total-receipt
  field
    packetRef : String
    allConsumedClaimsDisposed : Bool
    allConsumedClaimsDisposedIsTrue :
      allConsumedClaimsDisposed ≡ true
    orphanClaimsAdmitted : Bool
    orphanClaimsAdmittedIsFalse :
      orphanClaimsAdmitted ≡ false

open SourceTotalReceipt public

record ReviewedJoinReceipt : Set where
  constructor reviewed-join-receipt
  field
    joinRef : String
    leftClaimRef : String
    rightClaimRef : String
    joinBasisRef : String
    reviewed : Bool
    reviewedIsTrue : reviewed ≡ true
    mergesNarratives : Bool
    mergesNarrativesIsFalse : mergesNarratives ≡ false

open ReviewedJoinReceipt public

record DualChronologyReceipt : Set where
  constructor dual-chronology-receipt
  field
    chronologyRef : String
    eventTimeRef : String
    knowledgeTimeRef : String
    eventAndKnowledgeTimeCollapsed : Bool
    eventAndKnowledgeTimeCollapsedIsFalse :
      eventAndKnowledgeTimeCollapsed ≡ false

open DualChronologyReceipt public

record CausalMechanismReceipt : Set where
  constructor causal-mechanism-receipt
  field
    mechanismRef : String
    causeClaimRef : String
    effectClaimRef : String
    counterHypothesisRef : String
    provenanceRef : String
    reviewed : Bool
    reviewedIsTrue : reviewed ≡ true
    sourceAdjacencyUsedAsCausation : Bool
    sourceAdjacencyUsedAsCausationIsFalse :
      sourceAdjacencyUsedAsCausation ≡ false

open CausalMechanismReceipt public

record HistoricalMechanismWitness : Set where
  constructor historical-mechanism-witness
  field
    witnessRef : String
    sourceTotal : SourceTotalReceipt
    reviewedJoin : ReviewedJoinReceipt
    chronology : DualChronologyReceipt
    causalMechanism : CausalMechanismReceipt
    createsPoliticalVerdict : Bool
    createsPoliticalVerdictIsFalse :
      createsPoliticalVerdict ≡ false
    createsUniversalRanking : Bool
    createsUniversalRankingIsFalse :
      createsUniversalRanking ≡ false

open HistoricalMechanismWitness public

data MechanismResidualKind : Set where
  sourceTotalityResidual : MechanismResidualKind
  reviewedJoinResidual : MechanismResidualKind
  chronologyResidual : MechanismResidualKind
  causalMechanismResidual : MechanismResidualKind

record MechanismResidual : Set where
  constructor mechanism-residual
  field
    kind : MechanismResidualKind
    residualRef : String
    requiredEvidence : String
    acquisitionHint : String
    mayPromoteTruth : Bool
    mayPromoteTruthIsFalse :
      mayPromoteTruth ≡ false

open MechanismResidual public

data MechanismCompilation : Set where
  closed :
    HistoricalMechanismWitness →
    MechanismCompilation
  abstain :
    List MechanismResidual →
    MechanismCompilation

compileHistoricalMechanism :
  String →
  SourceTotalReceipt →
  ReviewedJoinReceipt →
  DualChronologyReceipt →
  CausalMechanismReceipt →
  HistoricalMechanismWitness
compileHistoricalMechanism ref sourceTotal reviewedJoin chronology causal =
  historical-mechanism-witness
    ref
    sourceTotal
    reviewedJoin
    chronology
    causal
    false refl
    false refl

------------------------------------------------------------------------
-- No shortcut constructors.
------------------------------------------------------------------------

data SourceTotalityAloneCreatesMechanism : Set where
data ReviewedJoinAloneCreatesMechanism : Set where
data ChronologyAloneCreatesMechanism : Set where
data CausalHypothesisAloneCreatesMechanism : Set where
data AbstentionMayBePromotedToClosure : Set where
data ClosedMechanismCreatesPoliticalVerdict : Set where

sourceTotalityAloneDoesNotCreateMechanism :
  SourceTotalityAloneCreatesMechanism → ⊥
sourceTotalityAloneDoesNotCreateMechanism ()

reviewedJoinAloneDoesNotCreateMechanism :
  ReviewedJoinAloneCreatesMechanism → ⊥
reviewedJoinAloneDoesNotCreateMechanism ()

chronologyAloneDoesNotCreateMechanism :
  ChronologyAloneCreatesMechanism → ⊥
chronologyAloneDoesNotCreateMechanism ()

causalHypothesisAloneDoesNotCreateMechanism :
  CausalHypothesisAloneCreatesMechanism → ⊥
causalHypothesisAloneDoesNotCreateMechanism ()

abstentionDoesNotPromoteToClosure :
  AbstentionMayBePromotedToClosure → ⊥
abstentionDoesNotPromoteToClosure ()

closedMechanismDoesNotCreatePoliticalVerdict :
  ClosedMechanismCreatesPoliticalVerdict → ⊥
closedMechanismDoesNotCreatePoliticalVerdict ()

record HistoricalMechanismCompilerBoundary : Set where
  constructor historical-mechanism-compiler-boundary
  field
    sourceTotalityRequired : Bool
    reviewedJoinRequired : Bool
    dualChronologyRequired : Bool
    causalMechanismRequired : Bool
    missingPremiseRetainedAsResidual : Bool
    closureCreatesPoliticalVerdict : Bool
    closureCreatesUniversalRanking : Bool

canonicalHistoricalMechanismCompilerBoundary :
  HistoricalMechanismCompilerBoundary
canonicalHistoricalMechanismCompilerBoundary =
  historical-mechanism-compiler-boundary
    true true true true true false false
