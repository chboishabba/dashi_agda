module DASHI.Cognition.PNF.NumericPNFCompilation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)

open import DASHI.Cognition.PNF.NumericAuthority
open import DASHI.Cognition.PNF.NumericHyperfabric
open import DASHI.Cognition.PNF.SpacyNumericProjection

------------------------------------------------------------------------
-- Durable parser work and fenced completion.
------------------------------------------------------------------------

data ParserPartitionState : Set where
  pendingPartition leasedPartition committedPartition : ParserPartitionState
  stalePartition failedPartition : ParserPartitionState

data FenceComparison : Set where
  matchingFence staleFence : FenceComparison

data PartitionCommitDecision : Set where
  commitPartition rejectStaleAttempt : PartitionCommitDecision

decidePartitionCommit : FenceComparison → PartitionCommitDecision
decidePartitionCommit matchingFence = commitPartition
decidePartitionCommit staleFence = rejectStaleAttempt

staleFenceCannotCommit : decidePartitionCommit staleFence ≡ rejectStaleAttempt
staleFenceCannotCommit = refl

record NumericSentenceWork : Set where
  constructor numericSentenceWork
  field
    workSentence : SentenceId
    parserRows : List NumericTokenRow
    sentenceInterface : ClosedInterface

open NumericSentenceWork public

------------------------------------------------------------------------
-- Strict publication exists only for a closed document interface. The receipt
-- carries residual demands and counts, not a reconstructed legacy document.
------------------------------------------------------------------------

data StrictPublication : CoverageState → Set where
  strictClosedPublication :
    ClosedInterface →
    HumanReference →
    List ResidualDemandSignature →
    Nat → Nat → Nat →
    StrictPublication closedCoverage

openStrictPublicationImpossible : StrictPublication openCoverage → ⊥
openStrictPublicationImpossible ()

record StrictCompilerBypassBoundary : Set where
  constructor strictCompilerBypassBoundary
  field
    legacyDocumentMaterialisation : Bool
    legacyDocumentMaterialisationIsFalse :
      legacyDocumentMaterialisation ≡ false
    legacyProjectionInvoked : Bool
    legacyProjectionInvokedIsFalse : legacyProjectionInvoked ≡ false
    worldResolutionDeferred : Bool
    worldResolutionDeferredIsTrue : worldResolutionDeferred ≡ true
    publicationContainsArbitraryLocalMentions : Bool
    publicationContainsArbitraryLocalMentionsIsFalse :
      publicationContainsArbitraryLocalMentions ≡ false

canonicalStrictCompilerBypassBoundary : StrictCompilerBypassBoundary
canonicalStrictCompilerBypassBoundary =
  strictCompilerBypassBoundary false refl false refl true refl false refl

record NumericCompilationOrder : Set where
  constructor numericCompilationOrder
  field
    parserProjectionBeforeSentenceClosure : Bool
    sentenceClosureBeforeRegionalReduction : Bool
    regionalReductionBeforeDocumentPublication : Bool
    documentPublicationBeforeWorldResolution : Bool

canonicalNumericCompilationOrder : NumericCompilationOrder
canonicalNumericCompilationOrder =
  numericCompilationOrder true true true true
