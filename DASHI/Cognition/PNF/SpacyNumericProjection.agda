module DASHI.Cognition.PNF.SpacyNumericProjection where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.EventAlgebra as ExistingPNF
open import DASHI.Cognition.PNF.NumericAuthority

------------------------------------------------------------------------
-- spaCy is an observation producer, not semantic authority.
------------------------------------------------------------------------

spacyProducerWitness : ExistingPNF.ParserProducer
spacyProducerWitness = ExistingPNF.spaCyProducer

data Capability : Set where
  tokenizationCapability sentenceSegmentationCapability : Capability
  lemmaCapability posCapability tagCapability dependencyCapability : Capability
  morphologyCapability namedEntityCapability : Capability

data NumericAnnotation : Set where
  annotationPresent : SymbolId → NumericAnnotation
  annotationUnavailable : Capability → NumericAnnotation

data LemmaObservation : Set where
  parserLemma : SymbolId → LemmaObservation
  orthFallbackLemma : SymbolId → LemmaObservation

record PipelineCapabilityReceipt : Set where
  constructor pipelineCapabilityReceipt
  field
    tokenizationAvailable : Bool
    sentenceSegmentationAvailable : Bool
    lemmaAvailable : Bool
    posAvailable : Bool
    tagAvailable : Bool
    dependencyAvailable : Bool
    morphologyAvailable : Bool
    namedEntityAvailable : Bool

open PipelineCapabilityReceipt public

------------------------------------------------------------------------
-- Sentence ownership is explicit. A crossing sentence becomes a repair
-- obligation; it is never silently truncated into an owned sentence.
------------------------------------------------------------------------

data SentenceOwnership : Set where
  fullyOwned boundaryCrossing outsideOwner : SentenceOwnership

data SentenceDisposition : Set where
  commitSentence queueBoundaryRepair ignoreOutside : SentenceDisposition

disposeSentence : SentenceOwnership → SentenceDisposition
disposeSentence fullyOwned = commitSentence
disposeSentence boundaryCrossing = queueBoundaryRepair
disposeSentence outsideOwner = ignoreOutside

crossingNeverCommits : disposeSentence boundaryCrossing ≡ queueBoundaryRepair
crossingNeverCommits = refl

------------------------------------------------------------------------
-- Dependency heads.
--
-- spaCy roots point to themselves. A non-self head must be found in the
-- committed numeric token map. Missing lookup is a projection failure, not a
-- license to rewrite the dependency as a self-loop.
------------------------------------------------------------------------

data HeadDeclaration : Set where
  declaredSelfHead : HeadDeclaration
  declaredHeadAt : Nat → Nat → HeadDeclaration

data HeadLookup : Set where
  foundHead : TokenId → HeadLookup
  missingHead : HeadLookup

data HeadProjection (self : TokenId) : Set where
  rootProjected : HeadProjection self
  dependencyProjected : TokenId → HeadProjection self
  headProjectionFailure : HeadProjection self

projectHead : (self : TokenId) → HeadDeclaration → HeadLookup → HeadProjection self
projectHead self declaredSelfHead lookup = rootProjected
projectHead self (declaredHeadAt start end) (foundHead head) = dependencyProjected head
projectHead self (declaredHeadAt start end) missingHead = headProjectionFailure

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

data HeadCommit (self : TokenId) : Set where
  rootCommit : HeadCommit self
  dependencyCommit : TokenId → HeadCommit self

commitHead : ∀ {self} → HeadProjection self → Maybe (HeadCommit self)
commitHead rootProjected = just rootCommit
commitHead (dependencyProjected head) = just (dependencyCommit head)
commitHead headProjectionFailure = nothing

headCommitId : ∀ {self} → HeadCommit self → TokenId
headCommitId {self} rootCommit = self
headCommitId (dependencyCommit head) = head

rootHeadIsSelf : ∀ self lookup →
  commitHead (projectHead self declaredSelfHead lookup) ≡ just rootCommit
rootHeadIsSelf self lookup = refl

missingDependentHeadCannotCommit : ∀ self start end →
  commitHead (projectHead self (declaredHeadAt start end) missingHead) ≡ nothing
missingDependentHeadCannotCommit self start end = refl

failureIsNotRoot : ∀ {self} → headProjectionFailure {self} ≡ rootProjected → ⊥
failureIsNotRoot ()

------------------------------------------------------------------------
-- Numeric parser observation. Capability absence is typed as absence; it is
-- not encoded as a meaningful empty-string symbol.
------------------------------------------------------------------------

record SpacyTokenObservation : Set where
  constructor spacyTokenObservation
  field
    token : TokenId
    sentence : SentenceId
    localOrdinal : Nat
    startChar endChar : Nat
    orth : SymbolId
    lemma : LemmaObservation
    pos tag dependency : NumericAnnotation
    morphology : Maybe MorphSetId
    declaredHead : HeadDeclaration

open SpacyTokenObservation public

record NumericTokenRow : Set where
  constructor numericTokenRow
  field
    observation : SpacyTokenObservation
    committedHead : HeadCommit (token observation)

open NumericTokenRow public

committedHeadToken : NumericTokenRow → TokenId
committedHeadToken row = headCommitId (committedHead row)

record SpacyProjectionBoundary : Set where
  constructor spacyProjectionBoundary
  field
    missingHeadFallsBackToSelf : Bool
    missingHeadFallsBackToSelfIsFalse : missingHeadFallsBackToSelf ≡ false
    unavailableAnnotationEncodedAsEmptySymbol : Bool
    unavailableAnnotationEncodedAsEmptySymbolIsFalse :
      unavailableAnnotationEncodedAsEmptySymbol ≡ false
    crossingSentenceCommittedAsPartialSentence : Bool
    crossingSentenceCommittedAsPartialSentenceIsFalse :
      crossingSentenceCommittedAsPartialSentence ≡ false
    dependencyGraphDuplicatedAfterTokenHeadCommit : Bool
    dependencyGraphDuplicatedAfterTokenHeadCommitIsFalse :
      dependencyGraphDuplicatedAfterTokenHeadCommit ≡ false
    parserDirectlyPromotesWorldFact : Bool
    parserDirectlyPromotesWorldFactIsFalse : parserDirectlyPromotesWorldFact ≡ false

canonicalSpacyProjectionBoundary : SpacyProjectionBoundary
canonicalSpacyProjectionBoundary =
  spacyProjectionBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
