module DASHI.Cognition.PNF.SensibLawITIRNarrativeComparisonTransportExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.NarrativeClaimProvenanceExact as Narrative
import DASHI.Cognition.PNF.SensibLawClaimLatticeNarrativeStatusLiveBidiExact as StatusBridge

------------------------------------------------------------------------
-- SENSIBLAW / ITIR NARRATIVE COMPARISON TRANSPORT
--
-- Mirrors the implemented public-media comparison contract:
--
-- source span -> attribution wrapper -> proposition -> claim link ->
-- argument family -> narrative -> pairwise comparison
--
-- Causal links require link_type, confidence and counter_hypothesis_ref.
-- Missing provenance forces abstention / non-promotion.
------------------------------------------------------------------------

data LinkKind : Set where
  asserts : LinkKind
  attributesTo : LinkKind
  supports : LinkKind
  undermines : LinkKind
  cites : LinkKind

data LinkType : Set where
  attributionLink : LinkType
  causalSupport : LinkType
  causalDispute : LinkType
  citationLink : LinkType
  nonCausalAssociation : LinkType

data Confidence : Set where
  high : Confidence
  medium : Confidence
  low : Confidence
  abstain : Confidence

data ArgumentFamily : Set where
  cprsBlocking : ArgumentFamily
  woolworthsPrice : ArgumentFamily
  governmentCapacity : ArgumentFamily
  etsDelayAuthority : ArgumentFamily
  fallacies : ArgumentFamily
  otherArgumentFamily : ArgumentFamily

record SourceSpan : Set where
  constructor source-span
  field
    sourceId : String
    spanId : String
    textRef : String
    publicReproducible : Bool

open SourceSpan public

record AttributedProposition : Set where
  constructor attributed-proposition
  field
    propositionId : String
    predicateKey : String
    sourceSpan : SourceSpan
    speaker : String
    attributedAuthority : String
    modality : Narrative.ClaimModality
    argumentFamily : ArgumentFamily

open AttributedProposition public

record ClaimLink : Set where
  constructor claim-link
  field
    linkId : String
    kind : LinkKind
    fromProposition : String
    toProposition : String
    linkType : LinkType
    confidence : Confidence
    counterHypothesisRef : String
    provenanceReceipt : String
    completeForPublicArtifact : Bool

open ClaimLink public

record NarrativeLane : Set where
  constructor narrative-lane
  field
    laneId : String
    propositions : List AttributedProposition
    links : List ClaimLink
    hiddenTruthScore : Bool
    canonicalVerdict : Bool

open NarrativeLane public

data ComparisonStatus : Set where
  shared : ComparisonStatus
  leftOnly : ComparisonStatus
  rightOnly : ComparisonStatus
  disputed : ComparisonStatus
  unresolved : ComparisonStatus

record ComparisonRow : Set where
  constructor comparison-row
  field
    rowId : String
    status : ComparisonStatus
    leftPropositionRef : String
    rightPropositionRef : String
    reasoningDifference : String
    sourceLocalReceipt : String
    promotesTruth : Bool

open ComparisonRow public

record NarrativeComparison : Set where
  constructor narrative-comparison
  field
    left : NarrativeLane
    right : NarrativeLane
    rows : List ComparisonRow
    disagreementPreserved : Bool
    abstentionPreserved : Bool
    mergedCanonicalStory : Bool
    truthScoreProduced : Bool

open NarrativeComparison public

canonicalLaneBoundary :
  String → List AttributedProposition → List ClaimLink → NarrativeLane
canonicalLaneBoundary laneId propositions links =
  narrative-lane laneId propositions links false false

canonicalComparison :
  NarrativeLane → NarrativeLane → List ComparisonRow → NarrativeComparison
canonicalComparison left right rows =
  narrative-comparison left right rows true true false false

record PublicCausalLinkReceipt (link : ClaimLink) : Set where
  constructor public-causal-link-receipt
  field
    isCausal :
      kind link ≡ supports ⊎ kind link ≡ undermines
    complete :
      completeForPublicArtifact link ≡ true
    counterHypothesisPresent : String

open PublicCausalLinkReceipt public

data MissingCausalProvenanceMayPromote : Set where
data AttributionWrapperEqualsUnderlyingClaim : Set where
data ComparisonProducesTruthScore : Set where
data CompetingNarrativesMayMergeSilently : Set where
data CorroborationAdmitsTruth : Set where

missingCausalProvenanceDoesNotPromote :
  MissingCausalProvenanceMayPromote → ⊥
missingCausalProvenanceDoesNotPromote ()

attributionWrapperDoesNotEqualUnderlyingClaim :
  AttributionWrapperEqualsUnderlyingClaim → ⊥
attributionWrapperDoesNotEqualUnderlyingClaim ()

comparisonDoesNotProduceTruthScore :
  ComparisonProducesTruthScore → ⊥
comparisonDoesNotProduceTruthScore ()

competingNarrativesDoNotMergeSilently :
  CompetingNarrativesMayMergeSilently → ⊥
competingNarrativesDoNotMergeSilently ()

corroborationStillDoesNotAdmitTruth :
  CorroborationAdmitsTruth → ⊥
corroborationStillDoesNotAdmitTruth ()

compileModalityStillLeavesTruthUnresolved :
  (p : AttributedProposition) →
  let receipt =
        StatusBridge.compileNarrativeModality
          (propositionId p)
          ("event:" ++ propositionId p)
          (modality p)
  in
  DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact.truthStatus
    (StatusBridge.NarrativeModalityStatusReceipt.proposition receipt)
  ≡ DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact.truthUnresolved
compileModalityStillLeavesTruthUnresolved p = refl
