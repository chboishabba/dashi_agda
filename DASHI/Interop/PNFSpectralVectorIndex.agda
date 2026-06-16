module DASHI.Interop.PNFSpectralVectorIndex where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Interop.PNFSpectralFieldCore as Core
import DASHI.Interop.VectorNonAuthorityCore as VectorNA

------------------------------------------------------------------------
-- Vector-index boundary for PNF spectral navigation.
--
-- This module types the ANN / embedding lane as a proposal surface only.
-- Vector rows point from coordinates to object references; they do not carry
-- committed support, truth, admissibility, or ITIR authority.  A candidate can
-- only move through resolver anchoring, selector admission, and an explicit
-- ITIR commit stage.

data EmbeddingMethodTag : Set where
  textEmbeddingV1 : EmbeddingMethodTag
  pnfSpectralLaplacianV1 : EmbeddingMethodTag
  signedResidualLaplacianV1 : EmbeddingMethodTag
  braidTransportSpectrumV1 : EmbeddingMethodTag

canonicalEmbeddingMethods : List EmbeddingMethodTag
canonicalEmbeddingMethods =
  textEmbeddingV1
  ∷ pnfSpectralLaplacianV1
  ∷ signedResidualLaplacianV1
  ∷ braidTransportSpectrumV1
  ∷ []

data ⊤-local : Set where
  tt-local : ⊤-local

data VectorCoordinate : Set where
  vectorCoordinate : Nat → String → VectorCoordinate

data MetricGuaranteeKind : Set where
  exactMetricGuarantee : MetricGuaranteeKind
  annMetricGuarantee : MetricGuaranteeKind

canonicalMetricGuaranteeKinds : List MetricGuaranteeKind
canonicalMetricGuaranteeKinds =
  exactMetricGuarantee
  ∷ annMetricGuarantee
  ∷ []

record VectorMetricGuarantee : Set where
  constructor vectorMetricGuarantee
  field
    metricGuaranteeKind : MetricGuaranteeKind
    metricGuaranteeMethod : EmbeddingMethodTag
    metricGuaranteeProfile : String
    metricIsOperatorRelative : Bool
    exactMetricBoundAvailable : Bool
    annMetricBoundAvailable : Bool
    metricGuaranteeProximityOnly : Bool
    metricGuaranteeCarriesCommittedSupport : Bool
    metricGuaranteeCarriesTruth : Bool
    metricGuaranteeCarriesAdmissibility : Bool
    metricGuaranteeFailClosed : Bool

open VectorMetricGuarantee public

canonicalMetricGuaranteeBoundary :
  ∀ guarantee →
  metricGuaranteeProximityOnly guarantee ≡ true →
  metricGuaranteeCarriesCommittedSupport guarantee ≡ false →
  metricGuaranteeCarriesTruth guarantee ≡ false →
  metricGuaranteeCarriesAdmissibility guarantee ≡ false →
  metricGuaranteeFailClosed guarantee ≡ true →
  Set
canonicalMetricGuaranteeBoundary _ _ _ _ _ _ =
  ⊤-local

data PNFGraphOperatorTag : Set where
  pnfAdjacencyOperatorV1 : PNFGraphOperatorTag
  pnfResidualLaplacianOperatorV1 : PNFGraphOperatorTag
  pnfSignedBraidTransportOperatorV1 : PNFGraphOperatorTag

canonicalPNFGraphOperators : List PNFGraphOperatorTag
canonicalPNFGraphOperators =
  pnfAdjacencyOperatorV1
  ∷ pnfResidualLaplacianOperatorV1
  ∷ pnfSignedBraidTransportOperatorV1
  ∷ []

record ObjectRef : Set where
  constructor objectRef
  field
    coreObjectRef : Core.PredicateObjectRef
    objectRefLabel : String

open ObjectRef public

record VectorIndexRow : Set where
  constructor vectorIndexRow
  field
    embeddingMethod : EmbeddingMethodTag
    coordinate : VectorCoordinate
    referencedObject : ObjectRef
    rowProximityOnly : Bool
    rowCarriesCommittedSupport : Bool
    rowCarriesTruth : Bool
    rowCarriesAdmissibility : Bool

open VectorIndexRow public

record PNFGraphOperatorProximity : Set where
  constructor pnfGraphOperatorProximity
  field
    graphOperator : PNFGraphOperatorTag
    graphSourceRow : VectorIndexRow
    graphTargetRow : VectorIndexRow
    graphOperatorProfile : String
    graphOperatorRelative : Bool
    graphProximityOnly : Bool
    graphCarriesCommittedSupport : Bool
    graphCarriesTruth : Bool
    graphCarriesAdmissibility : Bool
    graphProximityFailClosed : Bool

open PNFGraphOperatorProximity public

canonicalGraphOperatorProximityBoundary :
  ∀ proximity →
  graphOperatorRelative proximity ≡ true →
  graphProximityOnly proximity ≡ true →
  graphCarriesCommittedSupport proximity ≡ false →
  graphCarriesTruth proximity ≡ false →
  graphCarriesAdmissibility proximity ≡ false →
  graphProximityFailClosed proximity ≡ true →
  Set
canonicalGraphOperatorProximityBoundary _ _ _ _ _ _ _ =
  ⊤-local

canonicalIndexRowBoundary :
  ∀ row →
  rowProximityOnly row ≡ true →
  rowCarriesCommittedSupport row ≡ false →
  rowCarriesTruth row ≡ false →
  rowCarriesAdmissibility row ≡ false →
  Set
canonicalIndexRowBoundary _ _ _ _ _ =
  ⊤-local

data CommittedSupportFromVector : Set where

committedSupportFromVectorImpossible :
  CommittedSupportFromVector →
  ⊥
committedSupportFromVectorImpossible ()

record CandidateRef : Set where
  constructor candidateRef
  field
    coreCandidateToken : Core.CandidateRef
    candidateObject : ObjectRef
    candidateMethod : EmbeddingMethodTag
    candidateCoordinate : VectorCoordinate
    candidateRank : Nat
    candidateProximityOnly : Bool
    candidateCommittedSupport : Bool

open CandidateRef public

data VectorArithmeticProposalKind : Set where
  vectorAdditionProposal : VectorArithmeticProposalKind
  vectorDifferenceProposal : VectorArithmeticProposalKind
  scalarStepProposal : VectorArithmeticProposalKind

canonicalVectorArithmeticProposalKinds : List VectorArithmeticProposalKind
canonicalVectorArithmeticProposalKinds =
  vectorAdditionProposal
  ∷ vectorDifferenceProposal
  ∷ scalarStepProposal
  ∷ []

record VectorArithmeticProposalRow : Set where
  constructor vectorArithmeticProposalRow
  field
    arithmeticProposalKind : VectorArithmeticProposalKind
    arithmeticSourceCandidate : CandidateRef
    arithmeticSourceCoordinate : VectorCoordinate
    arithmeticTransportCoordinate : VectorCoordinate
    arithmeticProposedObject : ObjectRef
    arithmeticProposalProfile : String
    arithmeticIsCandidateTransportProposal : Bool
    arithmeticCarriesCommittedSupport : Bool
    arithmeticCarriesTruth : Bool
    arithmeticCarriesAdmissibility : Bool
    arithmeticProposalFailClosed : Bool

open VectorArithmeticProposalRow public

canonicalArithmeticProposalBoundary :
  ∀ proposal →
  arithmeticIsCandidateTransportProposal proposal ≡ true →
  arithmeticCarriesCommittedSupport proposal ≡ false →
  arithmeticCarriesTruth proposal ≡ false →
  arithmeticCarriesAdmissibility proposal ≡ false →
  arithmeticProposalFailClosed proposal ≡ true →
  Set
canonicalArithmeticProposalBoundary _ _ _ _ _ _ =
  ⊤-local

rowToCandidateRef : Nat → VectorIndexRow → CandidateRef
rowToCandidateRef rank row =
  candidateRef
    (Core.PredicateObjectRef.candidate
      (coreObjectRef (referencedObject row)))
    (referencedObject row)
    (embeddingMethod row)
    (coordinate row)
    rank
    true
    false

rowToCandidateRefProximityOnly :
  ∀ rank row →
  candidateProximityOnly (rowToCandidateRef rank row) ≡ true
rowToCandidateRefProximityOnly _ _ =
  refl

rowToCandidateRefNoCommittedSupport :
  ∀ rank row →
  candidateCommittedSupport (rowToCandidateRef rank row) ≡ false
rowToCandidateRefNoCommittedSupport _ _ =
  refl

record VectorSearchReceipt : Set where
  constructor vectorSearchReceipt
  field
    queryCoordinate : VectorCoordinate
    searchedRows : List VectorIndexRow
    returnedCandidates : List CandidateRef
    vectorStageOnlyProposes : Bool
    searchReturnsCandidateRefOnly : Bool
    searchReturnsCommittedSupport : Bool
    runtimeANNAvailable : Bool
    externalEmbeddingModelAvailable : Bool
    absentProvidersFailClosed : Bool

open VectorSearchReceipt public

emptyVectorSearchReceipt :
  VectorCoordinate →
  VectorSearchReceipt
emptyVectorSearchReceipt query =
  vectorSearchReceipt
    query
    []
    []
    true
    true
    false
    false
    false
    true

emptySearchFailsClosed :
  ∀ query →
  absentProvidersFailClosed (emptyVectorSearchReceipt query) ≡ true
emptySearchFailsClosed _ =
  refl

emptySearchHasNoRuntimeANN :
  ∀ query →
  runtimeANNAvailable (emptyVectorSearchReceipt query) ≡ false
emptySearchHasNoRuntimeANN _ =
  refl

emptySearchHasNoExternalEmbeddingModel :
  ∀ query →
  externalEmbeddingModelAvailable (emptyVectorSearchReceipt query) ≡ false
emptySearchHasNoExternalEmbeddingModel _ =
  refl

------------------------------------------------------------------------
-- Pipeline authority stages.

data NavigationStage : Set where
  vectorProposes : NavigationStage
  resolverAnchors : NavigationStage
  selectorAdmits : NavigationStage
  itirCommits : NavigationStage

canonicalNavigationStages : List NavigationStage
canonicalNavigationStages =
  vectorProposes
  ∷ resolverAnchors
  ∷ selectorAdmits
  ∷ itirCommits
  ∷ []

record ResolverAnchor : Set where
  constructor resolverAnchor
  field
    anchoredCandidate : CandidateRef
    resolvedObject : ObjectRef
    resolverProfile : String
    resolverAnchored : Bool
    resolverConsumedVectorAsTruth : Bool
    resolverCommittedSupport : Bool

open ResolverAnchor public

anchorCandidate :
  String →
  CandidateRef →
  ResolverAnchor
anchorCandidate profile candidate =
  resolverAnchor
    candidate
    (candidateObject candidate)
    profile
    true
    false
    false

anchorDoesNotConsumeVectorAsTruth :
  ∀ profile candidate →
  resolverConsumedVectorAsTruth (anchorCandidate profile candidate) ≡ false
anchorDoesNotConsumeVectorAsTruth _ _ =
  refl

anchorDoesNotCommitSupport :
  ∀ profile candidate →
  resolverCommittedSupport (anchorCandidate profile candidate) ≡ false
anchorDoesNotCommitSupport _ _ =
  refl

record SelectorAdmission : Set where
  constructor selectorAdmission
  field
    selectedAnchor : ResolverAnchor
    residualLevel : Residual.ResidualLevel
    selectorProfile : String
    selectorAdmitted : Bool
    selectorUsedVectorProximityAsAdmissibility : Bool
    selectorCommittedSupport : Bool

open SelectorAdmission public

admitAnchoredCandidate :
  String →
  ResolverAnchor →
  Residual.ResidualLevel →
  SelectorAdmission
admitAnchoredCandidate profile anchor residual =
  selectorAdmission
    anchor
    residual
    profile
    true
    false
    false

selectorDoesNotUseVectorProximityAsAdmissibility :
  ∀ profile anchor residual →
  selectorUsedVectorProximityAsAdmissibility
    (admitAnchoredCandidate profile anchor residual)
  ≡
  false
selectorDoesNotUseVectorProximityAsAdmissibility _ _ _ =
  refl

selectorDoesNotCommitSupport :
  ∀ profile anchor residual →
  selectorCommittedSupport (admitAnchoredCandidate profile anchor residual)
  ≡
  false
selectorDoesNotCommitSupport _ _ _ =
  refl

record ITIRCommitReceipt : Set where
  constructor itirCommitReceipt
  field
    admittedSelection : SelectorAdmission
    itirProfile : String
    itirCommitted : Bool
    commitConsumesResolverAnchor : Bool
    commitConsumesSelectorAdmission : Bool
    commitConsumesVectorAsSupport : Bool

open ITIRCommitReceipt public

commitAdmittedSelection :
  String →
  SelectorAdmission →
  ITIRCommitReceipt
commitAdmittedSelection profile admission =
  itirCommitReceipt
    admission
    profile
    true
    true
    true
    false

itirCommitDoesNotConsumeVectorAsSupport :
  ∀ profile admission →
  commitConsumesVectorAsSupport (commitAdmittedSelection profile admission)
  ≡
  false
itirCommitDoesNotConsumeVectorAsSupport _ _ =
  refl

------------------------------------------------------------------------
-- End-to-end receipt.

canonicalVectorBoundaryStatement : String
canonicalVectorBoundaryStatement =
  "Vector proximity is a navigation proposal only. It is not truth, committed support, or admissibility; resolver anchoring, selector admission, and ITIR commit are separate authority stages."

canonicalProviderBoundaryStatement : String
canonicalProviderBoundaryStatement =
  "Runtime ANN providers and external embedding models are absent in this Agda receipt; provider absence fails closed and yields no runtime search authority."

record PNFSpectralVectorIndexReceipt : Set where
  constructor pnfSpectralVectorIndexReceipt
  field
    methods : List EmbeddingMethodTag
    methodsAreCanonical : methods ≡ canonicalEmbeddingMethods

    stages : List NavigationStage
    stagesAreCanonical : stages ≡ canonicalNavigationStages

    sampleCoordinate : VectorCoordinate
    sampleObject : ObjectRef
    sampleRow : VectorIndexRow
    sampleRowMethodIsPNFSpectral :
      embeddingMethod sampleRow ≡ pnfSpectralLaplacianV1
    sampleRowObjectRefOnly :
      referencedObject sampleRow ≡ sampleObject
    sampleRowProximityOnly :
      rowProximityOnly sampleRow ≡ true
    sampleRowCommittedSupportIsFalse :
      rowCarriesCommittedSupport sampleRow ≡ false
    sampleRowTruthIsFalse :
      rowCarriesTruth sampleRow ≡ false
    sampleRowAdmissibilityIsFalse :
      rowCarriesAdmissibility sampleRow ≡ false

    sampleCandidate : CandidateRef
    sampleCandidateIsFromRow :
      sampleCandidate ≡ rowToCandidateRef zero sampleRow
    sampleCandidateCommittedSupportIsFalse :
      candidateCommittedSupport sampleCandidate ≡ false

    searchReceipt : VectorSearchReceipt
    searchStageOnlyProposes :
      vectorStageOnlyProposes searchReceipt ≡ true
    searchCandidateRefOnly :
      searchReturnsCandidateRefOnly searchReceipt ≡ true
    searchCommittedSupportIsFalse :
      searchReturnsCommittedSupport searchReceipt ≡ false
    runtimeANNAbsent :
      runtimeANNAvailable searchReceipt ≡ false
    externalEmbeddingModelAbsent :
      externalEmbeddingModelAvailable searchReceipt ≡ false
    absentProvidersFailClosedHere :
      absentProvidersFailClosed searchReceipt ≡ true

    resolverReceipt : ResolverAnchor
    resolverCandidateIsSample :
      anchoredCandidate resolverReceipt ≡ sampleCandidate
    resolverAnchoredHere :
      resolverAnchored resolverReceipt ≡ true
    resolverVectorTruthIsFalse :
      resolverConsumedVectorAsTruth resolverReceipt ≡ false
    resolverCommitIsFalse :
      resolverCommittedSupport resolverReceipt ≡ false

    selectorReceipt : SelectorAdmission
    selectorAnchorIsResolver :
      selectedAnchor selectorReceipt ≡ resolverReceipt
    selectorAdmittedHere :
      selectorAdmitted selectorReceipt ≡ true
    selectorVectorAdmissibilityIsFalse :
      selectorUsedVectorProximityAsAdmissibility selectorReceipt ≡ false
    selectorCommitIsFalse :
      selectorCommittedSupport selectorReceipt ≡ false

    itirReceipt : ITIRCommitReceipt
    itirAdmissionIsSelector :
      admittedSelection itirReceipt ≡ selectorReceipt
    itirCommittedHere :
      itirCommitted itirReceipt ≡ true
    itirConsumesResolver :
      commitConsumesResolverAnchor itirReceipt ≡ true
    itirConsumesSelector :
      commitConsumesSelectorAdmission itirReceipt ≡ true
    itirVectorSupportIsFalse :
      commitConsumesVectorAsSupport itirReceipt ≡ false

    vectorProximityIsTruth : Bool
    vectorProximityIsTruthIsFalse :
      vectorProximityIsTruth ≡ false

    vectorProximityIsSupport : Bool
    vectorProximityIsSupportIsFalse :
      vectorProximityIsSupport ≡ false

    vectorProximityIsAdmissibility : Bool
    vectorProximityIsAdmissibilityIsFalse :
      vectorProximityIsAdmissibility ≡ false

    boundaryStatement : String
    boundaryStatementIsCanonical :
      boundaryStatement ≡ canonicalVectorBoundaryStatement

    providerBoundaryStatement : String
    providerBoundaryStatementIsCanonical :
      providerBoundaryStatement ≡ canonicalProviderBoundaryStatement

    metricGuaranteeKinds : List MetricGuaranteeKind
    metricGuaranteeKindsAreCanonical :
      metricGuaranteeKinds ≡ canonicalMetricGuaranteeKinds

    graphOperators : List PNFGraphOperatorTag
    graphOperatorsAreCanonical :
      graphOperators ≡ canonicalPNFGraphOperators

    arithmeticProposalKinds : List VectorArithmeticProposalKind
    arithmeticProposalKindsAreCanonical :
      arithmeticProposalKinds ≡ canonicalVectorArithmeticProposalKinds

    exactMetricGuaranteeReceipt : VectorMetricGuarantee
    exactMetricGuaranteeKindIsExact :
      metricGuaranteeKind exactMetricGuaranteeReceipt ≡ exactMetricGuarantee
    exactMetricGuaranteeOperatorRelative :
      metricIsOperatorRelative exactMetricGuaranteeReceipt ≡ true
    exactMetricBoundAvailableHere :
      exactMetricBoundAvailable exactMetricGuaranteeReceipt ≡ true
    exactMetricANNBoundUnavailable :
      annMetricBoundAvailable exactMetricGuaranteeReceipt ≡ false
    exactMetricGuaranteeProximityOnly :
      metricGuaranteeProximityOnly exactMetricGuaranteeReceipt ≡ true
    exactMetricGuaranteeSupportIsFalse :
      metricGuaranteeCarriesCommittedSupport exactMetricGuaranteeReceipt ≡ false
    exactMetricGuaranteeTruthIsFalse :
      metricGuaranteeCarriesTruth exactMetricGuaranteeReceipt ≡ false
    exactMetricGuaranteeAdmissibilityIsFalse :
      metricGuaranteeCarriesAdmissibility exactMetricGuaranteeReceipt ≡ false
    exactMetricGuaranteeFailClosedHere :
      metricGuaranteeFailClosed exactMetricGuaranteeReceipt ≡ true

    annMetricGuaranteeReceipt : VectorMetricGuarantee
    annMetricGuaranteeKindIsANN :
      metricGuaranteeKind annMetricGuaranteeReceipt ≡ annMetricGuarantee
    annMetricGuaranteeOperatorRelative :
      metricIsOperatorRelative annMetricGuaranteeReceipt ≡ true
    annMetricExactBoundUnavailable :
      exactMetricBoundAvailable annMetricGuaranteeReceipt ≡ false
    annMetricBoundUnavailableFailClosed :
      annMetricBoundAvailable annMetricGuaranteeReceipt ≡ false
    annMetricGuaranteeProximityOnly :
      metricGuaranteeProximityOnly annMetricGuaranteeReceipt ≡ true
    annMetricGuaranteeSupportIsFalse :
      metricGuaranteeCarriesCommittedSupport annMetricGuaranteeReceipt ≡ false
    annMetricGuaranteeTruthIsFalse :
      metricGuaranteeCarriesTruth annMetricGuaranteeReceipt ≡ false
    annMetricGuaranteeAdmissibilityIsFalse :
      metricGuaranteeCarriesAdmissibility annMetricGuaranteeReceipt ≡ false
    annMetricGuaranteeFailClosedHere :
      metricGuaranteeFailClosed annMetricGuaranteeReceipt ≡ true

    graphOperatorProximityReceipt : PNFGraphOperatorProximity
    graphOperatorProximityIsOperatorRelative :
      graphOperatorRelative graphOperatorProximityReceipt ≡ true
    graphOperatorProximityOnlyHere :
      graphProximityOnly graphOperatorProximityReceipt ≡ true
    graphOperatorSupportIsFalse :
      graphCarriesCommittedSupport graphOperatorProximityReceipt ≡ false
    graphOperatorTruthIsFalse :
      graphCarriesTruth graphOperatorProximityReceipt ≡ false
    graphOperatorAdmissibilityIsFalse :
      graphCarriesAdmissibility graphOperatorProximityReceipt ≡ false
    graphOperatorFailClosedHere :
      graphProximityFailClosed graphOperatorProximityReceipt ≡ true

    arithmeticProposalReceipt : VectorArithmeticProposalRow
    arithmeticProposalCandidateTransportOnly :
      arithmeticIsCandidateTransportProposal arithmeticProposalReceipt ≡ true
    arithmeticProposalSupportIsFalse :
      arithmeticCarriesCommittedSupport arithmeticProposalReceipt ≡ false
    arithmeticProposalTruthIsFalse :
      arithmeticCarriesTruth arithmeticProposalReceipt ≡ false
    arithmeticProposalAdmissibilityIsFalse :
      arithmeticCarriesAdmissibility arithmeticProposalReceipt ≡ false
    arithmeticProposalFailClosedHere :
      arithmeticProposalFailClosed arithmeticProposalReceipt ≡ true

    vectorNonAuthorityCoreAdapter :
      VectorNA.VectorNonAuthorityReceipt

    vectorNonAuthorityCoreAdapterIsCanonical :
      vectorNonAuthorityCoreAdapter
      ≡
      VectorNA.canonicalVectorNonAuthorityReceipt

    vectorNonAuthorityCoreTruthFalse :
      VectorNA.proposalRowCarriesTruthAuthority
        (VectorNA.receiptProposalRow vectorNonAuthorityCoreAdapter)
      ≡
      false

    vectorNonAuthorityCoreSupportFalse :
      VectorNA.proposalRowCarriesSupportAuthority
        (VectorNA.receiptProposalRow vectorNonAuthorityCoreAdapter)
      ≡
      false

    vectorNonAuthorityCoreAdmissibilityFalse :
      VectorNA.proposalRowCarriesAdmissibilityAuthority
        (VectorNA.receiptProposalRow vectorNonAuthorityCoreAdapter)
      ≡
      false

open PNFSpectralVectorIndexReceipt public

canonicalSampleCoordinate : VectorCoordinate
canonicalSampleCoordinate =
  vectorCoordinate (suc (suc (suc zero))) "pnf-spectral-coordinate"

canonicalSampleObject : ObjectRef
canonicalSampleObject =
  objectRef
    Core.canonicalPredicateObjectRef
    "pnf-object-ref"

canonicalSampleRow : VectorIndexRow
canonicalSampleRow =
  vectorIndexRow
    pnfSpectralLaplacianV1
    canonicalSampleCoordinate
    canonicalSampleObject
    true
    false
    false
    false

canonicalSampleCandidate : CandidateRef
canonicalSampleCandidate =
  rowToCandidateRef zero canonicalSampleRow

canonicalExactMetricGuarantee : VectorMetricGuarantee
canonicalExactMetricGuarantee =
  vectorMetricGuarantee
    exactMetricGuarantee
    pnfSpectralLaplacianV1
    "canonical-exact-operator-relative-metric-v1"
    true
    true
    false
    true
    false
    false
    false
    true

canonicalANNMetricGuarantee : VectorMetricGuarantee
canonicalANNMetricGuarantee =
  vectorMetricGuarantee
    annMetricGuarantee
    pnfSpectralLaplacianV1
    "canonical-ann-operator-relative-metric-v1"
    true
    false
    false
    true
    false
    false
    false
    true

canonicalGraphOperatorProximity : PNFGraphOperatorProximity
canonicalGraphOperatorProximity =
  pnfGraphOperatorProximity
    pnfResidualLaplacianOperatorV1
    canonicalSampleRow
    canonicalSampleRow
    "canonical-pnf-graph-operator-proximity-v1"
    true
    true
    false
    false
    false
    true

canonicalArithmeticProposalRow : VectorArithmeticProposalRow
canonicalArithmeticProposalRow =
  vectorArithmeticProposalRow
    vectorAdditionProposal
    canonicalSampleCandidate
    canonicalSampleCoordinate
    canonicalSampleCoordinate
    canonicalSampleObject
    "canonical-vector-arithmetic-candidate-transport-v1"
    true
    false
    false
    false
    true

canonicalSampleSearchReceipt : VectorSearchReceipt
canonicalSampleSearchReceipt =
  vectorSearchReceipt
    canonicalSampleCoordinate
    (canonicalSampleRow ∷ [])
    (canonicalSampleCandidate ∷ [])
    true
    true
    false
    false
    false
    true

canonicalResolverReceipt : ResolverAnchor
canonicalResolverReceipt =
  anchorCandidate "canonical-resolver-v1" canonicalSampleCandidate

canonicalSelectorReceipt : SelectorAdmission
canonicalSelectorReceipt =
  admitAnchoredCandidate
    "canonical-selector-v1"
    canonicalResolverReceipt
    Residual.partial

canonicalITIRCommitReceipt : ITIRCommitReceipt
canonicalITIRCommitReceipt =
  commitAdmittedSelection "canonical-itir-v1" canonicalSelectorReceipt

canonicalPNFSpectralVectorIndexReceipt :
  PNFSpectralVectorIndexReceipt
canonicalPNFSpectralVectorIndexReceipt =
  pnfSpectralVectorIndexReceipt
    canonicalEmbeddingMethods
    refl
    canonicalNavigationStages
    refl
    canonicalSampleCoordinate
    canonicalSampleObject
    canonicalSampleRow
    refl
    refl
    refl
    refl
    refl
    refl
    canonicalSampleCandidate
    refl
    refl
    canonicalSampleSearchReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    canonicalResolverReceipt
    refl
    refl
    refl
    refl
    canonicalSelectorReceipt
    refl
    refl
    refl
    refl
    canonicalITIRCommitReceipt
    refl
    refl
    refl
    refl
    refl
    false
    refl
    false
    refl
    false
    refl
    canonicalVectorBoundaryStatement
    refl
    canonicalProviderBoundaryStatement
    refl
    canonicalMetricGuaranteeKinds
    refl
    canonicalPNFGraphOperators
    refl
    canonicalVectorArithmeticProposalKinds
    refl
    canonicalExactMetricGuarantee
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    canonicalANNMetricGuarantee
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    canonicalGraphOperatorProximity
    refl
    refl
    refl
    refl
    refl
    refl
    canonicalArithmeticProposalRow
    refl
    refl
    refl
    refl
    refl
    VectorNA.canonicalVectorNonAuthorityReceipt
    refl
    refl
    refl
    refl

canonicalReceipt :
  PNFSpectralVectorIndexReceipt
canonicalReceipt =
  canonicalPNFSpectralVectorIndexReceipt

canonicalReceiptRuntimeANNAbsent :
  runtimeANNAvailable (searchReceipt canonicalReceipt) ≡ false
canonicalReceiptRuntimeANNAbsent =
  refl

canonicalReceiptExternalEmbeddingAbsent :
  externalEmbeddingModelAvailable (searchReceipt canonicalReceipt) ≡ false
canonicalReceiptExternalEmbeddingAbsent =
  refl

canonicalReceiptVectorTruthFalse :
  vectorProximityIsTruth canonicalReceipt ≡ false
canonicalReceiptVectorTruthFalse =
  refl

canonicalReceiptVectorSupportFalse :
  vectorProximityIsSupport canonicalReceipt ≡ false
canonicalReceiptVectorSupportFalse =
  refl

canonicalReceiptVectorAdmissibilityFalse :
  vectorProximityIsAdmissibility canonicalReceipt ≡ false
canonicalReceiptVectorAdmissibilityFalse =
  refl

canonicalReceiptITIRVectorSupportFalse :
  commitConsumesVectorAsSupport (itirReceipt canonicalReceipt) ≡ false
canonicalReceiptITIRVectorSupportFalse =
  refl

canonicalReceiptExactMetricTruthFalse :
  metricGuaranteeCarriesTruth
    (exactMetricGuaranteeReceipt canonicalReceipt)
  ≡
  false
canonicalReceiptExactMetricTruthFalse =
  refl

canonicalReceiptANNMetricBoundUnavailable :
  annMetricBoundAvailable
    (annMetricGuaranteeReceipt canonicalReceipt)
  ≡
  false
canonicalReceiptANNMetricBoundUnavailable =
  refl

canonicalReceiptANNMetricTruthFalse :
  metricGuaranteeCarriesTruth
    (annMetricGuaranteeReceipt canonicalReceipt)
  ≡
  false
canonicalReceiptANNMetricTruthFalse =
  refl

canonicalReceiptGraphOperatorTruthFalse :
  graphCarriesTruth
    (graphOperatorProximityReceipt canonicalReceipt)
  ≡
  false
canonicalReceiptGraphOperatorTruthFalse =
  refl

canonicalReceiptArithmeticProposalTruthFalse :
  arithmeticCarriesTruth
    (arithmeticProposalReceipt canonicalReceipt)
  ≡
  false
canonicalReceiptArithmeticProposalTruthFalse =
  refl

canonicalReceiptArithmeticProposalSupportFalse :
  arithmeticCarriesCommittedSupport
    (arithmeticProposalReceipt canonicalReceipt)
  ≡
  false
canonicalReceiptArithmeticProposalSupportFalse =
  refl

canonicalReceiptArithmeticProposalAdmissibilityFalse :
  arithmeticCarriesAdmissibility
    (arithmeticProposalReceipt canonicalReceipt)
  ≡
  false
canonicalReceiptArithmeticProposalAdmissibilityFalse =
  refl

canonicalReceiptVectorNonAuthorityCoreCanonical :
  vectorNonAuthorityCoreAdapter canonicalReceipt
  ≡
  VectorNA.canonicalVectorNonAuthorityReceipt
canonicalReceiptVectorNonAuthorityCoreCanonical =
  refl

canonicalReceiptVectorNonAuthorityCoreTruthFalse :
  VectorNA.proposalRowCarriesTruthAuthority
    (VectorNA.receiptProposalRow
      (vectorNonAuthorityCoreAdapter canonicalReceipt))
  ≡
  false
canonicalReceiptVectorNonAuthorityCoreTruthFalse =
  refl
