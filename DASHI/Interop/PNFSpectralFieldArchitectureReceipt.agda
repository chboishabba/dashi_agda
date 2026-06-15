module DASHI.Interop.PNFSpectralFieldArchitectureReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- PNF spectral field architecture receipt.
--
-- This module is an aggregate checked intake receipt for the PNF spectral
-- field stack.  It joins the four local architecture layers into one
-- normalized surface:
--
--   1. core object / fibre field;
--   2. residual weighted graph / Laplacian;
--   3. braid transport;
--   4. vector index / resolver / selector.
--
-- The receipt is intentionally architectural.  It records the intended
-- pipeline and governance boundaries, but it does not implement a runtime
-- parser, ANN backend, semantic truth engine, trading truth engine, or proof
-- that spectral coordinates improve retrieval quality.

data ArchitectureReceiptStatus : Set where
  pnfSpectralFieldArchitectureRecorded_intakeOnly :
    ArchitectureReceiptStatus

data ArchitectureLayer : Set where
  coreObjectFibreFieldLayer :
    ArchitectureLayer

  residualWeightedGraphLaplacianLayer :
    ArchitectureLayer

  braidTransportLayer :
    ArchitectureLayer

  spectralVectorIndexResolverSelectorLayer :
    ArchitectureLayer

canonicalArchitectureLayers : List ArchitectureLayer
canonicalArchitectureLayers =
  coreObjectFibreFieldLayer
  ∷ residualWeightedGraphLaplacianLayer
  ∷ braidTransportLayer
  ∷ spectralVectorIndexResolverSelectorLayer
  ∷ []

data PipelineStage : Set where
  rawEvidenceStage :
    PipelineStage

  evidenceSpanPNFStage :
    PipelineStage

  residualMeetJoinGraphStage :
    PipelineStage

  fibreFieldStage :
    PipelineStage

  braidTransportStage :
    PipelineStage

  spectralCoordinatesStage :
    PipelineStage

  vectorIndexOverReferencesStage :
    PipelineStage

  resolverSelectorStage :
    PipelineStage

  itirValidationStage :
    PipelineStage

  supportPacketAnswerSignalStage :
    PipelineStage

canonicalPipeline : List PipelineStage
canonicalPipeline =
  rawEvidenceStage
  ∷ evidenceSpanPNFStage
  ∷ residualMeetJoinGraphStage
  ∷ fibreFieldStage
  ∷ braidTransportStage
  ∷ spectralCoordinatesStage
  ∷ vectorIndexOverReferencesStage
  ∷ resolverSelectorStage
  ∷ itirValidationStage
  ∷ supportPacketAnswerSignalStage
  ∷ []

data GovernanceBoundary : Set where
  architectureIntakeOnlyBoundary :
    GovernanceBoundary

  noRuntimeParserBoundary :
    GovernanceBoundary

  noANNBackendBoundary :
    GovernanceBoundary

  noSpectralUtilityProofBoundary :
    GovernanceBoundary

  noSemanticTruthBoundary :
    GovernanceBoundary

  noTradingTruthBoundary :
    GovernanceBoundary

canonicalGovernanceBoundaries : List GovernanceBoundary
canonicalGovernanceBoundaries =
  architectureIntakeOnlyBoundary
  ∷ noRuntimeParserBoundary
  ∷ noANNBackendBoundary
  ∷ noSpectralUtilityProofBoundary
  ∷ noSemanticTruthBoundary
  ∷ noTradingTruthBoundary
  ∷ []

data ReceiptProjectionKind : Set where
  projectCoreObjectFibreField :
    ReceiptProjectionKind

  projectResidualWeightedGraphLaplacian :
    ReceiptProjectionKind

  projectBraidTransport :
    ReceiptProjectionKind

  projectSpectralVectorIndexResolverSelector :
    ReceiptProjectionKind

record ComponentReceiptRef : Set where
  field
    projectionKind :
      ReceiptProjectionKind

    layer :
      ArchitectureLayer

    moduleName :
      String

    canonicalReceiptName :
      String

    responsibility :
      String

    componentPositiveBoundary :
      String

    forbiddenPromotion :
      String

open ComponentReceiptRef public

canonicalCoreObjectFibreReceiptRef : ComponentReceiptRef
canonicalCoreObjectFibreReceiptRef =
  record
    { projectionKind =
        projectCoreObjectFibreField
    ; layer =
        coreObjectFibreFieldLayer
    ; moduleName =
        "DASHI.Interop.PNFSpectralFieldCore"
    ; canonicalReceiptName =
        "canonicalPNFSpectralFieldCoreReceipt"
    ; responsibility =
        "Object-level EvidenceSpan/PNF carrier and fibre-field intake surface."
    ; componentPositiveBoundary =
        "Records typed core objects, evidence spans, PNF coordinates, and fibres."
    ; forbiddenPromotion =
        "Does not parse runtime evidence or certify semantic truth."
    }

canonicalResidualWeightedGraphReceiptRef : ComponentReceiptRef
canonicalResidualWeightedGraphReceiptRef =
  record
    { projectionKind =
        projectResidualWeightedGraphLaplacian
    ; layer =
        residualWeightedGraphLaplacianLayer
    ; moduleName =
        "DASHI.Interop.PNFSpectralFieldGraph"
    ; canonicalReceiptName =
        "canonicalPNFSpectralFieldGraphReceipt"
    ; responsibility =
        "Residual graph, meet/join edge, weighting, and Laplacian intake surface."
    ; componentPositiveBoundary =
        "Records residual adjacency and Laplacian-ready architecture over PNF spans."
    ; forbiddenPromotion =
        "Does not prove spectral gap, retrieval quality, or physical utility."
    }

canonicalBraidTransportReceiptRef : ComponentReceiptRef
canonicalBraidTransportReceiptRef =
  record
    { projectionKind =
        projectBraidTransport
    ; layer =
        braidTransportLayer
    ; moduleName =
        "DASHI.Interop.PNFBraidTransportField"
    ; canonicalReceiptName =
        "canonicalPNFBraidTransportFieldReceipt"
    ; responsibility =
        "Braid transport between fibres and residual graph paths."
    ; componentPositiveBoundary =
        "Records transport architecture for braid-carry movement across fibres."
    ; forbiddenPromotion =
        "Does not assert physical braid dynamics or analytic transport estimates."
    }

canonicalSpectralVectorIndexReceiptRef : ComponentReceiptRef
canonicalSpectralVectorIndexReceiptRef =
  record
    { projectionKind =
        projectSpectralVectorIndexResolverSelector
    ; layer =
        spectralVectorIndexResolverSelectorLayer
    ; moduleName =
        "DASHI.Interop.PNFSpectralVectorIndex"
    ; canonicalReceiptName =
        "canonicalPNFSpectralVectorIndexReceipt"
    ; responsibility =
        "Spectral coordinates, vector index over references, resolver, and selector."
    ; componentPositiveBoundary =
        "Records typed reference-index architecture for selection after validation."
    ; forbiddenPromotion =
        "Does not implement ANN search, truth ranking, trading advice, or answer authority."
    }

canonicalComponentReceipts : List ComponentReceiptRef
canonicalComponentReceipts =
  canonicalCoreObjectFibreReceiptRef
  ∷ canonicalResidualWeightedGraphReceiptRef
  ∷ canonicalBraidTransportReceiptRef
  ∷ canonicalSpectralVectorIndexReceiptRef
  ∷ []

record PipelineReceipt : Set where
  field
    pipelineName :
      String

    stages :
      List PipelineStage

    cleanPipelineStatement :
      String

    firstStage :
      PipelineStage

    finalStage :
      PipelineStage

    validationBoundary :
      String

open PipelineReceipt public

canonicalPipelineReceipt : PipelineReceipt
canonicalPipelineReceipt =
  record
    { pipelineName =
        "PNF spectral field intake-to-answer pipeline"
    ; stages =
        canonicalPipeline
    ; cleanPipelineStatement =
        "raw evidence -> EvidenceSpan/PNF -> residual/meet/join graph -> fibres -> braids -> spectral coordinates -> vector index over refs -> resolver/selector -> ITIR validation -> support packet/answer/signal"
    ; firstStage =
        rawEvidenceStage
    ; finalStage =
        supportPacketAnswerSignalStage
    ; validationBoundary =
        "ITIR validation is a downstream gate before support-packet, answer, or signal use."
    }

record GovernanceReceipt : Set where
  field
    governanceName :
      String

    boundaries :
      List GovernanceBoundary

    architectureOnly :
      Bool

    noRuntimeParser :
      Bool

    noANNBackend :
      Bool

    noProofOfSpectralUtility :
      Bool

    noSemanticTruth :
      Bool

    noTradingTruth :
      Bool

    architectureOnlyIsTrue :
      architectureOnly ≡ true

    noRuntimeParserIsTrue :
      noRuntimeParser ≡ true

    noANNBackendIsTrue :
      noANNBackend ≡ true

    noProofOfSpectralUtilityIsTrue :
      noProofOfSpectralUtility ≡ true

    noSemanticTruthIsTrue :
      noSemanticTruth ≡ true

    noTradingTruthIsTrue :
      noTradingTruth ≡ true

open GovernanceReceipt public

canonicalGovernanceReceipt : GovernanceReceipt
canonicalGovernanceReceipt =
  record
    { governanceName =
        "PNF spectral field normalized governance"
    ; boundaries =
        canonicalGovernanceBoundaries
    ; architectureOnly =
        true
    ; noRuntimeParser =
        true
    ; noANNBackend =
        true
    ; noProofOfSpectralUtility =
        true
    ; noSemanticTruth =
        true
    ; noTradingTruth =
        true
    ; architectureOnlyIsTrue =
        refl
    ; noRuntimeParserIsTrue =
        refl
    ; noANNBackendIsTrue =
        refl
    ; noProofOfSpectralUtilityIsTrue =
        refl
    ; noSemanticTruthIsTrue =
        refl
    ; noTradingTruthIsTrue =
        refl
    }

record PNFSpectralFieldArchitectureReceipt : Set where
  field
    status :
      ArchitectureReceiptStatus

    receiptName :
      String

    layerCount :
      Nat

    layers :
      List ArchitectureLayer

    componentReceipts :
      List ComponentReceiptRef

    coreObjectFibreComponent :
      ComponentReceiptRef

    residualWeightedGraphComponent :
      ComponentReceiptRef

    braidTransportComponent :
      ComponentReceiptRef

    spectralVectorIndexComponent :
      ComponentReceiptRef

    pipelineReceipt :
      PipelineReceipt

    governanceReceipt :
      GovernanceReceipt

    intakeSummary :
      String

    architecturePositiveBoundary :
      String

    falsePromotionGuards :
      String

    validationOwner :
      String

    promotesRuntimeParser :
      Bool

    promotesANNBackend :
      Bool

    provesSpectralUtility :
      Bool

    promotesSemanticTruth :
      Bool

    promotesTradingTruth :
      Bool

    promotesRuntimeParserIsFalse :
      promotesRuntimeParser ≡ false

    promotesANNBackendIsFalse :
      promotesANNBackend ≡ false

    provesSpectralUtilityIsFalse :
      provesSpectralUtility ≡ false

    promotesSemanticTruthIsFalse :
      promotesSemanticTruth ≡ false

    promotesTradingTruthIsFalse :
      promotesTradingTruth ≡ false

open PNFSpectralFieldArchitectureReceipt public

canonicalPNFSpectralFieldArchitectureReceipt :
  PNFSpectralFieldArchitectureReceipt
canonicalPNFSpectralFieldArchitectureReceipt =
  record
    { status =
        pnfSpectralFieldArchitectureRecorded_intakeOnly
    ; receiptName =
        "canonicalPNFSpectralFieldArchitectureReceipt"
    ; layerCount =
        4
    ; layers =
        canonicalArchitectureLayers
    ; componentReceipts =
        canonicalComponentReceipts
    ; coreObjectFibreComponent =
        canonicalCoreObjectFibreReceiptRef
    ; residualWeightedGraphComponent =
        canonicalResidualWeightedGraphReceiptRef
    ; braidTransportComponent =
        canonicalBraidTransportReceiptRef
    ; spectralVectorIndexComponent =
        canonicalSpectralVectorIndexReceiptRef
    ; pipelineReceipt =
        canonicalPipelineReceipt
    ; governanceReceipt =
        canonicalGovernanceReceipt
    ; intakeSummary =
        "Aggregates PNF core/fibre field, residual graph/Laplacian, braid transport, and spectral vector index/resolver/selector into one architecture receipt."
    ; architecturePositiveBoundary =
        "Architecture and intake receipt only; downstream validation must occur before support packet, answer, or signal use."
    ; falsePromotionGuards =
        "No runtime parser, no ANN backend, no proof of spectral utility, no semantic truth, and no trading truth are promoted here."
    ; validationOwner =
        "Main validation lane / ITIR gate"
    ; promotesRuntimeParser =
        false
    ; promotesANNBackend =
        false
    ; provesSpectralUtility =
        false
    ; promotesSemanticTruth =
        false
    ; promotesTradingTruth =
        false
    ; promotesRuntimeParserIsFalse =
        refl
    ; promotesANNBackendIsFalse =
        refl
    ; provesSpectralUtilityIsFalse =
        refl
    ; promotesSemanticTruthIsFalse =
        refl
    ; promotesTradingTruthIsFalse =
        refl
    }

------------------------------------------------------------------------
-- Named projections to component receipts.

projectCoreObjectFibreComponentReceipt :
  PNFSpectralFieldArchitectureReceipt → ComponentReceiptRef
projectCoreObjectFibreComponentReceipt receipt =
  coreObjectFibreComponent receipt

projectResidualWeightedGraphComponentReceipt :
  PNFSpectralFieldArchitectureReceipt → ComponentReceiptRef
projectResidualWeightedGraphComponentReceipt receipt =
  residualWeightedGraphComponent receipt

projectBraidTransportComponentReceipt :
  PNFSpectralFieldArchitectureReceipt → ComponentReceiptRef
projectBraidTransportComponentReceipt receipt =
  braidTransportComponent receipt

projectSpectralVectorIndexComponentReceipt :
  PNFSpectralFieldArchitectureReceipt → ComponentReceiptRef
projectSpectralVectorIndexComponentReceipt receipt =
  spectralVectorIndexComponent receipt

canonicalCoreObjectFibreComponentReceipt : ComponentReceiptRef
canonicalCoreObjectFibreComponentReceipt =
  projectCoreObjectFibreComponentReceipt
    canonicalPNFSpectralFieldArchitectureReceipt

canonicalResidualWeightedGraphComponentReceipt : ComponentReceiptRef
canonicalResidualWeightedGraphComponentReceipt =
  projectResidualWeightedGraphComponentReceipt
    canonicalPNFSpectralFieldArchitectureReceipt

canonicalBraidTransportComponentReceipt : ComponentReceiptRef
canonicalBraidTransportComponentReceipt =
  projectBraidTransportComponentReceipt
    canonicalPNFSpectralFieldArchitectureReceipt

canonicalSpectralVectorIndexComponentReceipt : ComponentReceiptRef
canonicalSpectralVectorIndexComponentReceipt =
  projectSpectralVectorIndexComponentReceipt
    canonicalPNFSpectralFieldArchitectureReceipt

canonicalArchitecturePipelineProjection : PipelineReceipt
canonicalArchitecturePipelineProjection =
  pipelineReceipt canonicalPNFSpectralFieldArchitectureReceipt

canonicalArchitectureGovernanceProjection : GovernanceReceipt
canonicalArchitectureGovernanceProjection =
  governanceReceipt canonicalPNFSpectralFieldArchitectureReceipt
