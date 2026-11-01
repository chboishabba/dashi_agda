module DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Obligations where

open import Agda.Builtin.String using (String)

open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Core
open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Methods
open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Benchmark

record SphericalRectangleObligations
    (run : CompetitorRunReceipt) : Set₁ where
  field
    closedFormOrSampledMap : Set
    jacobianOrAreaMetric : Set
    seamLedger : Set
    poleOrFoldBoundary : Set

record ScientificGridObligations
    (run : CompetitorRunReceipt) : Set₁ where
  field
    cellAreaWitness : Set
    neighbourGraphWitness : Set
    hierarchyWitness : Set
    rectangleExportBoundary : Set

record SpectralBasisObligations
    (run : CompetitorRunReceipt) : Set₁ where
  field
    basisWitness : Set
    coefficientProjection : Set
    reconstructionMetric : Set
    discontinuityBoundary : Set

record MeshParameterizerObligations
    (run : CompetitorRunReceipt) : Set₁ where
  field
    diskOrChartWitness : Set
    foldoverMetric : Set
    distortionEnergy : Set
    boundaryPolicy : Set

record SeamCutOptimizerObligations
    (run : CompetitorRunReceipt) : Set₁ where
  field
    seamSetWitness : Set
    parameterizationWitness : Set
    seamDistortionTradeoff : Set
    manufacturableExtractionBoundary : Set

record BlackBoxToolObligations
    (run : CompetitorRunReceipt) : Set₁ where
  field
    toolVersion : String
    settingsHash : String
    measuredOnly : Set
    noInternalProof : Set

record BodyCorrespondenceObligations
    (run : CompetitorRunReceipt) : Set₁ where
  field
    partLabels : Set
    surfaceCorrespondence : Set
    manufacturingBoundary : Set

record LearnedProposalObligations
    (run : CompetitorRunReceipt) : Set₁ where
  field
    modelHash : String
    predictedOutput : Set
    evaluatorRun : CompetitorRunReceipt
    proposalOnly : Set

record BT369Obligations
    (run : CompetitorRunReceipt) : Set₁ where
  field
    tritCarrier : Set
    orientation6 : Set
    neighbourhood9 : Set
    ternaryPrefix : Set
    mdlStopRule : Set
    braidLedger : Set
    declaredBenchmarkWin : Set

ObligationsFor : CompetitorRunReceipt → Set₁
ObligationsFor run with methodFamily (kind (method run))
... | sphericalRectangleExport = SphericalRectangleObligations run
... | sphericalScientificGrid = ScientificGridObligations run
... | spectralBasis = SpectralBasisObligations run
... | meshParameterizer = MeshParameterizerObligations run
... | seamAndCutOptimizer = SeamCutOptimizerObligations run
... | blackBoxArtistTool = BlackBoxToolObligations run
... | bodyCorrespondenceAtlas = BodyCorrespondenceObligations run
... | learnedProposal = LearnedProposalObligations run
... | dashiNativeAtlas = BT369Obligations run
