{-# OPTIONS --safe #-}
module DASHI.Interop.SLRPNFToAgdaPreflightProofJoinPipelineExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _<_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Cognition.PNF.EventAlgebra as Event
import DASHI.Cognition.PNF.CandidateInvalidation as Invalidation
import DASHI.Cognition.Utterance.AdmissibilityGate as Admissibility
import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Interop.PNFResidualConsumerNextObligation as Consumer
import Ontology.Hecke.PNFResidualBridge as HeckeBridge
import Ontology.Hecke.QuotientRepresentation as Quotient
import DASHI.Interop.PNFSpectralFieldCore as SpectralCore
import DASHI.Interop.PNFSpectralFieldGraph as SpectralGraph
import DASHI.Interop.PNFSpectralCoordinateRebuildability as Rebuild
import DASHI.Interop.PNFSpectralNumericABICore as SpectralABI
import DASHI.Interop.SLRProtectedPNFFleetReductionExact as FleetReduction
import DASHI.Interop.ITIRMCPFullRegistryCoverageExact as Registry
import DASHI.Interop.SLRFullWorkspaceCrateCoverageExact as Crates
import DASHI.Interop.SLRStructuralReceiptFirewallExact as Firewall

canonicalR1SlotPartition : FleetReduction.SlotPartition
canonicalR1SlotPartition =
  FleetReduction.slotPartition 294671 11611 12929 319211 refl

invalidatedPNFCannotEnterAdmittedFrames :
  (r : Invalidation.PNFInvalidationReceipt) →
  Event.validity (Invalidation.invalidatedCandidate r) ≡ Event.admissible → ⊥
invalidatedPNFCannotEnterAdmittedFrames = Invalidation.invalidatedCannotBeAdmitted

record AdmittedPNFFramePair : Set where
  constructor admittedPNFFramePair
  field
    leftCandidate : Event.CandidatePNF
    rightCandidate : Event.CandidatePNF
    leftIsAdmitted : Event.validity leftCandidate ≡ Event.admissible
    rightIsAdmitted : Event.validity rightCandidate ≡ Event.admissible
    leftEmissionReceipt : Residual.PNFEmissionReceipt
    rightEmissionReceipt : Residual.PNFEmissionReceipt

record StageR2HeckeFibreQuotientSummary : Set where
  constructor stageR2HeckeFibreQuotientSummary
  field
    rawCandidateCount : Nat
    admittedFrameCount : Nat
    uniqueHeckeFibreCount : Nat
    retainedFibreCount : Nat
    eliminatedCandidateCount : Nat
    totalConservationExact : rawCandidateCount ≡ eliminatedCandidateCount + retainedFibreCount
    admittedSplitExact : admittedFrameCount ≡ 3640 + uniqueHeckeFibreCount
    uniqueToRetainedSplitExact : uniqueHeckeFibreCount ≡ 7358 + retainedFibreCount

canonicalStageR2HeckeQuotient : StageR2HeckeFibreQuotientSummary
canonicalStageR2HeckeQuotient =
  stageR2HeckeFibreQuotientSummary 319211 12929 9289 1931 317280 refl refl refl

sameHeckePoolSharesFibreRepresentative :
  ∀ {S Class : Set}
  (q : Quotient.QuotientInterfaceOn S Class)
  (x y : S) →
  HeckeBridge.SameHeckeCandidatePool q x y →
  Quotient.QuotientInterfaceOn.proj q x ≡ Quotient.QuotientInterfaceOn.proj q y
sameHeckePoolSharesFibreRepresentative _ _ _ samePool = samePool

record PNFObligationDemand : Set where
  constructor pnfObligationDemand
  field
    demandRef : String
    externalObligationRef : String
    statementDigest : String
    leftEmissionReceipt : Residual.PNFEmissionReceipt
    rightEmissionReceipt : Residual.PNFEmissionReceipt
    residualLevel : Residual.ResidualLevel
    residualComesFromReceiptComputation :
      residualLevel ≡ Residual.receiptResidual leftEmissionReceipt rightEmissionReceipt
    protection : FleetReduction.Protection String

buildPNFObligationDemandFromReceipts :
  (demandRef externalObligationRef statementDigest : String) →
  (leftReceipt rightReceipt : Residual.PNFEmissionReceipt) →
  (protection : FleetReduction.Protection String) →
  PNFObligationDemand
buildPNFObligationDemandFromReceipts
  demandRef externalObligationRef statementDigest leftReceipt rightReceipt protection =
  pnfObligationDemand demandRef externalObligationRef statementDigest
    leftReceipt rightReceipt (Residual.receiptResidual leftReceipt rightReceipt)
    refl protection

record StageR3LifecycleSummary : Set where
  constructor stageR3LifecycleSummary
  field
    evaluatedProposals : Nat
    resolvedUniqueCount : Nat
    blockedConflictCount : Nat
    domainIRCoreKnowledgeRows : Nat
    actionableProjectionDemandRows : Nat
    proposalSplitExact : evaluatedProposals ≡ resolvedUniqueCount + blockedConflictCount

canonicalStageR3Lifecycle : StageR3LifecycleSummary
canonicalStageR3Lifecycle = stageR3LifecycleSummary 622 600 22 1112 221 refl

data MarchenkoPasturBand : Set where
  insideMarchenkoPasturBulk :
    (eigenvalueMicros bulkUpperEdgeMicros : Nat) →
    (eigenvalueMicros < suc bulkUpperEdgeMicros) ≡ true →
    MarchenkoPasturBand
  aboveMarchenkoPasturBulkEdge :
    (eigenvalueMicros bulkUpperEdgeMicros : Nat) →
    (bulkUpperEdgeMicros < eigenvalueMicros) ≡ true →
    MarchenkoPasturBand

data ShrinkageTypedOutcome (A : Set) : Set where
  shrunkSpectralBulkToZero : A → ShrinkageTypedOutcome A
  retainedAsMacroscopicEigenMotif : FleetReduction.Retained A → ShrinkageTypedOutcome A
  retainedByProtectedObligationWitness : FleetReduction.Retained A → ShrinkageTypedOutcome A

record MarchenkoPasturShrinkageSpec : Set where
  constructor marchenkoPasturShrinkageSpec
  field
    threadCountT : Nat
    featureCountN : Nat
    bulkNullDimensions : Nat
    macroscopicEigenMotifDimensions : Nat
    bulkPlusSignalExact : featureCountN ≡ bulkNullDimensions + macroscopicEigenMotifDimensions
    bulkUpperEdgeMicros : Nat
    coordinateRebuildabilityRow : Rebuild.SpectralCoordinateMapRow
    numericABIBinding : SpectralABI.PNFRowMapBinding

canonicalMarchenkoPasturSpec : MarchenkoPasturShrinkageSpec
canonicalMarchenkoPasturSpec =
  marchenkoPasturShrinkageSpec 200 120 117 3 refl 3148495
    Rebuild.canonicalSpectralCoordinateMapRow SpectralABI.canonicalPNFRowMapBinding

applyMarchenkoPasturWithTypedProtection :
  ∀ {A : Set} → MarchenkoPasturBand →
  FleetReduction.Protection A → ShrinkageTypedOutcome A
applyMarchenkoPasturWithTypedProtection (aboveMarchenkoPasturBulkEdge _ _ _) prot =
  retainedAsMacroscopicEigenMotif (FleetReduction.retain prot)
applyMarchenkoPasturWithTypedProtection (insideMarchenkoPasturBulk _ _ _) (FleetReduction.spectral x) =
  shrunkSpectralBulkToZero x
applyMarchenkoPasturWithTypedProtection (insideMarchenkoPasturBulk _ _ _) (FleetReduction.formallyRequired x) =
  retainedByProtectedObligationWitness (FleetReduction.retain (FleetReduction.formallyRequired x))
applyMarchenkoPasturWithTypedProtection (insideMarchenkoPasturBulk _ _ _) (FleetReduction.reviewed x) =
  retainedByProtectedObligationWitness (FleetReduction.retain (FleetReduction.reviewed x))

marchenkoPasturShrinksUnprotectedSpectralBulkToZero :
  ∀ {A : Set} (eig edge : Nat) (inBulk : (eig < suc edge) ≡ true) (x : A) →
  applyMarchenkoPasturWithTypedProtection
    (insideMarchenkoPasturBulk eig edge inBulk) (FleetReduction.spectral x)
  ≡ shrunkSpectralBulkToZero x
marchenkoPasturShrinksUnprotectedSpectralBulkToZero _ _ _ _ = refl

protectedFormalSurvivesMarchenkoPasturBulk :
  ∀ {A : Set} (eig edge : Nat) (inBulk : (eig < suc edge) ≡ true) (x : A) →
  applyMarchenkoPasturWithTypedProtection
    (insideMarchenkoPasturBulk eig edge inBulk) (FleetReduction.formallyRequired x)
  ≡ retainedByProtectedObligationWitness (FleetReduction.retainedFormal x)
protectedFormalSurvivesMarchenkoPasturBulk _ _ _ _ = refl

protectedReviewedSurvivesMarchenkoPasturBulk :
  ∀ {A : Set} (eig edge : Nat) (inBulk : (eig < suc edge) ≡ true) (x : A) →
  applyMarchenkoPasturWithTypedProtection
    (insideMarchenkoPasturBulk eig edge inBulk) (FleetReduction.reviewed x)
  ≡ retainedByProtectedObligationWitness (FleetReduction.retainedReviewed x)
protectedReviewedSurvivesMarchenkoPasturBulk _ _ _ _ = refl

marchenkoPasturCannotDropFormalSingleton :
  ∀ {A : Set} (eig edge : Nat) (inBulk : (eig < suc edge) ≡ true) (x y : A) →
  applyMarchenkoPasturWithTypedProtection
    (insideMarchenkoPasturBulk eig edge inBulk) (FleetReduction.formallyRequired x)
  ≡ shrunkSpectralBulkToZero y → ⊥
marchenkoPasturCannotDropFormalSingleton _ _ _ _ _ ()

data DashiAgdaPreflightOp : Set where
  opDiagnose : DashiAgdaPreflightOp
  opNextError : DashiAgdaPreflightOp
  opApplyFix : DashiAgdaPreflightOp
  opAffected : DashiAgdaPreflightOp
  opRefresh : DashiAgdaPreflightOp
  opCacheStatus : DashiAgdaPreflightOp
  opSemanticStatus : DashiAgdaPreflightOp
  opPromote : DashiAgdaPreflightOp
  opPromotionHistory : DashiAgdaPreflightOp
  opSymbolSearch : DashiAgdaPreflightOp
  opRelatedSymbols : DashiAgdaPreflightOp
  opObjectDetail : DashiAgdaPreflightOp
  opDiscover : DashiAgdaPreflightOp
  opRoundLineage : DashiAgdaPreflightOp
  opNarrativeArchaeology : DashiAgdaPreflightOp
  opNarrativeHistory : DashiAgdaPreflightOp
  opNarrativeFrontier : DashiAgdaPreflightOp
  opNarrativeStale : DashiAgdaPreflightOp
  opNarrativeExplain : DashiAgdaPreflightOp
  opProofRoute : DashiAgdaPreflightOp
  opProofRouteForObligation : DashiAgdaPreflightOp
  opFormalEvidenceForObligation : DashiAgdaPreflightOp
  opProofRouteHistory : DashiAgdaPreflightOp
  opDa51Resolve : DashiAgdaPreflightOp
  opDa51Evidence : DashiAgdaPreflightOp
  opDa51Frontier : DashiAgdaPreflightOp

preflightOpToITIRTool : DashiAgdaPreflightOp → Registry.ITIRMCPToolId
preflightOpToITIRTool opDiagnose = Registry.itirFormalInspect
preflightOpToITIRTool opNextError = Registry.itirFormalInspect
preflightOpToITIRTool opApplyFix = Registry.itirFormalRefine
preflightOpToITIRTool opAffected = Registry.itirFormalInspect
preflightOpToITIRTool opRefresh = Registry.itirFormalInspect
preflightOpToITIRTool opCacheStatus = Registry.itirFormalInspect
preflightOpToITIRTool opSemanticStatus = Registry.itirFormalInspect
preflightOpToITIRTool opPromote = Registry.itirFormalCertify
preflightOpToITIRTool opPromotionHistory = Registry.itirFormalInspect
preflightOpToITIRTool opSymbolSearch = Registry.itirFormalInspect
preflightOpToITIRTool opRelatedSymbols = Registry.itirFormalInspect
preflightOpToITIRTool opObjectDetail = Registry.itirFormalInspect
preflightOpToITIRTool opDiscover = Registry.itirFormalInspect
preflightOpToITIRTool opRoundLineage = Registry.itirFormalInspect
preflightOpToITIRTool opNarrativeArchaeology = Registry.itirFormalInspect
preflightOpToITIRTool opNarrativeHistory = Registry.itirFormalInspect
preflightOpToITIRTool opNarrativeFrontier = Registry.itirFormalInspect
preflightOpToITIRTool opNarrativeStale = Registry.itirFormalInspect
preflightOpToITIRTool opNarrativeExplain = Registry.itirFormalInspect
preflightOpToITIRTool opProofRoute = Registry.itirFormalRoute
preflightOpToITIRTool opProofRouteForObligation = Registry.itirFormalRoute
preflightOpToITIRTool opFormalEvidenceForObligation = Registry.itirFormalRoute
preflightOpToITIRTool opProofRouteHistory = Registry.itirFormalRoute
preflightOpToITIRTool opDa51Resolve = Registry.itirFormalRoute
preflightOpToITIRTool opDa51Evidence = Registry.itirFormalRoute
preflightOpToITIRTool opDa51Frontier = Registry.itirFormalRoute

record AgdaSymbolSearchReceipt : Set where
  constructor agdaSymbolSearchReceipt
  field
    queryText : String
    includeHistory : Bool
    roundSnapshotNoiseHidden : Bool
    historyExclusionLaw : includeHistory ≡ false → roundSnapshotNoiseHidden ≡ true
    resolvedModule : String
    resolvedSymbolId : String

defaultSearchHidesRoundSnapshotNoise :
  (r : AgdaSymbolSearchReceipt) →
  AgdaSymbolSearchReceipt.includeHistory r ≡ false →
  AgdaSymbolSearchReceipt.roundSnapshotNoiseHidden r ≡ true
defaultSearchHidesRoundSnapshotNoise r noHist =
  AgdaSymbolSearchReceipt.historyExclusionLaw r noHist

data SimilarityKind : Set where
  exactSymbolMatch : SimilarityKind
  signatureEquivalentMatch : SimilarityKind
  structurallySimilarMatch : SimilarityKind

record AgdaObjectDetailReceipt : Set where
  constructor agdaObjectDetailReceipt
  field
    symbolId : String
    moduleName : String
    similarityKind : SimilarityKind
    sourceDigest : String
    requiredImports : List String
    hasPostulates : Bool
    hasUnsolvedMetas : Bool
    safePragmaVerified : Bool
    goldenSafeLaw : hasPostulates ≡ false

record ObligationRouteBinding (demand : PNFObligationDemand) : Set where
  constructor obligationRouteBinding
  field
    routedSymbolId : String
    da51Address : String
    boundDemandRef : String
    boundExternalObligationRef : String
    boundStatementDigest : String
    demandRefMatches : boundDemandRef ≡ PNFObligationDemand.demandRef demand
    externalObligationMatches :
      boundExternalObligationRef ≡ PNFObligationDemand.externalObligationRef demand
    statementDigestMatches :
      boundStatementDigest ≡ PNFObligationDemand.statementDigest demand
    backingCrate : Crates.SLRCrateId
    backingCrateIsFormalBridge : backingCrate ≡ Crates.slFormalProofBridge

record PreflightDiagnosticsReceipt : Set where
  constructor preflightDiagnosticsReceipt
  field
    targetModule : String
    errorCount : Nat
    reverseImportAffectedScoped : Bool
    zeroErrors : errorCount ≡ zero

record FormalProofJoin
    (demand : PNFObligationDemand)
    (search : AgdaSymbolSearchReceipt)
    (detail : AgdaObjectDetailReceipt)
    (route : ObligationRouteBinding demand)
    (diag : PreflightDiagnosticsReceipt) : Set where
  constructor formalProofJoin
  field
    demandIsNoTypedMeet :
      Residual.receiptResidual
        (PNFObligationDemand.leftEmissionReceipt demand)
        (PNFObligationDemand.rightEmissionReceipt demand)
      ≡ Residual.noTypedMeet
    roundNoiseFiltered :
      AgdaSymbolSearchReceipt.roundSnapshotNoiseHidden search ≡ true
    searchMatchesDetail :
      AgdaSymbolSearchReceipt.resolvedSymbolId search ≡ AgdaObjectDetailReceipt.symbolId detail
    detailMatchesRoute :
      AgdaObjectDetailReceipt.symbolId detail ≡ ObligationRouteBinding.routedSymbolId route
    detailIsGoldenSafe : AgdaObjectDetailReceipt.safePragmaVerified detail ≡ true
    crossDomainJoinReceipt :
      Firewall.CrossDomainJoinAdmissible (Firewall.crossDomainJoinReceipt true true)
    routingReceipt :
      Firewall.RoutingAdmissible (Firewall.routingReceipt Firewall.pgPNFCostedParetoConductor)

roundNoiseBlocksFormalProofJoin :
  ∀ {demand search detail route diag} →
  AgdaSymbolSearchReceipt.roundSnapshotNoiseHidden search ≡ false →
  FormalProofJoin demand search detail route diag → ⊥
roundNoiseBlocksFormalProofJoin noiseFalse join
  with FormalProofJoin.roundNoiseFiltered join
... | noiseTrue rewrite noiseFalse with noiseTrue
... | ()

record EndToEndPNFToAgdaProofJoinPipeline
    {S Class : Set}
    (quotient : Quotient.QuotientInterfaceOn S Class)
    (leftState rightState : S) : Set where
  constructor endToEndPNFToAgdaProofJoinPipeline
  field
    stageR1AdmittedPair : AdmittedPNFFramePair
    stageR2SameHeckePool : HeckeBridge.SameHeckeCandidatePool quotient leftState rightState
    stageR3Demand : PNFObligationDemand
    stageR3LeftReceiptMatchesR1 :
      PNFObligationDemand.leftEmissionReceipt stageR3Demand
      ≡ AdmittedPNFFramePair.leftEmissionReceipt stageR1AdmittedPair
    stageR3RightReceiptMatchesR1 :
      PNFObligationDemand.rightEmissionReceipt stageR3Demand
      ≡ AdmittedPNFFramePair.rightEmissionReceipt stageR1AdmittedPair
    stageR4Band : MarchenkoPasturBand
    stageR4RetainedWitness : FleetReduction.Retained String
    stageR4ProtectedSurvivability :
      applyMarchenkoPasturWithTypedProtection
        stageR4Band (PNFObligationDemand.protection stageR3Demand)
      ≡ retainedByProtectedObligationWitness stageR4RetainedWitness
    stageR5Search : AgdaSymbolSearchReceipt
    stageR5Detail : AgdaObjectDetailReceipt
    stageR5Route : ObligationRouteBinding stageR3Demand
    stageR5Diagnostics : PreflightDiagnosticsReceipt
    stageR5Join :
      FormalProofJoin stageR3Demand stageR5Search stageR5Detail stageR5Route stageR5Diagnostics

record StageR5FormalSubtractionSummary : Set where
  constructor stageR5FormalSubtractionSummary
  field
    dischargedCoreKnowledgeFibres : Nat
    polarityContradictionGaps : Nat
    unformalisedFormalGaps : Nat
    totalEvaluatedFrontierFibres : Nat
    frontierPartitionExact :
      totalEvaluatedFrontierFibres ≡
        dischargedCoreKnowledgeFibres + (polarityContradictionGaps + unformalisedFormalGaps)

canonicalStageR5FormalSubtraction : StageR5FormalSubtractionSummary
canonicalStageR5FormalSubtraction = stageR5FormalSubtractionSummary 584 44 58 686 refl
