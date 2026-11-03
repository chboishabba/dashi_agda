{-# OPTIONS --safe #-}
module DASHI.Interop.SLRPNFToAgdaPreflightProofJoinPipelineExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Cognition.PNF.EventAlgebra as Event
import DASHI.Cognition.PNF.CandidateInvalidation as Invalidation
import DASHI.Cognition.Utterance.AdmissibilityGate as Admissibility
import DASHI.Interop.SensibLawResidualLattice as Residual
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
    residualLevel : Residual.ResidualLevel
    protection : FleetReduction.Protection String

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
  insideMarchenkoPasturBulk : MarchenkoPasturBand
  aboveMarchenkoPasturBulkEdge : MarchenkoPasturBand

data ShrinkageOutcome : Set where
  shrunkToBulkZero : ShrinkageOutcome
  retainedAsMacroscopicEigenMotif : ShrinkageOutcome
  retainedByProtectedObligationWitness : ShrinkageOutcome

record MarchenkoPasturShrinkageSpec : Set where
  constructor marchenkoPasturShrinkageSpec
  field
    threadCountT : Nat
    featureCountN : Nat
    bulkNullDimensions : Nat
    macroscopicEigenMotifDimensions : Nat
    bulkPlusSignalExact : featureCountN ≡ bulkNullDimensions + macroscopicEigenMotifDimensions
    coordinateRebuildabilityRow : Rebuild.SpectralCoordinateMapRow
    numericABIBinding : SpectralABI.PNFRowMapBinding

canonicalMarchenkoPasturSpec : MarchenkoPasturShrinkageSpec
canonicalMarchenkoPasturSpec =
  marchenkoPasturShrinkageSpec 200 120 117 3 refl
    Rebuild.canonicalSpectralCoordinateMapRow SpectralABI.canonicalPNFRowMapBinding

applyMarchenkoPasturWithProtection : MarchenkoPasturBand → Bool → ShrinkageOutcome
applyMarchenkoPasturWithProtection aboveMarchenkoPasturBulkEdge _ =
  retainedAsMacroscopicEigenMotif
applyMarchenkoPasturWithProtection insideMarchenkoPasturBulk true =
  retainedByProtectedObligationWitness
applyMarchenkoPasturWithProtection insideMarchenkoPasturBulk false =
  shrunkToBulkZero

marchenkoPasturShrinksUnprotectedBulkToZero :
  applyMarchenkoPasturWithProtection insideMarchenkoPasturBulk false ≡ shrunkToBulkZero
marchenkoPasturShrinksUnprotectedBulkToZero = refl

protectedFormalOrReviewedSurvivesMarchenkoPasturBulk :
  applyMarchenkoPasturWithProtection insideMarchenkoPasturBulk true ≡ retainedByProtectedObligationWitness
protectedFormalOrReviewedSurvivesMarchenkoPasturBulk = refl

marchenkoPasturCannotDropProtectedSingleton :
  applyMarchenkoPasturWithProtection insideMarchenkoPasturBulk true ≡ shrunkToBulkZero → ⊥
marchenkoPasturCannotDropProtectedSingleton ()

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
      PNFObligationDemand.residualLevel demand ≡ Residual.noTypedMeet
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
