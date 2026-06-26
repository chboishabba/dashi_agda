module DASHI.Interop.PolarityBettiSupportBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.AuthorityNonPromotionCore as AuthorityNA
import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Interop.PNFHodgeResidualTopology as PNFTopology
import DASHI.Interop.PolarityPhaseFieldBridge as PhaseField

------------------------------------------------------------------------
-- Candidate-only Betti boundary over local polarity / phase support.
--
-- This module stays finite and theorem-thin.  It does not compute homology;
-- it records local beta-0 / beta-1 / beta-2 style summary rows over the
-- existing polarity / phase support geometry and supervoxel surfaces.  The
-- topology references are receipt-only, blocked-authority diagnostics.

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

data BettiSummaryKind : Set where
  beta0Summary : BettiSummaryKind
  beta1Summary : BettiSummaryKind
  beta2Summary : BettiSummaryKind

bettiSummaryIndex : BettiSummaryKind → Nat
bettiSummaryIndex beta0Summary = zero
bettiSummaryIndex beta1Summary = suc zero
bettiSummaryIndex beta2Summary = suc (suc zero)

bettiSummaryBoundaryTag :
  BettiSummaryKind →
  PNFTopology.BoundaryMapShapeTag
bettiSummaryBoundaryTag beta0Summary = PNFTopology.d0
bettiSummaryBoundaryTag beta1Summary = PNFTopology.d1
bettiSummaryBoundaryTag beta2Summary = PNFTopology.d1

bettiSummaryLaplacianTag :
  BettiSummaryKind →
  PNFTopology.HodgeLaplacianTag
bettiSummaryLaplacianTag beta0Summary = PNFTopology.Δ0
bettiSummaryLaplacianTag beta1Summary = PNFTopology.Δ1
bettiSummaryLaplacianTag beta2Summary = PNFTopology.Δ2

data BettiSupportSurface : Set where
  supportGeometrySurface : BettiSupportSurface
  supervoxelSurface : BettiSupportSurface
  mixedLocalSurface : BettiSupportSurface

record BettiSupportRow : Set where
  constructor mkBettiSupportRow
  field
    rowLabel :
      String

    rowSummaryKind :
      BettiSummaryKind

    rowIndex :
      Nat

    rowIndexMatches :
      rowIndex ≡ bettiSummaryIndex rowSummaryKind

    rowSupportSurface :
      BettiSupportSurface

    rowSupportGeometry :
      PhaseField.SupportGeometry

    rowSupportSupervoxel :
      PhaseField.Supervoxel

    rowSupportWave :
      PhaseField.WaveCandidateMixture

    rowLocalScale :
      Nat

    rowLocalScaleMatches :
      rowLocalScale ≡
      PhaseField.supportScale rowSupportGeometry

    rowBoundaryShape :
      PNFTopology.BoundaryMapShape

    rowBoundaryShapeTagMatches :
      PNFTopology.boundaryTag rowBoundaryShape ≡
      bettiSummaryBoundaryTag rowSummaryKind

    rowLaplacianTag :
      PNFTopology.HodgeLaplacianTag

    rowLaplacianTagMatches :
      rowLaplacianTag ≡ bettiSummaryLaplacianTag rowSummaryKind

    rowBoundaryLayer :
      PNFTopology.HodgeLaplacianBoundaryLayer

    rowBoundaryLayerMatches :
      rowBoundaryLayer ≡
      PNFTopology.laplacianBoundaryLayer rowLaplacianTag

    rowComponentCount :
      Nat

    rowCycleCount :
      Nat

    rowVoidCount :
      Nat

    rowResidualTopologyReceiptOnly :
      Bool

    rowResidualTopologyReceiptOnlyIsTrue :
      rowResidualTopologyReceiptOnly ≡ true

    rowCandidateOnly :
      Bool

    rowPromoted :
      Bool

    rowCandidateOnlyIsTrue :
      rowCandidateOnly ≡ true

    rowPromotedIsFalse :
      rowPromoted ≡ false

open BettiSupportRow public

canonicalBeta0Row : BettiSupportRow
canonicalBeta0Row =
  mkBettiSupportRow
    "beta-0-local-components"
    beta0Summary
    zero
    refl
    supportGeometrySurface
    PhaseField.canonicalBalancedSupportGeometry
    PhaseField.canonicalBalancedSupervoxel
    PhaseField.canonicalStandingWave
    (suc (suc zero))
    refl
    PNFTopology.d0BoundaryShape
    refl
    PNFTopology.Δ0
    refl
    PNFTopology.signedGraphLaplacian0Implementable
    refl
    (suc zero)
    zero
    zero
    true
    refl
    true
    false
    refl
    refl

canonicalBeta1Row : BettiSupportRow
canonicalBeta1Row =
  mkBettiSupportRow
    "beta-1-local-loops"
    beta1Summary
    (suc zero)
    refl
    mixedLocalSurface
    PhaseField.canonicalYinSupportGeometry
    PhaseField.canonicalYinYangSupervoxel
    PhaseField.canonicalYinYangWave
    (suc zero)
    refl
    PNFTopology.d1BoundaryShape
    refl
    PNFTopology.Δ1
    refl
    PNFTopology.hodgeLaplacian1DiagnosticOnly
    refl
    (suc zero)
    (suc zero)
    zero
    true
    refl
    true
    false
    refl
    refl

canonicalBeta2Row : BettiSupportRow
canonicalBeta2Row =
  mkBettiSupportRow
    "beta-2-local-cavities"
    beta2Summary
    (suc (suc zero))
    refl
    supervoxelSurface
    PhaseField.canonicalYangSupportGeometry
    PhaseField.canonicalBalancedSupervoxel
    PhaseField.canonicalCounterWave
    (suc zero)
    refl
    PNFTopology.d1BoundaryShape
    refl
    PNFTopology.Δ2
    refl
    PNFTopology.hodgeLaplacian2DiagnosticOnly
    refl
    (suc zero)
    zero
    (suc zero)
    true
    refl
    true
    false
    refl
    refl

canonicalBettiRows : List BettiSupportRow
canonicalBettiRows =
  canonicalBeta0Row
  ∷ canonicalBeta1Row
  ∷ canonicalBeta2Row
  ∷ []

canonicalBettiRowCount : Nat
canonicalBettiRowCount =
  listCount canonicalBettiRows

canonicalBettiRowCountIs3 :
  canonicalBettiRowCount ≡ 3
canonicalBettiRowCountIs3 = refl

beta0HasNoLocalCycles :
  rowCycleCount canonicalBeta0Row ≡ zero
beta0HasNoLocalCycles = refl

beta0HasNoLocalVoids :
  rowVoidCount canonicalBeta0Row ≡ zero
beta0HasNoLocalVoids = refl

beta1HasOneLocalLoop :
  rowCycleCount canonicalBeta1Row ≡ suc zero
beta1HasOneLocalLoop = refl

beta1BoundaryTagIsd1 :
  PNFTopology.boundaryTag (rowBoundaryShape canonicalBeta1Row) ≡ PNFTopology.d1
beta1BoundaryTagIsd1 = refl

beta2HasOneLocalVoid :
  rowVoidCount canonicalBeta2Row ≡ suc zero
beta2HasOneLocalVoid = refl

beta2LaplacianIsΔ2 :
  rowLaplacianTag canonicalBeta2Row ≡ PNFTopology.Δ2
beta2LaplacianIsΔ2 = refl

allCanonicalRowsAreReceiptOnly :
  rowResidualTopologyReceiptOnly canonicalBeta0Row ≡ true
allCanonicalRowsAreReceiptOnly = refl

------------------------------------------------------------------------
-- Blocked-authority governance.

bettiCandidateOnlyRow : CandidateOnly.CandidateOnlyRow
bettiCandidateOnlyRow =
  CandidateOnly.mkCandidateOnlyRow
    "polarity-betti-support-boundary"
    "lane-6"
    "DASHI/Interop/PolarityBettiSupportBoundary"
    CandidateOnly.diagnosticCandidateKind
    CandidateOnly.diagnosticCandidateOnlyStatus
    "candidate-only beta-0 / beta-1 / beta-2 summary rows over local support geometry, supervoxels, and wave-localized topology references"
    "blocked authority, no promoted topology theorem, no external runtime or empirical authority"

bettiCandidateOnlyReceipt :
  CandidateOnly.CandidateOnlyReceipt bettiCandidateOnlyRow
bettiCandidateOnlyReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    bettiCandidateOnlyRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

bettiBlockedAuthorityKinds : List AuthorityNA.AuthorityKind
bettiBlockedAuthorityKinds =
  AuthorityNA.canonicalAuthorityKinds

record BettiSupportGovernance : Set where
  constructor mkBettiSupportGovernance
  field
    governanceCandidateRow :
      CandidateOnly.CandidateOnlyRow

    governanceCandidateReceipt :
      CandidateOnly.CandidateOnlyReceipt governanceCandidateRow

    governanceAuthorityBundle :
      AuthorityNA.AuthorityNonPromotionBundle

    governanceBlockedAuthorityKinds :
      List AuthorityNA.AuthorityKind

    governanceBlockedAuthorityKindsAreCanonical :
      governanceBlockedAuthorityKinds ≡ bettiBlockedAuthorityKinds

    governanceBlockedAuthorityKindsFalse :
      AuthorityNA.AllAuthorityKindsFalse
        governanceAuthorityBundle
        governanceBlockedAuthorityKinds

    governancePhaseFieldBridge :
      PhaseField.PolarityPhaseFieldBridge

    governancePhaseFieldBridgeIsCanonical :
      governancePhaseFieldBridge ≡
      PhaseField.canonicalPolarityPhaseFieldBridge

    governanceResidualTopologyStatus :
      PNFTopology.PNFHodgeResidualTopologyStatus

    governanceResidualTopologyStatusIsReceiptOnly :
      governanceResidualTopologyStatus ≡
      PNFTopology.residualTopologyReceipt_noHodgeAuthorityPromotion

    governanceCandidateOnly :
      Bool

    governancePromoted :
      Bool

    governanceCandidateOnlyIsTrue :
      governanceCandidateOnly ≡ true

    governancePromotedIsFalse :
      governancePromoted ≡ false

open BettiSupportGovernance public

canonicalBettiSupportGovernance : BettiSupportGovernance
canonicalBettiSupportGovernance =
  mkBettiSupportGovernance
    bettiCandidateOnlyRow
    bettiCandidateOnlyReceipt
    AuthorityNA.canonicalAuthorityNonPromotionBundle
    bettiBlockedAuthorityKinds
    refl
    (AuthorityNA.proveAllAuthorityKindsFalse
      AuthorityNA.canonicalAuthorityNonPromotionBundle
      bettiBlockedAuthorityKinds)
    PhaseField.canonicalPolarityPhaseFieldBridge
    refl
    PNFTopology.residualTopologyReceipt_noHodgeAuthorityPromotion
    refl
    true
    false
    refl
    refl

------------------------------------------------------------------------
-- Top-level local Betti boundary.

record PolarityBettiSupportBoundary : Set where
  constructor mkPolarityBettiSupportBoundary
  field
    boundaryLabel :
      String

    boundaryPhaseFieldBridge :
      PhaseField.PolarityPhaseFieldBridge

    boundaryPhaseFieldBridgeIsCanonical :
      boundaryPhaseFieldBridge ≡
      PhaseField.canonicalPolarityPhaseFieldBridge

    boundaryResidualTopologyStatus :
      PNFTopology.PNFHodgeResidualTopologyStatus

    boundaryResidualTopologyStatusIsReceiptOnly :
      boundaryResidualTopologyStatus ≡
      PNFTopology.residualTopologyReceipt_noHodgeAuthorityPromotion

    boundaryRows :
      List BettiSupportRow

    boundaryRowCount :
      Nat

    boundaryRowCountMatches :
      boundaryRowCount ≡ listCount boundaryRows

    boundaryGovernance :
      BettiSupportGovernance

    boundaryCandidateOnly :
      Bool

    boundaryPromoted :
      Bool

    boundaryCandidateOnlyIsTrue :
      boundaryCandidateOnly ≡ true

    boundaryPromotedIsFalse :
      boundaryPromoted ≡ false

open PolarityBettiSupportBoundary public

PolarityBettiSupportBoundaryReceipt : Set
PolarityBettiSupportBoundaryReceipt =
  PolarityBettiSupportBoundary

canonicalPolarityBettiSupportBoundary : PolarityBettiSupportBoundary
canonicalPolarityBettiSupportBoundary =
  mkPolarityBettiSupportBoundary
    "polarity-betti-support-boundary"
    PhaseField.canonicalPolarityPhaseFieldBridge
    refl
    PNFTopology.residualTopologyReceipt_noHodgeAuthorityPromotion
    refl
    canonicalBettiRows
    3
    refl
    canonicalBettiSupportGovernance
    true
    false
    refl
    refl

canonicalPolarityBettiSupportBoundaryReceipt :
  PolarityBettiSupportBoundaryReceipt
canonicalPolarityBettiSupportBoundaryReceipt =
  canonicalPolarityBettiSupportBoundary

boundaryRowsAreCanonical :
  boundaryRows canonicalPolarityBettiSupportBoundary ≡ canonicalBettiRows
boundaryRowsAreCanonical = refl

boundaryGovernanceBlockedKindsFalse :
  AuthorityNA.AllAuthorityKindsFalse
    (governanceAuthorityBundle
      (boundaryGovernance canonicalPolarityBettiSupportBoundary))
    (governanceBlockedAuthorityKinds
      (boundaryGovernance canonicalPolarityBettiSupportBoundary))
boundaryGovernanceBlockedKindsFalse =
  governanceBlockedAuthorityKindsFalse canonicalBettiSupportGovernance

boundaryPolicySummary : String
boundaryPolicySummary =
  "candidate-only local Betti boundary over polarity-phase support geometry and supervoxels, with beta-0 components, beta-1 loops, beta-2 cavities, and receipt-only residual topology references"

------------------------------------------------------------------------
-- Stage fibres, quotient support, and carry-depth summaries.

data BettiTopologyStage : Set where
  supportGeometryStage : BettiTopologyStage
  quotientSupportStage : BettiTopologyStage
  carryDepthStage : BettiTopologyStage

record BettiStageFibre : Set where
  constructor mkBettiStageFibre
  field
    stageFibreLabel :
      String

    stageFibreStage :
      BettiTopologyStage

    stageFibreRow :
      BettiSupportRow

    stageFibreSupportSurface :
      BettiSupportSurface

    stageFibreSupportSurfaceMatches :
      stageFibreSupportSurface ≡ rowSupportSurface stageFibreRow

    stageFibreSupportGeometry :
      PhaseField.SupportGeometry

    stageFibreSupportSupervoxel :
      PhaseField.Supervoxel

    stageFibreSupportWave :
      PhaseField.WaveCandidateMixture

    stageFibreCarryDepth :
      Nat

    stageFibreCarryDepthMatches :
      stageFibreCarryDepth ≡ rowLocalScale stageFibreRow

    stageFibreCandidateOnly :
      Bool

    stageFibrePromoted :
      Bool

    stageFibreCandidateOnlyIsTrue :
      stageFibreCandidateOnly ≡ true

    stageFibrePromotedIsFalse :
      stageFibrePromoted ≡ false

open BettiStageFibre public

canonicalBeta0StageFibre : BettiStageFibre
canonicalBeta0StageFibre =
  mkBettiStageFibre
    "beta-0-stage-fibre"
    supportGeometryStage
    canonicalBeta0Row
    supportGeometrySurface
    refl
    PhaseField.canonicalBalancedSupportGeometry
    PhaseField.canonicalBalancedSupervoxel
    PhaseField.canonicalStandingWave
    (suc (suc zero))
    refl
    true
    false
    refl
    refl

canonicalBeta1StageFibre : BettiStageFibre
canonicalBeta1StageFibre =
  mkBettiStageFibre
    "beta-1-stage-fibre"
    quotientSupportStage
    canonicalBeta1Row
    mixedLocalSurface
    refl
    PhaseField.canonicalYinSupportGeometry
    PhaseField.canonicalYinYangSupervoxel
    PhaseField.canonicalYinYangWave
    (suc zero)
    refl
    true
    false
    refl
    refl

canonicalBeta2StageFibre : BettiStageFibre
canonicalBeta2StageFibre =
  mkBettiStageFibre
    "beta-2-stage-fibre"
    carryDepthStage
    canonicalBeta2Row
    supervoxelSurface
    refl
    PhaseField.canonicalYangSupportGeometry
    PhaseField.canonicalBalancedSupervoxel
    PhaseField.canonicalCounterWave
    (suc zero)
    refl
    true
    false
    refl
    refl

canonicalBettiStageFibres : List BettiStageFibre
canonicalBettiStageFibres =
  canonicalBeta0StageFibre
  ∷ canonicalBeta1StageFibre
  ∷ canonicalBeta2StageFibre
  ∷ []

canonicalBettiStageFibreCount : Nat
canonicalBettiStageFibreCount =
  listCount canonicalBettiStageFibres

canonicalBettiStageFibreCountIs3 :
  canonicalBettiStageFibreCount ≡ 3
canonicalBettiStageFibreCountIs3 = refl

bettiStageFibrePolicySummary : String
bettiStageFibrePolicySummary =
  "candidate-only stage fibres read the beta rows as stage-local support geometry, quotient support, and carry-depth summaries without promoting topology authority"

data BettiQuotientSupportKind : Set where
  geometryQuotientSupport : BettiQuotientSupportKind
  quotientSurfaceSupport : BettiQuotientSupportKind
  carryDepthQuotientSupport : BettiQuotientSupportKind

record BettiQuotientSupport : Set where
  constructor mkBettiQuotientSupport
  field
    quotientSupportLabel :
      String

    quotientSupportKind :
      BettiQuotientSupportKind

    quotientSupportRow :
      BettiSupportRow

    quotientSupportSurface :
      BettiSupportSurface

    quotientSupportSurfaceMatches :
      quotientSupportSurface ≡ rowSupportSurface quotientSupportRow

    quotientSupportGeometry :
      PhaseField.SupportGeometry

    quotientSupportSupervoxel :
      PhaseField.Supervoxel

    quotientSupportWave :
      PhaseField.WaveCandidateMixture

    quotientSupportCarryDepth :
      Nat

    quotientSupportCarryDepthMatches :
      quotientSupportCarryDepth ≡ rowLocalScale quotientSupportRow

    quotientSupportCandidateOnly :
      Bool

    quotientSupportPromoted :
      Bool

    quotientSupportCandidateOnlyIsTrue :
      quotientSupportCandidateOnly ≡ true

    quotientSupportPromotedIsFalse :
      quotientSupportPromoted ≡ false

open BettiQuotientSupport public

canonicalBeta0QuotientSupport : BettiQuotientSupport
canonicalBeta0QuotientSupport =
  mkBettiQuotientSupport
    "beta-0-quotient-support"
    geometryQuotientSupport
    canonicalBeta0Row
    supportGeometrySurface
    refl
    PhaseField.canonicalBalancedSupportGeometry
    PhaseField.canonicalBalancedSupervoxel
    PhaseField.canonicalStandingWave
    (suc (suc zero))
    refl
    true
    false
    refl
    refl

canonicalBeta1QuotientSupport : BettiQuotientSupport
canonicalBeta1QuotientSupport =
  mkBettiQuotientSupport
    "beta-1-quotient-support"
    quotientSurfaceSupport
    canonicalBeta1Row
    mixedLocalSurface
    refl
    PhaseField.canonicalYinSupportGeometry
    PhaseField.canonicalYinYangSupervoxel
    PhaseField.canonicalYinYangWave
    (suc zero)
    refl
    true
    false
    refl
    refl

canonicalBeta2QuotientSupport : BettiQuotientSupport
canonicalBeta2QuotientSupport =
  mkBettiQuotientSupport
    "beta-2-quotient-support"
    carryDepthQuotientSupport
    canonicalBeta2Row
    supervoxelSurface
    refl
    PhaseField.canonicalYangSupportGeometry
    PhaseField.canonicalBalancedSupervoxel
    PhaseField.canonicalCounterWave
    (suc zero)
    refl
    true
    false
    refl
    refl

canonicalBettiQuotientSupports : List BettiQuotientSupport
canonicalBettiQuotientSupports =
  canonicalBeta0QuotientSupport
  ∷ canonicalBeta1QuotientSupport
  ∷ canonicalBeta2QuotientSupport
  ∷ []

canonicalBettiQuotientSupportCount : Nat
canonicalBettiQuotientSupportCount =
  listCount canonicalBettiQuotientSupports

canonicalBettiQuotientSupportCountIs3 :
  canonicalBettiQuotientSupportCount ≡ 3
canonicalBettiQuotientSupportCountIs3 = refl

bettiQuotientSupportPolicySummary : String
bettiQuotientSupportPolicySummary =
  "quotient support keeps the three Betti rows as finite quotient surfaces over local polarity-phase geometry, with candidate-only carries and blocked promotion"

record BettiCarryDepthSummary : Set where
  constructor mkBettiCarryDepthSummary
  field
    carryDepthSummaryLabel :
      String

    carryDepthSummaryRow :
      BettiSupportRow

    carryDepthSummaryStageFibre :
      BettiStageFibre

    carryDepthSummaryMeasure :
      Nat

    carryDepthSummaryMeasureMatches :
      carryDepthSummaryMeasure ≡ rowLocalScale carryDepthSummaryRow

    carryDepthSummarySurface :
      BettiSupportSurface

    carryDepthSummarySurfaceMatches :
      carryDepthSummarySurface ≡
      stageFibreSupportSurface carryDepthSummaryStageFibre

    carryDepthSummaryCandidateOnly :
      Bool

    carryDepthSummaryPromoted :
      Bool

    carryDepthSummaryCandidateOnlyIsTrue :
      carryDepthSummaryCandidateOnly ≡ true

    carryDepthSummaryPromotedIsFalse :
      carryDepthSummaryPromoted ≡ false

    carryDepthSummaryText :
      String

open BettiCarryDepthSummary public

canonicalBeta0CarryDepthSummary : BettiCarryDepthSummary
canonicalBeta0CarryDepthSummary =
  mkBettiCarryDepthSummary
    "beta-0-carry-depth-summary"
    canonicalBeta0Row
    canonicalBeta0StageFibre
    (suc (suc zero))
    refl
    supportGeometrySurface
    refl
    true
    false
    refl
    refl
    "beta-0 carry depth tracks the local support geometry scale and the stage-fibre quotient surface"

canonicalBeta1CarryDepthSummary : BettiCarryDepthSummary
canonicalBeta1CarryDepthSummary =
  mkBettiCarryDepthSummary
    "beta-1-carry-depth-summary"
    canonicalBeta1Row
    canonicalBeta1StageFibre
    (suc zero)
    refl
    mixedLocalSurface
    refl
    true
    false
    refl
    refl
    "beta-1 carry depth tracks the quotient-support surface and the local residual loop reading"

canonicalBeta2CarryDepthSummary : BettiCarryDepthSummary
canonicalBeta2CarryDepthSummary =
  mkBettiCarryDepthSummary
    "beta-2-carry-depth-summary"
    canonicalBeta2Row
    canonicalBeta2StageFibre
    (suc zero)
    refl
    supervoxelSurface
    refl
    true
    false
    refl
    refl
    "beta-2 carry depth tracks the supervoxel quotient and the cavity-style topological summary"

canonicalBettiCarryDepthSummaries : List BettiCarryDepthSummary
canonicalBettiCarryDepthSummaries =
  canonicalBeta0CarryDepthSummary
  ∷ canonicalBeta1CarryDepthSummary
  ∷ canonicalBeta2CarryDepthSummary
  ∷ []

canonicalBettiCarryDepthSummaryCount : Nat
canonicalBettiCarryDepthSummaryCount =
  listCount canonicalBettiCarryDepthSummaries

canonicalBettiCarryDepthSummaryCountIs3 :
  canonicalBettiCarryDepthSummaryCount ≡ 3
canonicalBettiCarryDepthSummaryCountIs3 = refl

bettiCarryDepthPolicySummary : String
bettiCarryDepthPolicySummary =
  "carry-depth summaries expose the beta rows as bounded local depth readings over the stage fibres, quotient support, and polarity-phase support geometry"

record BettiSupportTopologySummary : Set where
  constructor mkBettiSupportTopologySummary
  field
    supportTopologySummaryLabel :
      String

    supportTopologyStageFibres :
      List BettiStageFibre

    supportTopologyQuotientSupports :
      List BettiQuotientSupport

    supportTopologyCarryDepthSummaries :
      List BettiCarryDepthSummary

    supportTopologyCandidateOnly :
      Bool

    supportTopologyPromoted :
      Bool

    supportTopologyCandidateOnlyIsTrue :
      supportTopologyCandidateOnly ≡ true

    supportTopologyPromotedIsFalse :
      supportTopologyPromoted ≡ false

    supportTopologyPolicySummary :
      String

open BettiSupportTopologySummary public

canonicalBettiSupportTopologySummary : BettiSupportTopologySummary
canonicalBettiSupportTopologySummary =
  mkBettiSupportTopologySummary
    "polarity-betti-support-topology-summary"
    canonicalBettiStageFibres
    canonicalBettiQuotientSupports
    canonicalBettiCarryDepthSummaries
    true
    false
    refl
    refl
    "candidate-only topology summary over stage fibres, quotient support, and carry-depth readings for the canonical beta rows"

canonicalBettiSupportTopologySummaryReceipt :
  BettiSupportTopologySummary
canonicalBettiSupportTopologySummaryReceipt =
  canonicalBettiSupportTopologySummary

canonicalBettiTopologySummaryStageFibreCount :
  listCount (supportTopologyStageFibres canonicalBettiSupportTopologySummary) ≡ 3
canonicalBettiTopologySummaryStageFibreCount =
  refl

canonicalBettiTopologySummaryQuotientSupportCount :
  listCount (supportTopologyQuotientSupports canonicalBettiSupportTopologySummary) ≡ 3
canonicalBettiTopologySummaryQuotientSupportCount =
  refl

canonicalBettiTopologySummaryCarryDepthCount :
  listCount (supportTopologyCarryDepthSummaries canonicalBettiSupportTopologySummary) ≡ 3
canonicalBettiTopologySummaryCarryDepthCount =
  refl
