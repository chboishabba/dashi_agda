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
