module DASHI.EverythingTOESymmetryResolved369 where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)

------------------------------------------------------------------------
-- Focused TOE aggregate: generic symmetry-resolved fibre calculus plus the
-- existing SSP/369 representation-reduction and physics instances.
------------------------------------------------------------------------

import DASHI.Core.SymmetryResolvedFibreExact
import DASHI.EverythingSSPRepresentationReductionRound9
import DASHI.Physics.Closure.TOESymmetryResolved369BridgeExact

-- Reuse the existing exact finite GR/quantum proof-term regression.
-- It contains a terminal physical non-promotion theorem.
-- Do not replace this import with DASHI.Unifier placeholder axioms.
import DASHI.Unified.GRQuantumProofTermRegression
import DASHI.Physics.YangMills.YangMillsTOEConvergenceRound559Exact as YMTOE
import DASHI.Physics.YangMills.YangMillsTOEConvergenceRound559Validation


------------------------------------------------------------------------
-- Direct Yang-Mills TOE exports.
--
-- These aliases keep the root fail-closed.
-- They do not create a second theorem owner.
------------------------------------------------------------------------

toe369YangMillsBetaDrivenSourceFlowLevel : ProofLevel
toe369YangMillsBetaDrivenSourceFlowLevel =
  YMTOE.toeBetaDrivenSourceFlowLevel

toe369YangMillsBetaHistorySameStateCouplingLevel : ProofLevel
toe369YangMillsBetaHistorySameStateCouplingLevel =
  YMTOE.toeBetaHistorySameStateCouplingLevel

toe369YangMillsCanonicalCompleteDensityLevel : ProofLevel
toe369YangMillsCanonicalCompleteDensityLevel =
  YMTOE.toeBetaHistoryToCanonicalCompleteDensityLevel

toe369YangMillsRegularEProjectionLevel : ProofLevel
toe369YangMillsRegularEProjectionLevel =
  YMTOE.toePublishedFlowToRegularEProjectionCompilerLevel

toe369YangMillsRegularELocalizationSourceLevel : ProofLevel
toe369YangMillsRegularELocalizationSourceLevel =
  YMTOE.toeCMP119RegularELocalizationSourceLevel

toe369YangMillsStressScaleCompilerLevel : ProofLevel
toe369YangMillsStressScaleCompilerLevel =
  YMTOE.toeUnifiedGeneratedActionStressScaleCompilerLevel

toe369YangMillsStrictCasimirCarrierLevel : ProofLevel
toe369YangMillsStrictCasimirCarrierLevel =
  YMTOE.toeStrictCasimirCarrierCompilerLevel

toe369YangMillsPublishedRGDoesNotPromoteContinuum :
  YMTOE.toeFlat4DContinuumTransferProvedHere ≡ false
toe369YangMillsPublishedRGDoesNotPromoteContinuum =
  YMTOE.toePublishedRGDoesNotPromoteContinuum

toe369YangMillsOSWightmanContinuumNotConstructed :
  YMTOE.toeOSWightmanContinuumConstructionProvedHere ≡ false
toe369YangMillsOSWightmanContinuumNotConstructed =
  YMTOE.toeOSWightmanContinuumConstructionProvedHereIsFalse

toe369YangMillsContinuumMassGapNotPromoted :
  YMTOE.toeContinuumMassGapPromoted ≡ false
toe369YangMillsContinuumMassGapNotPromoted =
  YMTOE.toeContinuumMassGapPromotedIsFalse

toe369YangMillsClayNotPromoted :
  YMTOE.toeClayYangMillsPromoted ≡ false
toe369YangMillsClayNotPromoted =
  YMTOE.toeClayYangMillsPromotedIsFalse
