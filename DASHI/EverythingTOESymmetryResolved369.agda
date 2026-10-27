module DASHI.EverythingTOESymmetryResolved369 where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)

------------------------------------------------------------------------
-- Focused TOE aggregate: generic symmetry-resolved fibre calculus plus the
-- existing SSP/369 representation-reduction and physics instances.
------------------------------------------------------------------------

import DASHI.Core.SymmetryResolvedFibreExact
import DASHI.EverythingSSPRepresentationReductionRound9
import DASHI.Physics.Closure.TOESymmetryResolved369BridgeExact

import DASHI.Physics.YangMills.YangMillsTOEConvergenceRound559Exact as YMTOE
import DASHI.Physics.YangMills.YangMillsTOEConvergenceRound559Validation
import DASHI.Unified.YMBlockDMaxCutTOEExact as YMBlockD

------------------------------------------------------------------------
-- Yang-Mills TOE fail-closed root facts.
------------------------------------------------------------------------

toePublishedFiniteRGDoesNotPromoteFourDimensionalContinuum :
  YMTOE.toeFlat4DContinuumTransferProvedHere ≡ false
toePublishedFiniteRGDoesNotPromoteFourDimensionalContinuum =
  YMTOE.toePublishedRGDoesNotPromoteContinuum

toeYangMillsClayPromotionRemainsFalse :
  YMTOE.toeClayYangMillsPromoted ≡ false
toeYangMillsClayPromotionRemainsFalse =
  YMTOE.toeClayYangMillsPromotedIsFalse


------------------------------------------------------------------------
-- Yang-Mills Block-D compactness max-cut.
-- Reuse the normalized owner.
------------------------------------------------------------------------

toe369YangMillsBlockDProjectiveCarrierLevel :
  DASHI.Physics.YangMills.CompactLieProofLevel.ProofLevel
toe369YangMillsBlockDProjectiveCarrierLevel =
  YMBlockD.blockDProjectiveFiniteMarginalCarrierCompilerLevel

toe369YangMillsBlockDProjectivePhysicalMomentInputsLevel :
  DASHI.Physics.YangMills.CompactLieProofLevel.ProofLevel
toe369YangMillsBlockDProjectivePhysicalMomentInputsLevel =
  YMBlockD.blockDProjectivePhysicalMomentCompactnessInputsLevel

toe369YangMillsBlockDSelectedMarginalDictionaryLevel :
  DASHI.Physics.YangMills.CompactLieProofLevel.ProofLevel
toe369YangMillsBlockDSelectedMarginalDictionaryLevel =
  YMBlockD.blockDSelectedCMP119ToProjectiveMarginalDictionaryLevel

toe369YangMillsBlockDGlobalContainmentProducerLevel :
  DASHI.Physics.YangMills.CompactLieProofLevel.ProofLevel
toe369YangMillsBlockDGlobalContainmentProducerLevel =
  YMBlockD.blockDGlobalSelectedContainmentProducerLevel

toe369YangMillsBlockDBoundedPlaquetteDoesNotPayContinuum :
  YMBlockD.Projective.routeDisposition
    YMBlockD.Projective.boundedPlaquetteMoment
  ≡ YMBlockD.Projective.insufficientForContinuumContainment
toe369YangMillsBlockDBoundedPlaquetteDoesNotPayContinuum =
  YMBlockD.blockDBoundedPlaquetteMomentInsufficient

toe369YangMillsBlockDContinuumStillOpen :
  YMTOE.toeFlat4DContinuumTransferProvedHere ≡ false
toe369YangMillsBlockDContinuumStillOpen =
  YMBlockD.blockDFlat4DContinuumTransferStillOpen

toe369YangMillsBlockDClayStillNotPromoted :
  YMTOE.toeClayYangMillsPromoted ≡ false
toe369YangMillsBlockDClayStillNotPromoted =
  YMBlockD.blockDClayYangMillsStillNotPromoted
