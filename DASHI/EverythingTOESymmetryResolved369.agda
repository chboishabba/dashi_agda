module DASHI.EverythingTOESymmetryResolved369 where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)

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
  ProofLevel
toe369YangMillsBlockDProjectiveCarrierLevel =
  YMBlockD.blockDProjectiveFiniteMarginalCarrierCompilerLevel

toe369YangMillsBlockDProjectivePhysicalMomentInputsLevel :
  ProofLevel
toe369YangMillsBlockDProjectivePhysicalMomentInputsLevel =
  YMBlockD.blockDProjectivePhysicalMomentCompactnessInputsLevel

toe369YangMillsBlockDSelectedMarginalDictionaryLevel :
  ProofLevel
toe369YangMillsBlockDSelectedMarginalDictionaryLevel =
  YMBlockD.blockDSelectedCMP119ToProjectiveMarginalDictionaryLevel

toe369YangMillsBlockDGlobalContainmentProducerLevel :
  ProofLevel
toe369YangMillsBlockDGlobalContainmentProducerLevel =
  YMBlockD.blockDGlobalSelectedContainmentProducerLevel

toe369YangMillsBlockDBoundedPlaquettePromotionAllowed :
  Bool
toe369YangMillsBlockDBoundedPlaquettePromotionAllowed =
  YMBlockD.blockDBoundedPlaquettePromotionAllowed

toe369YangMillsBlockDBoundedPlaquettePromotionAllowedIsFalse :
  toe369YangMillsBlockDBoundedPlaquettePromotionAllowed ≡ false
toe369YangMillsBlockDBoundedPlaquettePromotionAllowedIsFalse =
  YMBlockD.blockDBoundedPlaquettePromotionAllowedIsFalse

toe369YangMillsBlockDContinuumStillOpen :
  YMTOE.toeFlat4DContinuumTransferProvedHere ≡ false
toe369YangMillsBlockDContinuumStillOpen =
  YMBlockD.blockDFlat4DContinuumTransferStillOpen

toe369YangMillsBlockDClayStillNotPromoted :
  YMTOE.toeClayYangMillsPromoted ≡ false
toe369YangMillsBlockDClayStillNotPromoted =
  YMBlockD.blockDClayYangMillsStillNotPromoted
