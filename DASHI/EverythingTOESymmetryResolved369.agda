module DASHI.EverythingTOESymmetryResolved369 where

------------------------------------------------------------------------
-- Focused TOE aggregate: generic symmetry-resolved fibre calculus plus the
-- existing SSP/369 representation-reduction and physics instances.
------------------------------------------------------------------------

import DASHI.Core.SymmetryResolvedFibreExact
import DASHI.EverythingSSPRepresentationReductionRound9
import DASHI.Physics.Closure.TOESymmetryResolved369BridgeExact as NSTOE

-- Reuse the existing exact finite GR/quantum proof-term regression.
-- It contains a terminal physical non-promotion theorem.
-- Do not replace this import with DASHI.Unifier placeholder axioms.
import DASHI.Unified.GRQuantumProofTermRegression
import DASHI.Physics.Closure.NSABCDMaxCut20261002Exact as NSMaxCut
import DASHI.Unified.NSABCDTOENonPromotionBridgeExact as NSABCDTOE
import DASHI.Unified.NSABCDTOENonPromotionBridgeValidation

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)

toeNavierStokesClayPromotionRemainsFalse :
  NSMaxCut.clayPromotion ≡ false
toeNavierStokesClayPromotionRemainsFalse =
  NSABCDTOE.nsClayPromotionRemainsFalse


toeNavierStokesR650CombinedSelfExternalRecombined :
  NSTOE.NSR650.round650SelfExternalRecombineToSingleGlobalCommutator ≡ true
toeNavierStokesR650CombinedSelfExternalRecombined =
  NSTOE.toeNSR650CombinedSelfExternalRecombined

toeNavierStokesR650CombinedPaymentRemainsOpen :
  NSTOE.NSR650.round650CombinedSelfExternalCutoffUniformPaymentClosed ≡ false
toeNavierStokesR650CombinedPaymentRemainsOpen =
  NSTOE.toeNSR650CombinedCutoffUniformPaymentRemainsOpen

toeNavierStokesR650ClayPromotionRemainsFalse :
  NSTOE.NSR650.round650ClayPromotion ≡ false
toeNavierStokesR650ClayPromotionRemainsFalse =
  NSTOE.toeNSR650ClayPromotionRemainsFalse
