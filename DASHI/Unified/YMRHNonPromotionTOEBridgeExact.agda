{-# OPTIONS --safe #-}
module DASHI.Unified.YMRHNonPromotionTOEBridgeExact where

------------------------------------------------------------------------
-- YM / RH NON-PROMOTION BRIDGE INTO THE FOCUSED TOE GRAPH
--
-- O/R/C/S/L/P/G/F
--
-- O: Reuse current theorem-bearing YM and RH boundaries.
-- R: Expose exact non-promotion facts to the TOE import graph.
-- C: Import only existing proof owners. Add no scientific theorem.
-- S: Keep YM and RH carriers distinct. Keep source authority unchanged.
-- L: YM mass-gap boundary and RH current direct frontier remain the owners.
-- P: The TOE graph can consume exact fail-closed proofs without promotion.
-- G: No Clay, RH, GRQFT, or terminal TOE promotion follows.
-- F: If either upstream boundary changes, this bridge must fail to elaborate.
--
-- Preconditions:
--   * canonical YM mass-gap boundary exists;
--   * current RH direct frontier exists;
--   * unified YM facade object exists.
--
-- Invariants:
--   * source theorem ownership remains upstream;
--   * a status receipt is not converted into a stronger theorem;
--   * YM and RH are not identified as the same mathematical object.
--
-- Postconditions:
--   * YM formal projections remain non-promoting;
--   * the YM Clay mass-gap promotion bit is false;
--   * the current RH frontier states that RH is not derived.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Unified.InvariantSpine as Spine
import DASHI.Unified.Physics as UnifiedPhysics
import DASHI.Physics.Closure.YangMillsMassGapBoundary as YM
import DASHI.Analysis.RiemannG2CurrentDirectOneLeafFrontierExact as RH

yangMillsUnifiedFormalProjectionRemainsNonPromoting :
  ∀ kind →
  Spine.objectProjectionPromotion UnifiedPhysics.yangMillsObject kind ≡ false
yangMillsUnifiedFormalProjectionRemainsNonPromoting =
  Spine.canonicalInvariantObjectsDoNotPromoteFormalProjections
    UnifiedPhysics.yangMillsObject

yangMillsClayMassGapNotPromoted :
  YM.YangMillsMassGapBoundaryReceipt.massGapPromoted
    YM.canonicalYangMillsMassGapBoundaryReceipt
  ≡ false
yangMillsClayMassGapNotPromoted =
  YM.YangMillsMassGapBoundaryReceipt.massGapPromotedIsFalse
    YM.canonicalYangMillsMassGapBoundaryReceipt

riemannHypothesisNotDerivedAtCurrentFrontier :
  RH.CurrentDirectOneLeafFrontierBoundary.rhDerived
    RH.canonicalCurrentDirectOneLeafFrontierBoundary
  ≡ false
riemannHypothesisNotDerivedAtCurrentFrontier =
  RH.CurrentDirectOneLeafFrontierBoundary.rhDerivedIsFalse
    RH.canonicalCurrentDirectOneLeafFrontierBoundary
