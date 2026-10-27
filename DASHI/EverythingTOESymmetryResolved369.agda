module DASHI.EverythingTOESymmetryResolved369 where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Unified.OggSSP2BTOEExact as TwoBTOE

------------------------------------------------------------------------
-- Focused TOE aggregate: generic symmetry-resolved fibre calculus plus the
-- existing SSP/369 representation-reduction and physics instances.
------------------------------------------------------------------------

import DASHI.Core.SymmetryResolvedFibreExact
import DASHI.EverythingSSPRepresentationReductionRound9
import DASHI.Physics.Closure.TOESymmetryResolved369BridgeExact


------------------------------------------------------------------------
-- Monster 2B normalized max-cut and non-promotion surface.
------------------------------------------------------------------------

toe2BResidualCountIsThree :
  TwoBTOE.normalizedTwoBResidualCount ≡ 3
toe2BResidualCountIsThree =
  TwoBTOE.normalizedTwoBResidualCountIsThree

toe2BRepresentationDiscoveryClosed :
  TwoBTOE.canonicalOggSSP2BTOEReceipt .representationDiscoveryLeaves ≡ 0
toe2BRepresentationDiscoveryClosed = refl

toe2BFormalSourceActionStillOpen :
  TwoBTOE.formalSourceActionPaidFlag ≡ false
toe2BFormalSourceActionStillOpen =
  TwoBTOE.formalSourceActionPaidFlagIsFalse

toe2BWeldEquivarianceStillOpen :
  TwoBTOE.weldEquivariancePaidFlag ≡ false
toe2BWeldEquivarianceStillOpen =
  TwoBTOE.weldEquivariancePaidFlagIsFalse

toe2BTerminalQ10RecognitionStillOpen :
  TwoBTOE.terminalQ10RecognitionPaidFlag ≡ false
toe2BTerminalQ10RecognitionStillOpen =
  TwoBTOE.terminalQ10RecognitionPaidFlagIsFalse

toe2BTerminalDefectSourceStillOpen :
  TwoBTOE.terminalDefectSourcePaidFlag ≡ false
toe2BTerminalDefectSourceStillOpen =
  TwoBTOE.terminalDefectSourcePaidFlagIsFalse

toe2BP31SameObjectPromotionStillBlocked :
  TwoBTOE.p31SameObjectPromotionPaidFlag ≡ false
toe2BP31SameObjectPromotionStillBlocked =
  TwoBTOE.p31SameObjectPromotionPaidFlagIsFalse

toe2B279SameObjectPromotionStillBlocked :
  TwoBTOE.twoSevenNineSameObjectPromotionPaidFlag ≡ false
toe2B279SameObjectPromotionStillBlocked =
  TwoBTOE.twoSevenNineSameObjectPromotionPaidFlagIsFalse

toe2BZKPFrame : TwoBTOE.OggSSP2BTOEZKPFrame
toe2BZKPFrame =
  TwoBTOE.canonicalOggSSP2BTOEZKPFrame

toe2BReceipt : TwoBTOE.OggSSP2BTOEReceipt
toe2BReceipt =
  TwoBTOE.canonicalOggSSP2BTOEReceipt
