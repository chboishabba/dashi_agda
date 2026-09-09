module DASHI.Physics.Closure.NSTriadKNDyadicCriticalNormEquivalenceBoundaryRound517Exact where

------------------------------------------------------------------------
-- ROUND517 / DYADIC CRITICAL NORM EQUIVALENCE BOUNDARY
--
-- The introspective route to R515's physical critical-observable realization
-- begins here as a standard-analysis seam.  Later R518-R520 refine this seam:
--
--   R518 closes the canonical dyadic/Euclidean SQUARED annulus;
--   R519 reuses the constructed Bishop Nat root, nonnegativity and semantic
--        square law;
--   R520 proves finite floor-root and every canonical rational approximant are
--        monotone in the radicand.
--
-- Thus this file remains the historical whole-norm boundary, while the current
-- first missing coordinate is narrower: realize pointwise order of the regular
-- root approximants as order of the corresponding Bishop reals, then lift the
-- resulting modewise multiplier comparison through the finite Fourier sum.
--
-- No Navier--Stokes cancellation estimate is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNDyadicEuclideanShellMarginRound88Exact as R88
import DASHI.Physics.Closure.NSTriadKNConcreteUpperSquaredPacketRound104Exact as Packet
import DASHI.Physics.Closure.NSTriadKNCriticalProductionPacketLayerCakeRound104Exact as LayerCake
import DASHI.Physics.Closure.NSTriadKNCriticalRadialRealizationProofSearchRound516Exact as R516

data DyadicCriticalNormResidual : Set where
  missingUniformDyadicHOneHalfEquivalence : DyadicCriticalNormResidual
  missingUniformDyadicHThreeHalfEquivalence : DyadicCriticalNormResidual
  dyadicCriticalNormRealizationClosed : DyadicCriticalNormResidual

record DyadicCriticalNormStatus : Set where
  constructor dyadic-critical-norm-status
  field
    hOneHalfEquivalencePresent : Bool
    hThreeHalfEquivalencePresent : Bool

open DyadicCriticalNormStatus public

firstMissing : DyadicCriticalNormStatus → DyadicCriticalNormResidual
firstMissing (dyadic-critical-norm-status false h32) =
  missingUniformDyadicHOneHalfEquivalence
firstMissing (dyadic-critical-norm-status true false) =
  missingUniformDyadicHThreeHalfEquivalence
firstMissing (dyadic-critical-norm-status true true) =
  dyadicCriticalNormRealizationClosed

currentStatus : DyadicCriticalNormStatus
currentStatus = dyadic-critical-norm-status false false

currentFirstMissing :
  firstMissing currentStatus ≡ missingUniformDyadicHOneHalfEquivalence
currentFirstMissing = refl

round517InfinityEuclideanSquareComparisonClosed : Bool
round517InfinityEuclideanSquareComparisonClosed =
  R88.round88InfinityEuclideanSquareComparisonClosed

round517UpperPacketBoundaryFluxClosed : Bool
round517UpperPacketBoundaryFluxClosed =
  Packet.round104ConcreteUpperSquaredPacketBoundaryFluxClosed

round517FiniteRadialLayerCakeClosed : Bool
round517FiniteRadialLayerCakeClosed =
  LayerCake.round104FiniteRadialAbelLayerCakeClosed

round517DyadicProducerSelectedAsShortestFiniteRoute : Bool
round517DyadicProducerSelectedAsShortestFiniteRoute = true

round517UniformDyadicHOneHalfEquivalenceClosed : Bool
round517UniformDyadicHOneHalfEquivalenceClosed = false

round517UniformDyadicHThreeHalfEquivalenceClosed : Bool
round517UniformDyadicHThreeHalfEquivalenceClosed = false

round517LaterRoundsReduceThisToBishopOrderRealization : Bool
round517LaterRoundsReduceThisToBishopOrderRealization = true

round517ThisResidualIsStandardAnalysisNotNSCancellation : Bool
round517ThisResidualIsStandardAnalysisNotNSCancellation = true

round517ClayPromotion : Bool
round517ClayPromotion = false

round517InfinityEuclideanSquareComparisonClosedIsTrue :
  round517InfinityEuclideanSquareComparisonClosed ≡ true
round517InfinityEuclideanSquareComparisonClosedIsTrue =
  R88.round88InfinityEuclideanSquareComparisonClosedIsTrue

round517UpperPacketBoundaryFluxClosedIsTrue :
  round517UpperPacketBoundaryFluxClosed ≡ true
round517UpperPacketBoundaryFluxClosedIsTrue =
  Packet.round104ConcreteUpperSquaredPacketBoundaryFluxClosedIsTrue

round517FiniteRadialLayerCakeClosedIsTrue :
  round517FiniteRadialLayerCakeClosed ≡ true
round517FiniteRadialLayerCakeClosedIsTrue =
  LayerCake.round104FiniteRadialAbelLayerCakeClosedIsTrue

round517UniformDyadicHOneHalfEquivalenceClosedIsFalse :
  round517UniformDyadicHOneHalfEquivalenceClosed ≡ false
round517UniformDyadicHOneHalfEquivalenceClosedIsFalse = refl

round517UniformDyadicHThreeHalfEquivalenceClosedIsFalse :
  round517UniformDyadicHThreeHalfEquivalenceClosed ≡ false
round517UniformDyadicHThreeHalfEquivalenceClosedIsFalse = refl

round517LaterRoundsReduceThisToBishopOrderRealizationIsTrue :
  round517LaterRoundsReduceThisToBishopOrderRealization ≡ true
round517LaterRoundsReduceThisToBishopOrderRealizationIsTrue = refl

round517ClayPromotionIsFalse : round517ClayPromotion ≡ false
round517ClayPromotionIsFalse = refl
