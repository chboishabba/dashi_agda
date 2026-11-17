module DASHI.Physics.Closure.NSTriadKNHeatWeightedOperatorTTStarReuseRound338Exact where

------------------------------------------------------------------------
-- ROUND338 / BIDI REUSE: OPERATOR TT* COMPILER AND SUPPORT-OVERLAP REDUCTION
-- ARE ALREADY IN THE REPOSITORY
--
-- R336 attached the literal R329 heat-weighted nested cells to the old signed
-- scalar pre-TT* ledger.  A deeper repo audit shows that the operator-level
-- downstream is also already owned:
--
-- * R30 owns the finite cutoff-uniform Cotlar--Stein compiler for ONE operator
--   family, including BOTH T_q^* T_r and T_q T_r^* faces;
-- * R42 owns the weaker physical support-overlap route
--
--       P(q,r) <= m(q,r) g(distance),   0 <= m <= 1,
--
--   so exact equality with a model Gram kernel is unnecessary;
-- * R43 removes duplication of the two Cotlar faces only after a literal
--   skew-adjoint T*=-T seam has been proved for the old transport matrix;
-- * R61/R63 already own the width-one/common-hat and normalized-support
--   architecture used downstream of such a physical product estimate.
--
-- Therefore none of those abstractions should be rebuilt for F_s.  The live
-- carrier-specific obligations are narrower:
--
--   (1) realize the literal heat-weighted nested R329 shell family as the SAME
--       operatorAt family consumed by R30;
--   (2) prove the physical pair-product support envelope on that family;
--   (3) prove a weighted skew/self-adjoint relation only if one wants to reuse
--       R43's one-face collapse.  R294 swap-invariance alone does NOT imply it.
--
-- In particular, a scalar real-Hermitian overlap receipt from R336 is useful
-- but is not by itself an R30 OperatorCrossShellDecay witness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Admission
import DASHI.Physics.Closure.NSTriadKNCutoffUniformCotlarSteinRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNComSupportOverlapRound42Exact as R42
import DASHI.Physics.Closure.NSTriadKNComAdjointSupportEnvelopeRound43Exact as R43
import DASHI.Physics.Closure.NSTriadKNComActiveSixThreeRealizationRound61Exact as R61
import DASHI.Physics.Closure.NSTriadKNResonantDominantCommonHatRound63Exact as R63
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedPreTTStarAdapterRound336Exact as R336
import DASHI.Physics.Closure.NSTriadKNLocalWitnessGlobalAggregationFrontierRound337Exact as R337

data HeatWeightedTTStarLeaf : Set where
  literalShellOperatorRealization : HeatWeightedTTStarLeaf
  physicalLeftPairProductEnvelope : HeatWeightedTTStarLeaf
  physicalRightPairProductEnvelope : HeatWeightedTTStarLeaf
  optionalWeightedAdjointCollapse : HeatWeightedTTStarLeaf
  cutoffUniformCotlarAggregation : HeatWeightedTTStarLeaf
  spacetimeFsPayment : HeatWeightedTTStarLeaf

data LeafState : Set where closed open blocked optional : LeafState

leafState : HeatWeightedTTStarLeaf → LeafState
leafState literalShellOperatorRealization = open
leafState physicalLeftPairProductEnvelope = blocked
leafState physicalRightPairProductEnvelope = blocked
leafState optionalWeightedAdjointCollapse = optional
leafState cutoffUniformCotlarAggregation = blocked
leafState spacetimeFsPayment = blocked

operatorCotlarCompilerDisposition : Admission.RouteDisposition
operatorCotlarCompilerDisposition = Admission.redirectedReuse

supportOverlapReductionDisposition : Admission.RouteDisposition
supportOverlapReductionDisposition = Admission.redirectedReuse

oldTransportAdjointCollapseForFsDisposition : Admission.RouteDisposition
oldTransportAdjointCollapseForFsDisposition = Admission.rejected Admission.carrierMismatch

literalFsOperatorRealizationDisposition : Admission.RouteDisposition
literalFsOperatorRealizationDisposition = Admission.admitted

round338OperatorCotlarCompilerAlreadyOwned : Bool
round338OperatorCotlarCompilerAlreadyOwned =
  R30.operatorValuedCotlarSteinReducerClosed

round338SupportOverlapReductionAlreadyOwned : Bool
round338SupportOverlapReductionAlreadyOwned =
  R42.comSupportOverlapReductionClosed

round338OldAdjointFaceDuplicationRemovalAlreadyOwned : Bool
round338OldAdjointFaceDuplicationRemovalAlreadyOwned =
  R43.comAdjointFaceDuplicationRemoved

round338ActivePhysicalGramThenOverlapEnvelopePatternAlreadyOwned : Bool
round338ActivePhysicalGramThenOverlapEnvelopePatternAlreadyOwned =
  R61.b1ExactPhysicalGramThenB3SixThreeOverlapSuffices

round338EveryResonantTriadHasDominantCommonHatAlreadyOwned : Bool
round338EveryResonantTriadHasDominantCommonHatAlreadyOwned =
  R63.round63EveryResonantTriadHasConstructedDominantCommonHat

round338R294SwapInvariantWeightImpliesWeightedOperatorSkewAdjoint : Bool
round338R294SwapInvariantWeightImpliesWeightedOperatorSkewAdjoint = false

round338R336ScalarOverlapAloneInstantiatesR30OperatorDecay : Bool
round338R336ScalarOverlapAloneInstantiatesR30OperatorDecay = false

round338LiteralFsShellOperatorRealizationClosed : Bool
round338LiteralFsShellOperatorRealizationClosed = false

round338PhysicalTwoSidedFsPairProductEnvelopeClosed : Bool
round338PhysicalTwoSidedFsPairProductEnvelopeClosed = false

round338CutoffUniformCotlarClosed : Bool
round338CutoffUniformCotlarClosed = false

round338SpacetimeFsPaid : Bool
round338SpacetimeFsPaid = false

round338PackageAClosed : Bool
round338PackageAClosed = false

round338ClayPromotion : Bool
round338ClayPromotion = false

round338OperatorCotlarCompilerAlreadyOwnedIsTrue :
  round338OperatorCotlarCompilerAlreadyOwned ≡ true
round338OperatorCotlarCompilerAlreadyOwnedIsTrue = refl

round338R294SwapInvariantWeightImpliesWeightedOperatorSkewAdjointIsFalse :
  round338R294SwapInvariantWeightImpliesWeightedOperatorSkewAdjoint ≡ false
round338R294SwapInvariantWeightImpliesWeightedOperatorSkewAdjointIsFalse = refl

round338R336ScalarOverlapAloneInstantiatesR30OperatorDecayIsFalse :
  round338R336ScalarOverlapAloneInstantiatesR30OperatorDecay ≡ false
round338R336ScalarOverlapAloneInstantiatesR30OperatorDecayIsFalse = refl

round338PackageAClosedIsFalse : round338PackageAClosed ≡ false
round338PackageAClosedIsFalse = refl

round338ClayPromotionIsFalse : round338ClayPromotion ≡ false
round338ClayPromotionIsFalse = refl
