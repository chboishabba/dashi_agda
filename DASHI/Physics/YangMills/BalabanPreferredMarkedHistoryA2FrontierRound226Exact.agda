{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPreferredMarkedHistoryA2FrontierRound226Exact where

------------------------------------------------------------------------
-- ROUND226 / PREFERRED A2 = DIRECT MARKED-HISTORY RESPONSE
--
-- The explicit geometric response-kernel + quartic-injection route is a useful
-- fallback decomposition, but Round116 is strictly weaker when its source mark
-- is the actual shooting-history derivative: the shared CMP116 beta mark already
-- has the finite partial-sum bound needed by Row A.
--
-- Preferred A2 source coordinates are therefore:
--
--   1. literal generated-history derivative = CMP116 beta-mark response;
--   2. literal CMP109 beta difference = marginal + irrelevant/history response.
--
-- Marginal cubic summation, beta-mark partial bound and canonical small-coupling
-- arithmetic are existing compilers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanA2SharedMarkedHistoryDerivativeRound116Exact as Marked
import DASHI.Physics.YangMills.BalabanA2MixedCauchyCubicMarginalRound112Exact as Marginal
import DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseProducerAdapterExact as Fallback
import DASHI.Physics.YangMills.BalabanPreferredSourceRealizationFrontierRound212Exact as R212


data PreferredA2Leaf226 : Set where
  literalMixedInteractionCauchySource : PreferredA2Leaf226
  literalGeneratedHistoryDerivativeIsCMP116BetaMark : PreferredA2Leaf226
  betaMarkPartialBound : PreferredA2Leaf226
  marginalCubicSensitivity : PreferredA2Leaf226
  literalCMP109MarginalPlusIrrelevantDecomposition : PreferredA2Leaf226
  canonicalRowASmallCouplingArithmetic : PreferredA2Leaf226

data LeafState226 : Set where
  closed open blocked : LeafState226

preferredA2LeafState226 : PreferredA2Leaf226 → LeafState226
preferredA2LeafState226 literalMixedInteractionCauchySource = open
preferredA2LeafState226 literalGeneratedHistoryDerivativeIsCMP116BetaMark = open
preferredA2LeafState226 betaMarkPartialBound = closed
preferredA2LeafState226 marginalCubicSensitivity = closed
preferredA2LeafState226 literalCMP109MarginalPlusIrrelevantDecomposition = blocked
preferredA2LeafState226 canonicalRowASmallCouplingArithmetic = closed

-- `mixedInteraction` is shared with the local/marginal lane.  If another source
-- owner supplies it, the next independent A2 coordinate is the beta-mark weld.
preferredFirstA2SourceCoordinate226 : PreferredA2Leaf226
preferredFirstA2SourceCoordinate226 = literalMixedInteractionCauchySource

preferredFirstA2HistoryCoordinate226 : PreferredA2Leaf226
preferredFirstA2HistoryCoordinate226 =
  literalGeneratedHistoryDerivativeIsCMP116BetaMark

betaMarkPartialCompilerClosed :
  preferredA2LeafState226 betaMarkPartialBound ≡ closed
betaMarkPartialCompilerClosed = refl

marginalCubicCompilerClosed :
  preferredA2LeafState226 marginalCubicSensitivity ≡ closed
marginalCubicCompilerClosed = refl

canonicalArithmeticClosed :
  preferredA2LeafState226 canonicalRowASmallCouplingArithmetic ≡ closed
canonicalArithmeticClosed = refl

literalGeneratedHistoryDerivativeIsCMP116BetaMarkLevel : ProofLevel
literalGeneratedHistoryDerivativeIsCMP116BetaMarkLevel =
  Marked.literalCMP116BetaMarkIsGeneratedHistoryDerivativeLevel

betaMarkPartialBoundCompilerLevel : ProofLevel
betaMarkPartialBoundCompilerLevel = Marked.a2SharedMarkedHistoryDerivativeCompilerLevel

marginalCubicSensitivityCompilerLevel : ProofLevel
marginalCubicSensitivityCompilerLevel = Marginal.a2MixedCauchyMarginalSensitivityLevel

literalCMP109MarginalPlusIrrelevantDecompositionLevel : ProofLevel
literalCMP109MarginalPlusIrrelevantDecompositionLevel =
  Marginal.literalCMP109MarginalPlusIrrelevantDecompositionLevel

-- Fallback only: if the beta mark does not denote the actual generated-history
-- derivative, the explicit Ward/quartic response producer remains available.
explicitResponseKernelFallbackLevel : ProofLevel
explicitResponseKernelFallbackLevel = Fallback.literalWardQuarticResponseProducerLevel

-- Historical alias from R212 now refines to the two preferred coordinates above;
-- it is not counted as an additional physical theorem.
legacyGeneratedHistoryProducerLevel : ProofLevel
legacyGeneratedHistoryProducerLevel =
  R212.literalCMP109GeneratedHistoryResponseProducerLevel

round226A2PhysicalClosure : Bool
round226A2PhysicalClosure = false

round226A2PhysicalClosureIsFalse : round226A2PhysicalClosure ≡ false
round226A2PhysicalClosureIsFalse = refl
