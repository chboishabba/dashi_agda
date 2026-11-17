{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPreferredA2FrontierRound231Exact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanA2DirectMarginalDerivativeRound229Exact as Marginal
import DASHI.Physics.YangMills.BalabanA2MixedCauchyToDirectMarginalRound230Exact as StrongBridge
import DASHI.Physics.YangMills.BalabanA2SharedMarkedHistoryDerivativeRound116Exact as Marked
import DASHI.Physics.YangMills.BalabanA2MixedCauchyCubicMarginalRound112Exact as OldMarginal
import DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseProducerAdapterExact as Fallback

------------------------------------------------------------------------
-- ROUND231 / LEAST-PRIVILEGE A2 SOURCE FRONTIER
------------------------------------------------------------------------

data PreferredA2Leaf231 : Set where
  literalCMP109LocalBetaDerivativeBound : PreferredA2Leaf231
  marginalCubicSummation : PreferredA2Leaf231
  literalGeneratedHistoryDerivativeIsCMP116BetaMark : PreferredA2Leaf231
  betaMarkPartialSummation : PreferredA2Leaf231
  literalCMP109MarginalPlusIrrelevantDecomposition : PreferredA2Leaf231

data LeafState231 : Set where
  closed open blocked : LeafState231

preferredA2LeafState231 : PreferredA2Leaf231 → LeafState231
preferredA2LeafState231 literalCMP109LocalBetaDerivativeBound = open
preferredA2LeafState231 marginalCubicSummation = blocked
preferredA2LeafState231 literalGeneratedHistoryDerivativeIsCMP116BetaMark = open
preferredA2LeafState231 betaMarkPartialSummation = closed
preferredA2LeafState231 literalCMP109MarginalPlusIrrelevantDecomposition = blocked

preferredFirstA2Coordinate231 : PreferredA2Leaf231
preferredFirstA2Coordinate231 = literalCMP109LocalBetaDerivativeBound

preferredIndependentHistoryCoordinate231 : PreferredA2Leaf231
preferredIndependentHistoryCoordinate231 =
  literalGeneratedHistoryDerivativeIsCMP116BetaMark

localBetaDerivativeLevel : ProofLevel
localBetaDerivativeLevel = Marginal.literalCMP109LocalBetaDerivativeBoundLevel

marginalCompilerLevel : ProofLevel
marginalCompilerLevel = Marginal.a2DirectMarginalDerivativeCompilerLevel

betaMarkSameObjectLevel : ProofLevel
betaMarkSameObjectLevel = Marked.literalCMP116BetaMarkIsGeneratedHistoryDerivativeLevel

betaMarkCompilerLevel : ProofLevel
betaMarkCompilerLevel = Marked.a2SharedMarkedHistoryDerivativeCompilerLevel

marginalPlusIrrelevantDecompositionLevel : ProofLevel
marginalPlusIrrelevantDecompositionLevel =
  OldMarginal.literalCMP109MarginalPlusIrrelevantDecompositionLevel

-- The detailed mixed-Cauchy package is retained as a stronger producer of the
-- direct marginal contract; it is not the preferred A2 consumer premise.
strongMixedCauchyProducerCompilerLevel : ProofLevel
strongMixedCauchyProducerCompilerLevel =
  StrongBridge.mixedCauchyToDirectMarginalCompilerLevel

-- If the beta mark fails the same-object audit, retain the explicit response
-- kernel/quartic injection as a fallback producer rather than changing the
-- preferred consumer contract.
explicitResponseKernelFallbackLevel : ProofLevel
explicitResponseKernelFallbackLevel = Fallback.literalWardQuarticResponseProducerLevel

round231A2PhysicalClosure : Bool
round231A2PhysicalClosure = false

round231A2PhysicalClosureIsFalse : round231A2PhysicalClosure ≡ false
round231A2PhysicalClosureIsFalse = refl
