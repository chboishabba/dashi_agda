{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPreferredSourceRealizationFrontierRound212Exact where

------------------------------------------------------------------------
-- ROUND212 / INTROSPECTIVE SOURCE-REALIZATION FRONTIER
--
-- Two stale/over-strong payments are removed from the preferred route:
--
--   * R151's post-hoc equality between the Round108 density potential and the
--     BC1 potential is not an independent physical theorem when BC1 is built
--     from `R108.asCMP109116Continuation` from the outset.  The preferred
--     constructor in `BalabanR108BackedPresentCutActionExact` makes the scale,
--     background carrier and selected potential identical by construction.
--
--   * the Row-A scalar shooting inequality q < 1 is not an independent physical
--     estimate after a literal Ward/quartic response producer is supplied.
--     Round113/120 already compile the complete marginal + irrelevant finite
--     prefix sensitivity below one.  The physical work is the same-object
--     realization of that producer and its decomposition as the actual CMP109
--     beta difference on two generated histories.
--
-- This file therefore does NOT decrement any Clay research scoreboard.  It
-- only recomputes the first live source coordinates after those compiler-level
-- eliminations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (1ℚ; _<_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanR108BackedPresentCutActionExact as R108Backed
import DASHI.Physics.YangMills.BalabanA2PresentCutFallbackRound120Exact as A2
import DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseProducerAdapterExact as Producer

------------------------------------------------------------------------
-- PREFERRED LIVE COORDINATES
------------------------------------------------------------------------

data PreferredSourceLeaf212 : Set where
  r108SelectedPotentialSameObject : PreferredSourceLeaf212
  literalR108BackedPresentCutInputs : PreferredSourceLeaf212
  literalCMP109GeneratedHistoryResponseProducer : PreferredSourceLeaf212
  literalCMP109BetaDifferenceDecomposition : PreferredSourceLeaf212
  literalPhysicalCompositeD1ChainRule : PreferredSourceLeaf212
  rowAScalarSensitivityCompiler : PreferredSourceLeaf212

data LeafState212 : Set where
  closed open blocked : LeafState212

preferredLeafState212 : PreferredSourceLeaf212 → LeafState212
preferredLeafState212 r108SelectedPotentialSameObject = closed
preferredLeafState212 literalR108BackedPresentCutInputs = open
preferredLeafState212 literalCMP109GeneratedHistoryResponseProducer = open
preferredLeafState212 literalCMP109BetaDifferenceDecomposition = open
preferredLeafState212 literalPhysicalCompositeD1ChainRule = open
preferredLeafState212 rowAScalarSensitivityCompiler = closed

r108SelectedPotentialSameObjectClosed :
  preferredLeafState212 r108SelectedPotentialSameObject ≡ closed
r108SelectedPotentialSameObjectClosed = refl

rowAScalarSensitivityCompilerClosed :
  preferredLeafState212 rowAScalarSensitivityCompiler ≡ closed
rowAScalarSensitivityCompilerClosed = refl

------------------------------------------------------------------------
-- ROW-A SCALAR CONTRACTION IS ALREADY COMPILER OUTPUT
------------------------------------------------------------------------

rowAProducerFullSensitivityBelowOne :
  ∀ {cutoff : Nat}
    (producer : Producer.WardQuarticResponseProducer cutoff) →
  A2.presentCutTotalSensitivity producer cutoff < 1ℚ
rowAProducerFullSensitivityBelowOne = A2.presentCutFullSensitivityBelowOne

------------------------------------------------------------------------
-- INTROSPECTIVE PRIORITY
------------------------------------------------------------------------

-- R150 gives density/action realization the widest current consumer fanout.
-- After the preferred R108-backed constructor removes the post-hoc potential
-- equality, the first missing coordinate is the literal source instantiation
-- of the R108-backed present-cut object itself: second-variation calculus,
-- Eq.(5.1) binding, CMP116 normalized analytic demands, physical composite
-- family and concrete compact-group Heat/Doob realization on that SAME source.
preferredFirstOpenSourceLeaf212 : PreferredSourceLeaf212
preferredFirstOpenSourceLeaf212 = literalR108BackedPresentCutInputs

preferredFirstOpenSourceLeaf212IsOpen :
  preferredLeafState212 preferredFirstOpenSourceLeaf212 ≡ open
preferredFirstOpenSourceLeaf212IsOpen = refl

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
------------------------------------------------------------------------

r108BackedSamePotentialEliminationLevel : ProofLevel
r108BackedSamePotentialEliminationLevel =
  R108Backed.r108BackedPresentCutActionCompilerLevel

rowAScalarSensitivityFromProducerLevel : ProofLevel
rowAScalarSensitivityFromProducerLevel = A2.a2PresentCutFullSubunitLevel

literalR108BackedPresentCutInputsLevel : ProofLevel
literalR108BackedPresentCutInputsLevel = conditional

literalCMP109GeneratedHistoryResponseProducerLevel : ProofLevel
literalCMP109GeneratedHistoryResponseProducerLevel = conditional

literalCMP109BetaDifferenceDecompositionLevel : ProofLevel
literalCMP109BetaDifferenceDecompositionLevel = conditional

literalPhysicalCompositeD1ChainRuleLevel : ProofLevel
literalPhysicalCompositeD1ChainRuleLevel = conditional

round212PhysicalSourceClosure : Bool
round212PhysicalSourceClosure = false

round212ClayPromotion : Bool
round212ClayPromotion = false

round212PhysicalSourceClosureIsFalse : round212PhysicalSourceClosure ≡ false
round212PhysicalSourceClosureIsFalse = refl

round212ClayPromotionIsFalse : round212ClayPromotion ≡ false
round212ClayPromotionIsFalse = refl
