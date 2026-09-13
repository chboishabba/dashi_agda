{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPreferredD1SemanticsFrontierRound228Exact where

------------------------------------------------------------------------
-- ROUND228 / LEAST-PRIVILEGE D1 SEMANTICS
--
-- Round152 leaves one coarse equality saying BC2 D1 of the physical composite
-- equals the substituted first variation.  Existing owners show this contains
-- two logically independent coordinates:
--
--   D1a: BC2.firstVariation has the ordinary physical derivative semantics;
--   D1b: Round118.toPhysicalTangent is the first variation of the CMP116
--        substitution A=A(B).
--
-- Once those are identified, ordinary first-order chain rule has no A'' term
-- and the finite localized/global D1 sums are compiler-owned.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityFirstVariationRound105Exact as First
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as BC2D1
import DASHI.Physics.YangMills.BalabanBC1PhysicalCompositeD1ReductionRound152Exact as R152


data PreferredD1Leaf228 : Set where
  physicalBC2FirstVariationSemantics : PreferredD1Leaf228
  literalCMP116SubstitutionTangentIdentification : PreferredD1Leaf228
  ordinarySubstitutedFirstVariationChainRule : PreferredD1Leaf228
  finiteLocalizedD1Assembly : PreferredD1Leaf228

data LeafState228 : Set where
  closed open blocked : LeafState228

preferredD1LeafState228 : PreferredD1Leaf228 → LeafState228
preferredD1LeafState228 physicalBC2FirstVariationSemantics = open
preferredD1LeafState228 literalCMP116SubstitutionTangentIdentification = open
preferredD1LeafState228 ordinarySubstitutedFirstVariationChainRule = closed
preferredD1LeafState228 finiteLocalizedD1Assembly = closed

ordinaryD1ChainRuleClosed :
  preferredD1LeafState228 ordinarySubstitutedFirstVariationChainRule ≡ closed
ordinaryD1ChainRuleClosed = refl

finiteD1AssemblyClosed :
  preferredD1LeafState228 finiteLocalizedD1Assembly ≡ closed
finiteD1AssemblyClosed = refl

physicalBC2FirstVariationSemanticsLevel : ProofLevel
physicalBC2FirstVariationSemanticsLevel = BC2D1.presentCutBC2FirstVariationLinearityLevel

literalCMP116SubstitutionTangentIdentificationLevel : ProofLevel
literalCMP116SubstitutionTangentIdentificationLevel =
  Chain.literalCMP116SubstitutionDerivativeIdentificationLevel

ordinarySubstitutedFirstVariationCompilerLevel : ProofLevel
ordinarySubstitutedFirstVariationCompilerLevel =
  First.cmp116SubstitutedFirstVariationCompilerLevel

finiteLocalizedD1CompilerLevel : ProofLevel
finiteLocalizedD1CompilerLevel = R152.bc1PhysicalCompositeD1ReductionCompilerLevel

-- Compatibility: the old coarse physical-chain-rule leaf remains conditional
-- until D1a/D1b are actually supplied, but it is no longer the preferred
-- indivisible research coordinate.
legacyPhysicalCompositeD1ChainRuleLevel : ProofLevel
legacyPhysicalCompositeD1ChainRuleLevel = R152.literalPhysicalCompositeD1ChainRuleLevel

round228D1PhysicalClosure : Bool
round228D1PhysicalClosure = false

round228D1PhysicalClosureIsFalse : round228D1PhysicalClosure ≡ false
round228D1PhysicalClosureIsFalse = refl
