{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanInternalCompilerSourceRealizationFrontierRound154Exact where

------------------------------------------------------------------------
-- ROUND154 / INTERNAL COMPILER CLOSURE != SOURCE REALIZATION CLOSURE
--
-- Cross-pollinated proof shape only.  The finite-Heisenberg work motivates
-- the dependency discipline, but no Monster/Base369 carrier, group or
-- representation statement is imported into Yang--Mills.
--
-- R151 and R152 already expose the exact seam themselves:
--   machine-checked compiler from a supplied realization/chain-rule receipt
--   != literal source realization/physical chain-rule receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanRound108DirectUnifiedActionRound151Exact as R151
import DASHI.Physics.YangMills.BalabanBC1PhysicalCompositeD1ReductionRound152Exact as R152
import DASHI.Physics.YangMills.BalabanSequentialDiagnosticPlannerRound153Exact as R153

data SourceRealizationLeaf : Set where
  round108DirectCompiler : SourceRealizationLeaf
  literalRound108DensityPotentialRealization : SourceRealizationLeaf
  componentD1ReductionCompiler : SourceRealizationLeaf
  literalPhysicalCompositeChainRule : SourceRealizationLeaf
  diagnosticPlanner : SourceRealizationLeaf
  physicalSourceClosure : SourceRealizationLeaf

data LeafState : Set where closed open blocked : LeafState

leafState : SourceRealizationLeaf → LeafState
leafState round108DirectCompiler = closed
leafState literalRound108DensityPotentialRealization = open
leafState componentD1ReductionCompiler = closed
leafState literalPhysicalCompositeChainRule = open
leafState diagnosticPlanner = closed
leafState physicalSourceClosure = blocked

data Requires : SourceRealizationLeaf → SourceRealizationLeaf → Set where
  sourceNeedsLiteralDensityRealization :
    Requires physicalSourceClosure literalRound108DensityPotentialRealization
  sourceNeedsLiteralD1ChainRule :
    Requires physicalSourceClosure literalPhysicalCompositeChainRule

round151InternalCompilerClosed : leafState round108DirectCompiler ≡ closed
round151InternalCompilerClosed = refl

round151LiteralRealizationStillLive :
  leafState literalRound108DensityPotentialRealization ≡ open
round151LiteralRealizationStillLive = refl

round152InternalCompilerClosed : leafState componentD1ReductionCompiler ≡ closed
round152InternalCompilerClosed = refl

round152LiteralChainRuleStillLive :
  leafState literalPhysicalCompositeChainRule ≡ open
round152LiteralChainRuleStillLive = refl

internalCompilerClosureDoesNotCloseSource :
  leafState physicalSourceClosure ≡ blocked
internalCompilerClosureDoesNotCloseSource = refl

highestImpactRealizationLeaf : SourceRealizationLeaf
highestImpactRealizationLeaf = literalRound108DensityPotentialRealization

round154PhysicalSourceClosure : Bool
round154PhysicalSourceClosure = false

round154ClayPromotion : Bool
round154ClayPromotion = false

round154PhysicalSourceClosureIsFalse : round154PhysicalSourceClosure ≡ false
round154PhysicalSourceClosureIsFalse = refl

round154ClayPromotionIsFalse : round154ClayPromotion ≡ false
round154ClayPromotionIsFalse = refl
