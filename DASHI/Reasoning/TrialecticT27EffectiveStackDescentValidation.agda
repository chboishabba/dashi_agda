module DASHI.Reasoning.TrialecticT27EffectiveStackDescentValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.RelationalStageTwelveSiteExact as RelSheaf
import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower
import DASHI.Reasoning.TrialecticT27EffectiveStackDescentExact as Stack27
import DASHI.Reasoning.TrialecticGrothendieckThreeCellDescentExact as OldDescent
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell

policy : Tower.T27CompletionPolicy
policy = Tower.firstNine

boundary : Stack27.TrialecticT27EffectiveStackBoundary
boundary = Stack27.canonicalTrialecticT27EffectiveStackBoundary

objectDescentPaid : Stack27.completedT27ObjectDescentPaid boundary ≡ true
objectDescentPaid = refl

morphismDescentPaid : Stack27.completedT27MorphismDescentPaid boundary ≡ true
morphismDescentPaid = refl

localRecoveryPaid : Stack27.allThreeLocalMorphismsRecovered boundary ≡ true
localRecoveryPaid = refl

uniqueUpToIsoPaid : Stack27.completedT27RealizationsUniqueUpToTypedIso boundary ≡ true
uniqueUpToIsoPaid = refl

ambientNotPromoted : Stack27.unconstrainedAmbientT27EffectiveStackClaimed boundary ≡ false
ambientNotPromoted = refl

locals : RelSheaf.TriadicLocals Cell.CellDialectic
locals = OldDescent.structuredLocals Cell.canonicalCompatibleThreeCellBoundary

compatibility :
  RelSheaf.CompatibleOnTriadicCover OldDescent.cellOverlapSystem locals
compatibility = OldDescent.structuredCompatibility Cell.canonicalCompatibleThreeCellBoundary

canonicalRealization : Stack27.GraphGlobalRealization policy locals
canonicalRealization = Stack27.realizeCompatibleLocals policy locals compatibility
