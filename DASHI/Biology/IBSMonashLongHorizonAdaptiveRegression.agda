module DASHI.Biology.IBSMonashLongHorizonAdaptiveRegression where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Biology.IBSMonashLongHorizonAdaptiveExact as M

longHorizonAtlasRegression : M.canonicalMonashLongHorizonAtlas ≡ M.canonicalMonashLongHorizonAtlas
longHorizonAtlasRegression = refl

siNotPredictorRegression : M.SingleSIHypomorphPredictsFODMAPOutcomePermission → ⊥
siNotPredictorRegression = M.singleSIHypomorphDoesNotPredictFODMAPOutcome

strictRestrictionNotGoalRegression : M.MoreRestrictionAlwaysBetterPermission → ⊥
strictRestrictionNotGoalRegression = M.moreRestrictionIsNotAlwaysBetter
