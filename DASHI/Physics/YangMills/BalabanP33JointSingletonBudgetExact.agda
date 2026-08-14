module DASHI.Physics.YangMills.BalabanP33JointSingletonBudgetExact where

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector

jointSingletonBudget : ℚ
jointSingletonBudget = + 55 / 18874368

jointSingletonBudgetMatchesSelector :
  jointSingletonBudget ≡ Selector.remainingSingletonCoefficient
jointSingletonBudgetMatchesSelector = ℚRing.solve []

p33JointSingletonBudgetLevel : ProofLevel
p33JointSingletonBudgetLevel = machineChecked
