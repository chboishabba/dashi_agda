module DASHI.Physics.Closure.E6HyperformH3H2InvariantPotentialNoGoValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.E6HyperformH3H2InvariantPotentialNoGoExact as NoGo

translationTransitivityPaid :
  NoGo.translationSubgroupTransitive NoGo.canonicalInvariantPotentialBoundary ≡ true
translationTransitivityPaid = refl

invariantPotentialConstantPaid :
  NoGo.translationInvariantSingleSitePotentialConstant NoGo.canonicalInvariantPotentialBoundary ≡ true
invariantPotentialConstantPaid = refl

selectionStillNeedsExtraStructure :
  NoGo.invariantOnsitePotentialSelectsUniqueH2 NoGo.canonicalInvariantPotentialBoundary ≡ false
selectionStillNeedsExtraStructure = refl
