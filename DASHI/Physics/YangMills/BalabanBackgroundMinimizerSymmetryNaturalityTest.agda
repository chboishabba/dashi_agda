{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanBackgroundMinimizerSymmetryNaturalityTest where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanBackgroundMinimizerSymmetryNaturalityExact as N

uniquenessPaysNaturalityRegression :
  N.backgroundNaturalityFollowsFromInvariantVariationalProblem ≡ true
uniquenessPaysNaturalityRegression = refl

noPrimitiveBackgroundEquivarianceRegression :
  N.primitiveSelectedBackgroundEquivarianceRequired ≡ false
noPrimitiveBackgroundEquivarianceRegression = refl
