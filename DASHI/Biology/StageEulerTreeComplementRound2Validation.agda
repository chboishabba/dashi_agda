module DASHI.Biology.StageEulerTreeComplementRound2Validation where

import DASHI.Biology.PointedBulkSporadicTarotEverything
import DASHI.Foundations.BalancedTernaryResidualTreeExact as Tree
import DASHI.Foundations.StageProfile369SignedDistanceExact as Profile
import DASHI.Foundations.ConstrainedFrameEulerSelectorExact as Euler
import DASHI.Moonshine.DepthTwoNonaryStageTenComplementExact as Complement

open import DASHI.Core.Prelude
open import DASHI.Core.Optional

import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT

stageFiveFallbackRetainsOpenChild :
  Tree.residualConstituent Tree.stageFiveRetainedTree
  ≡ some BT.twoPositiveOneOpen
stageFiveFallbackRetainsOpenChild = Tree.stageFiveResidualIsStillPresent

stageFiveSignedProfileRegression :
  Profile.signedDistance6 Profile.stageFiveProfile369
  ≡ Profile.beforeClosure 1
stageFiveSignedProfileRegression = refl

stageSixSignedProfileRegression :
  Profile.signedDistance6 Profile.stageSixProfile369
  ≡ Profile.atClosure
stageSixSignedProfileRegression = refl

p71CrossScaleComplementRegression : 10 + 71 ≡ 81
p71CrossScaleComplementRegression =
  Complement.nonaryDepthTwoIsTenPlusSeventyOne

finiteFrameEulerRegression :
  Euler.finiteFirstVariation
    (Euler.deformation Euler.identityFrameDeformation)
  ≡ 0
finiteFrameEulerRegression = Euler.identityFrameVariationIsStationary
