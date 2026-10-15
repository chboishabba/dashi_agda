module DASHI.Physics.Foundations.OrientedBracketEMYMNS369Regression where

open import DASHI.Core.Prelude

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Physics.Foundations.OrientedThreeAxisBracket369Exact as Bracket369
import DASHI.Physics.Electromagnetism.RightHandRule369Exact as EM
import DASHI.Physics.YangMills.SU2Bracket369OrientationBridgeExact as YM
import DASHI.Physics.Closure.NSCross369OrientationBridgeExact as NS
import DASHI.Physics.YangMills.BalabanC3MonsterEquivarianceAuditExact as YMC3

------------------------------------------------------------------------
-- RED-first cross-domain contract.
--
-- This regression intentionally names the generic bracket owner and three
-- downstream physical bridges before their production files are added.
------------------------------------------------------------------------

rightHandXYZIsPositive :
  Bracket369.bracketOrientation Bracket369.xyzBracket ≡ BT.pos
rightHandXYZIsPositive = EM.xyzRightHandPositive

rightHandXZYIsNegative :
  Bracket369.bracketOrientation Bracket369.xzyBracket ≡ BT.neg
rightHandXZYIsNegative = EM.xzyRightHandNegative

parallelAxesAreNeutral :
  Bracket369.bracketOrientation Bracket369.xxyBracket ≡ BT.zero
parallelAxesAreNeutral = EM.repeatedAxisNeutral

rightHandSwapConjugatesC3 :
  (voxel : Bracket369.BracketVoxel) →
  Bracket369.bracketPhase (Bracket369.swapBracketInputs voxel)
  ≡ Bracket369.inverseBracketPhase (Bracket369.bracketPhase voxel)
rightHandSwapConjugatesC3 = Bracket369.swapBracketInputsConjugatesPhase

ymUsesSameOrientationSkeleton :
  YM.su2BracketUses369OrientationSkeleton ≡ true
ymUsesSameOrientationSkeleton = refl

ymPhysicalBalabanC3StillGated :
  YMC3.balabanLiteralC3ActionRecovered ≡ false
ymPhysicalBalabanC3StillGated = YM.balabanLiteralC3ActionStillGated

nsUsesSameOrientationSkeleton :
  NS.nsComplexCrossUses369OrientationSkeleton ≡ true
nsUsesSameOrientationSkeleton = refl

nsBeltramiParallelCrossSuppressionReused :
  NS.nsBeltramiCrossSuppressionReused ≡ true
nsBeltramiParallelCrossSuppressionReused = refl

nsOutputTransverseLerayCancellationReused :
  NS.nsOutputTransverseLerayCancellationReused ≡ true
nsOutputTransverseLerayCancellationReused = refl

nsComplex3AliasIsNotCyclicC3Promotion :
  NS.nsComplex3CarrierPromotedToCyclicC3 ≡ false
nsComplex3AliasIsNotCyclicC3Promotion = refl
