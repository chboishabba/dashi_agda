module DASHI.Cognition.PNF.OrientedZeroGrayTransitionGeometryExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.OrientedZeroFutureQuotientExact as Wave

bitDifference : Bool → Bool → Nat
bitDifference false false = 0
bitDifference false true = 1
bitDifference true false = 1
bitDifference true true = 0

hamming : Wave.TwoBit → Wave.TwoBit → Nat
hamming left right =
  bitDifference (Wave.high left) (Wave.high right)
  + bitDifference (Wave.low left) (Wave.low right)

binaryNegativeToApproachDistance :
  hamming (Wave.binaryCode Wave.negativeOne)
    (Wave.binaryCode Wave.negativeZero) ≡ 1
binaryNegativeToApproachDistance = refl

binaryZeroCrossingDistance :
  hamming (Wave.binaryCode Wave.negativeZero)
    (Wave.binaryCode Wave.positiveZero) ≡ 2
binaryZeroCrossingDistance = refl

binaryLeaveToPositiveDistance :
  hamming (Wave.binaryCode Wave.positiveZero)
    (Wave.binaryCode Wave.positiveOne) ≡ 1
binaryLeaveToPositiveDistance = refl

grayNegativeToApproachDistance :
  hamming (Wave.grayCode Wave.negativeOne)
    (Wave.grayCode Wave.negativeZero) ≡ 1
grayNegativeToApproachDistance = refl

grayZeroCrossingDistance :
  hamming (Wave.grayCode Wave.negativeZero)
    (Wave.grayCode Wave.positiveZero) ≡ 1
grayZeroCrossingDistance = refl

grayLeaveToPositiveDistance :
  hamming (Wave.grayCode Wave.positiveZero)
    (Wave.grayCode Wave.positiveOne) ≡ 1
grayLeaveToPositiveDistance = refl

binaryPathDistortion : Nat
binaryPathDistortion =
  hamming (Wave.binaryCode Wave.negativeOne) (Wave.binaryCode Wave.negativeZero)
  + hamming (Wave.binaryCode Wave.negativeZero) (Wave.binaryCode Wave.positiveZero)
  + hamming (Wave.binaryCode Wave.positiveZero) (Wave.binaryCode Wave.positiveOne)

grayPathDistortion : Nat
grayPathDistortion =
  hamming (Wave.grayCode Wave.negativeOne) (Wave.grayCode Wave.negativeZero)
  + hamming (Wave.grayCode Wave.negativeZero) (Wave.grayCode Wave.positiveZero)
  + hamming (Wave.grayCode Wave.positiveZero) (Wave.grayCode Wave.positiveOne)

binaryPathDistortionIsFour : binaryPathDistortion ≡ 4
binaryPathDistortionIsFour = refl

grayPathDistortionIsThree : grayPathDistortion ≡ 3
grayPathDistortionIsThree = refl

grayStrictlyImprovesPathDistortion : grayPathDistortion < binaryPathDistortion
grayStrictlyImprovesPathDistortion = s≤s (s≤s (s≤s (s≤s z≤n)))

------------------------------------------------------------------------
-- Equal-rate second-order objective.
------------------------------------------------------------------------

fixedCodeRate : Nat
fixedCodeRate = 2

binaryRatePlusTransition : Nat
binaryRatePlusTransition = fixedCodeRate + binaryPathDistortion

grayRatePlusTransition : Nat
grayRatePlusTransition = fixedCodeRate + grayPathDistortion

binaryRatePlusTransitionIsSix : binaryRatePlusTransition ≡ 6
binaryRatePlusTransitionIsSix = refl

grayRatePlusTransitionIsFive : grayRatePlusTransition ≡ 5
grayRatePlusTransitionIsFive = refl

grayStrictlyImprovesEqualRateDynamicObjective :
  grayRatePlusTransition < binaryRatePlusTransition
grayStrictlyImprovesEqualRateDynamicObjective =
  s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

------------------------------------------------------------------------
-- Minimum description length alone therefore does not determine the best exact
-- code: equal-rate encodings may induce different dynamical geometry.
------------------------------------------------------------------------
