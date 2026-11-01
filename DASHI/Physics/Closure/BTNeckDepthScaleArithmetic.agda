module DASHI.Physics.Closure.BTNeckDepthScaleArithmetic where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

import DASHI.Physics.Closure.BTCanonicalNeckAnalogue as Neck

------------------------------------------------------------------------
-- Finite depth/scale arithmetic for the p = 2, 3, 7 BT neck lanes.
--
-- The scale is recorded only by its symbolic inverse-scale denominator
-- p^depth.  This is Nat-level bookkeeping for finite BT neck analogues:
-- no smooth S2 neck, Ricci flow, surgery continuation, or Clay claim is
-- promoted here.

pow : Nat → Nat → Nat
pow base zero =
  1
pow base (suc exponent) =
  base * pow base exponent

length : {A : Set} → List A → Nat
length [] =
  0
length (_ ∷ xs) =
  suc (length xs)

record BTNeckDepthScaleRow : Set where
  field
    primeLane :
      Neck.BTPrimeLane

    prime :
      Nat

    primeIsLaneValue :
      prime ≡ Neck.primeValue primeLane

    depth :
      Nat

    primePowerAtDepth :
      Nat

    primePowerAtDepthIsPow :
      primePowerAtDepth ≡ pow prime depth

    inverseScaleDenominator :
      Nat

    inverseScaleDenominatorIsPrimePower :
      inverseScaleDenominator ≡ primePowerAtDepth

    crossSectionCardinality :
      Nat

    crossSectionCardinalityIsPrimePlusOne :
      crossSectionCardinality ≡ suc prime

    canonicalNeck :
      Neck.BTCanonicalNeckAnalogue

    canonicalNeckIsAtLaneAndDepth :
      canonicalNeck ≡ Neck.canonicalBTNeckAnalogueAt primeLane depth

    smoothS2CrossSectionPromoted :
      Bool

    smoothS2CrossSectionPromotedIsFalse :
      smoothS2CrossSectionPromoted ≡ false

    epsilonNeckTheoremPromoted :
      Bool

    epsilonNeckTheoremPromotedIsFalse :
      epsilonNeckTheoremPromoted ≡ false

open BTNeckDepthScaleRow public

btNeckDepthScaleRow :
  Neck.BTPrimeLane →
  Nat →
  BTNeckDepthScaleRow
btNeckDepthScaleRow lane d =
  record
    { primeLane =
        lane
    ; prime =
        Neck.primeValue lane
    ; primeIsLaneValue =
        refl
    ; depth =
        d
    ; primePowerAtDepth =
        pow (Neck.primeValue lane) d
    ; primePowerAtDepthIsPow =
        refl
    ; inverseScaleDenominator =
        pow (Neck.primeValue lane) d
    ; inverseScaleDenominatorIsPrimePower =
        refl
    ; crossSectionCardinality =
        suc (Neck.primeValue lane)
    ; crossSectionCardinalityIsPrimePlusOne =
        refl
    ; canonicalNeck =
        Neck.canonicalBTNeckAnalogueAt lane d
    ; canonicalNeckIsAtLaneAndDepth =
        refl
    ; smoothS2CrossSectionPromoted =
        Neck.smoothS2CrossSectionPromoted
          (Neck.canonicalBTNeckAnalogueAt lane d)
    ; smoothS2CrossSectionPromotedIsFalse =
        refl
    ; epsilonNeckTheoremPromoted =
        Neck.epsilonNeckTheoremPromoted
          (Neck.canonicalBTNeckAnalogueAt lane d)
    ; epsilonNeckTheoremPromotedIsFalse =
        refl
    }

p2Depth0Row : BTNeckDepthScaleRow
p2Depth0Row =
  btNeckDepthScaleRow Neck.p2Lane 0

p2Depth1Row : BTNeckDepthScaleRow
p2Depth1Row =
  btNeckDepthScaleRow Neck.p2Lane 1

p2Depth2Row : BTNeckDepthScaleRow
p2Depth2Row =
  btNeckDepthScaleRow Neck.p2Lane 2

p2Depth3Row : BTNeckDepthScaleRow
p2Depth3Row =
  btNeckDepthScaleRow Neck.p2Lane 3

p3Depth0Row : BTNeckDepthScaleRow
p3Depth0Row =
  btNeckDepthScaleRow Neck.p3Lane 0

p3Depth1Row : BTNeckDepthScaleRow
p3Depth1Row =
  btNeckDepthScaleRow Neck.p3Lane 1

p3Depth2Row : BTNeckDepthScaleRow
p3Depth2Row =
  btNeckDepthScaleRow Neck.p3Lane 2

p3Depth3Row : BTNeckDepthScaleRow
p3Depth3Row =
  btNeckDepthScaleRow Neck.p3Lane 3

p7Depth0Row : BTNeckDepthScaleRow
p7Depth0Row =
  btNeckDepthScaleRow Neck.p7Lane 0

p7Depth1Row : BTNeckDepthScaleRow
p7Depth1Row =
  btNeckDepthScaleRow Neck.p7Lane 1

p7Depth2Row : BTNeckDepthScaleRow
p7Depth2Row =
  btNeckDepthScaleRow Neck.p7Lane 2

p7Depth3Row : BTNeckDepthScaleRow
p7Depth3Row =
  btNeckDepthScaleRow Neck.p7Lane 3

canonicalBTNeckDepthScaleRows :
  List BTNeckDepthScaleRow
canonicalBTNeckDepthScaleRows =
  p2Depth0Row
  ∷ p2Depth1Row
  ∷ p2Depth2Row
  ∷ p2Depth3Row
  ∷ p3Depth0Row
  ∷ p3Depth1Row
  ∷ p3Depth2Row
  ∷ p3Depth3Row
  ∷ p7Depth0Row
  ∷ p7Depth1Row
  ∷ p7Depth2Row
  ∷ p7Depth3Row
  ∷ []

canonicalBTNeckDepthScaleRowCountIs12 :
  length canonicalBTNeckDepthScaleRows ≡ 12
canonicalBTNeckDepthScaleRowCountIs12 =
  refl

p2Depth0PrimePowerIs1 : primePowerAtDepth p2Depth0Row ≡ 1
p2Depth0PrimePowerIs1 =
  refl

p2Depth1PrimePowerIs2 : primePowerAtDepth p2Depth1Row ≡ 2
p2Depth1PrimePowerIs2 =
  refl

p2Depth2PrimePowerIs4 : primePowerAtDepth p2Depth2Row ≡ 4
p2Depth2PrimePowerIs4 =
  refl

p2Depth3PrimePowerIs8 : primePowerAtDepth p2Depth3Row ≡ 8
p2Depth3PrimePowerIs8 =
  refl

p3Depth0PrimePowerIs1 : primePowerAtDepth p3Depth0Row ≡ 1
p3Depth0PrimePowerIs1 =
  refl

p3Depth1PrimePowerIs3 : primePowerAtDepth p3Depth1Row ≡ 3
p3Depth1PrimePowerIs3 =
  refl

p3Depth2PrimePowerIs9 : primePowerAtDepth p3Depth2Row ≡ 9
p3Depth2PrimePowerIs9 =
  refl

p3Depth3PrimePowerIs27 : primePowerAtDepth p3Depth3Row ≡ 27
p3Depth3PrimePowerIs27 =
  refl

p7Depth0PrimePowerIs1 : primePowerAtDepth p7Depth0Row ≡ 1
p7Depth0PrimePowerIs1 =
  refl

p7Depth1PrimePowerIs7 : primePowerAtDepth p7Depth1Row ≡ 7
p7Depth1PrimePowerIs7 =
  refl

p7Depth2PrimePowerIs49 : primePowerAtDepth p7Depth2Row ≡ 49
p7Depth2PrimePowerIs49 =
  refl

p7Depth3PrimePowerIs343 : primePowerAtDepth p7Depth3Row ≡ 343
p7Depth3PrimePowerIs343 =
  refl

p2Depth3InverseScaleDenominatorIs8 :
  inverseScaleDenominator p2Depth3Row ≡ 8
p2Depth3InverseScaleDenominatorIs8 =
  refl

p3Depth3InverseScaleDenominatorIs27 :
  inverseScaleDenominator p3Depth3Row ≡ 27
p3Depth3InverseScaleDenominatorIs27 =
  refl

p7Depth3InverseScaleDenominatorIs343 :
  inverseScaleDenominator p7Depth3Row ≡ 343
p7Depth3InverseScaleDenominatorIs343 =
  refl

p2CrossSectionCardinalityIs3 :
  crossSectionCardinality p2Depth2Row ≡ 3
p2CrossSectionCardinalityIs3 =
  refl

p3CrossSectionCardinalityIs4 :
  crossSectionCardinality p3Depth3Row ≡ 4
p3CrossSectionCardinalityIs4 =
  refl

p7CrossSectionCardinalityIs8 :
  crossSectionCardinality p7Depth3Row ≡ 8
p7CrossSectionCardinalityIs8 =
  refl

p2Depth2CanonicalSmoothS2NotPromoted :
  smoothS2CrossSectionPromoted p2Depth2Row ≡ false
p2Depth2CanonicalSmoothS2NotPromoted =
  refl

p3Depth3CanonicalSmoothS2NotPromoted :
  smoothS2CrossSectionPromoted p3Depth3Row ≡ false
p3Depth3CanonicalSmoothS2NotPromoted =
  refl

p7Depth3CanonicalSmoothS2NotPromoted :
  smoothS2CrossSectionPromoted p7Depth3Row ≡ false
p7Depth3CanonicalSmoothS2NotPromoted =
  refl

p2Depth2CanonicalEpsilonNeckNotPromoted :
  epsilonNeckTheoremPromoted p2Depth2Row ≡ false
p2Depth2CanonicalEpsilonNeckNotPromoted =
  refl

p3Depth3CanonicalEpsilonNeckNotPromoted :
  epsilonNeckTheoremPromoted p3Depth3Row ≡ false
p3Depth3CanonicalEpsilonNeckNotPromoted =
  refl

p7Depth3CanonicalEpsilonNeckNotPromoted :
  epsilonNeckTheoremPromoted p7Depth3Row ≡ false
p7Depth3CanonicalEpsilonNeckNotPromoted =
  refl
