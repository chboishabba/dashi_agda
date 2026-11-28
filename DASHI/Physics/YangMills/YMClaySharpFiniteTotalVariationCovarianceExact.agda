module DASHI.Physics.YangMills.YMClaySharpFiniteTotalVariationCovarianceExact where

------------------------------------------------------------------------
-- SOURCE CALIBRATION / DASHI EXTENSION
--
-- Source calibration: Docs/physics/YMClayP0R445TwoMarkJointTVSharpCovarianceAndPhysicalW3RateCut20261124.md
-- in agent/ym-p0-cmp119-r445-master-weld-20261121 at 5407fb27.
-- DASHI extension: finite rational covariance-TV theorem and bad-event
-- 4p corollary. The present module does not claim membrane clustering or
-- endpoint promotion.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _*_; _/_; _≤_; _<_; ∣_∣; NonNegative; nonNegative;
   NonPositive; nonPositive; Positive; positive)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

sumRational : ∀ {A : Set} → List A → (A → ℚ) → ℚ
sumRational [] term = 0ℚ
sumRational (value ∷ values) term = term value + sumRational values term

sumRationalCong :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  (∀ value → left value ≡ right value) →
  sumRational values left ≡ sumRational values right
sumRationalCong [] left right pointwise = refl
sumRationalCong (value ∷ values) left right pointwise =
  cong₂ _+_ (pointwise value) (sumRationalCong values left right pointwise)

Observable : Set → Set
Observable State = State → ℚ

record FiniteRationalProbability (State : Set) : Set₁ where
  field
    states : List State
    weight : State → ℚ
    weightNonnegative : ∀ state → 0ℚ ≤ weight state
    normalized : sumRational states weight ≡ 1ℚ

open FiniteRationalProbability public

expectation :
  ∀ {State} → FiniteRationalProbability State → Observable State → ℚ
expectation probability observable =
  sumRational (states probability)
    (λ state → weight probability state * observable state)

covariance :
  ∀ {State} →
  FiniteRationalProbability State → Observable State → Observable State → ℚ
covariance probability left right =
  expectation probability (λ state → left state * right state)
  - expectation probability left * expectation probability right

twoℚ : ℚ
twoℚ = 1ℚ + 1ℚ

twoNN : 0ℚ ≤ twoℚ
twoNN =
  ℚP.+-mono-≤
    (ℚP.0≤∣p∣ 1ℚ)
    (ℚP.0≤∣p∣ 1ℚ)

twoPositiveProof : 0ℚ < twoℚ
twoPositiveProof = ℚP.positive⁻¹ twoℚ

instance
  twoPositive : Positive twoℚ
  twoPositive = ℚ.positive twoPositiveProof

fourℚ : ℚ
fourℚ = twoℚ + twoℚ

fourNN : 0ℚ ≤ fourℚ
fourNN = ℚP.+-mono-≤ twoNN twoNN

halfℚ : ℚ
halfℚ = + 1 / 2

halfNonnegative : 0ℚ ≤ halfℚ
halfNonnegative = ℚP.nonNegative⁻¹ halfℚ

coeffℚ : ℚ
coeffℚ = halfℚ * halfℚ

coeffNN : 0ℚ ≤ coeffℚ
coeffNN = ℚP.nonNegative⁻¹ coeffℚ

absHalf : ∣ halfℚ ∣ ≡ halfℚ
absHalf = ℚP.0≤p⇒∣p∣≡p halfNonnegative

halfAbsMul : ∀ (value : ℚ) → ∣ halfℚ ∣ * ∣ value ∣ ≡ halfℚ * ∣ value ∣
halfAbsMul value = cong (λ h → h * ∣ value ∣) absHalf

absMulLeft : ∀ {coeff : ℚ} → 0ℚ ≤ coeff →
  ∀ (value : ℚ) → ∣ coeff ∣ * ∣ value ∣ ≡ coeff * ∣ value ∣
absMulLeft {coeff} coeffNN value =
  cong (λ c → c * ∣ value ∣) (ℚP.0≤p⇒∣p∣≡p coeffNN)

oneNonnegative : 0ℚ ≤ 1ℚ
oneNonnegative = ℚP.0≤∣p∣ 1ℚ

record RationalInterval : Set where
  constructor interval
  field
    lower upper : ℚ
    ordered : lower ≤ upper

open RationalInterval public

record LiesIn (value : ℚ) (box : RationalInterval) : Set where
  constructor liesIn
  field
    lowerSound : lower box ≤ value
    upperSound : value ≤ upper box

open LiesIn public

constantInterval : ℚ → RationalInterval
constantInterval value = interval value value ℚP.≤-refl

addNegativeSelf : ∀ (a : ℚ) → a + (- a) ≡ 0ℚ
addNegativeSelf = ℚRing.solve-∀

addNegativeToDifference : ∀ (a b : ℚ) → b + (- a) ≡ b - a
addNegativeToDifference = ℚRing.solve-∀

addNegativeSumLeft : ∀ (a b : ℚ) → a + (- b - a) ≡ - b
addNegativeSumLeft = ℚRing.solve-∀

addNegativeSumRight : ∀ (a b : ℚ) → b + (- b - a) ≡ - a
addNegativeSumRight = ℚRing.solve-∀

subtractNonnegative : ∀ {a b : ℚ} → a ≤ b → 0ℚ ≤ b - a
subtractNonnegative {a} {b} inequality =
  let
    leftEquality : a + (- a) ≡ 0ℚ
    leftEquality = addNegativeSelf a

    rightEquality : b + (- a) ≡ b - a
    rightEquality = addNegativeToDifference a b
  in
  subst
    (λ left → 0ℚ ≤ left)
    rightEquality
    (subst
      (λ left → left ≤ b + (- a))
      leftEquality
      (ℚP.+-mono-≤ inequality ℚP.≤-refl))

negMono : ∀ {a b : ℚ} → a ≤ b → - b ≤ - a
negMono {a} {b} inequality =
  let
    leftEquality : a + (- b - a) ≡ - b
    leftEquality = addNegativeSumLeft a b

    rightEquality : b + (- b - a) ≡ - a
    rightEquality = addNegativeSumRight a b
  in
  subst
    (λ left → - b ≤ left)
    rightEquality
    (subst
      (λ left → left ≤ b + (- b - a))
      leftEquality
      (ℚP.+-mono-≤ inequality ℚP.≤-refl))

negateInterval : RationalInterval → RationalInterval
negateInterval box =
  interval (- upper box) (- lower box) (negMono (ordered box))

addInterval : RationalInterval → RationalInterval → RationalInterval
addInterval left right =
  interval
    (lower left + lower right)
    (upper left + upper right)
    (ℚP.+-mono-≤ (ordered left) (ordered right))

subtractInterval : RationalInterval → RationalInterval → RationalInterval
subtractInterval left right = addInterval left (negateInterval right)

min2 : ℚ → ℚ → ℚ
min2 left right with ℚP.≤-total left right
... | inj₁ _ = left
... | inj₂ _ = right

max2 : ℚ → ℚ → ℚ
max2 left right with ℚP.≤-total left right
... | inj₁ _ = right
... | inj₂ _ = left

min2BelowLeft : ∀ left right → min2 left right ≤ left
min2BelowLeft left right with ℚP.≤-total left right
... | inj₁ _ = ℚP.≤-refl
... | inj₂ rightBelow = rightBelow

min2BelowRight : ∀ left right → min2 left right ≤ right
min2BelowRight left right with ℚP.≤-total left right
... | inj₁ leftBelow = leftBelow
... | inj₂ _ = ℚP.≤-refl

leftBelowMax2 : ∀ left right → left ≤ max2 left right
leftBelowMax2 left right with ℚP.≤-total left right
... | inj₁ leftBelow = leftBelow
... | inj₂ _ = ℚP.≤-refl

rightBelowMax2 : ∀ left right → right ≤ max2 left right
rightBelowMax2 left right with ℚP.≤-total left right
... | inj₁ _ = ℚP.≤-refl
... | inj₂ rightBelow = rightBelow

min4 : ℚ → ℚ → ℚ → ℚ → ℚ
min4 first second third fourth =
  min2 (min2 first second) (min2 third fourth)

max4 : ℚ → ℚ → ℚ → ℚ → ℚ
max4 first second third fourth =
  max2 (max2 first second) (max2 third fourth)

min4BelowFirst : ∀ a b c d → min4 a b c d ≤ a
min4BelowFirst a b c d =
  ℚP.≤-trans
    (min2BelowLeft (min2 a b) (min2 c d))
    (min2BelowLeft a b)

min4BelowSecond : ∀ a b c d → min4 a b c d ≤ b
min4BelowSecond a b c d =
  ℚP.≤-trans
    (min2BelowLeft (min2 a b) (min2 c d))
    (min2BelowRight a b)

min4BelowThird : ∀ a b c d → min4 a b c d ≤ c
min4BelowThird a b c d =
  ℚP.≤-trans
    (min2BelowRight (min2 a b) (min2 c d))
    (min2BelowLeft c d)

min4BelowFourth : ∀ a b c d → min4 a b c d ≤ d
min4BelowFourth a b c d =
  ℚP.≤-trans
    (min2BelowRight (min2 a b) (min2 c d))
    (min2BelowRight c d)

firstBelowMax4 : ∀ a b c d → a ≤ max4 a b c d
firstBelowMax4 a b c d =
  ℚP.≤-trans
    (leftBelowMax2 a b)
    (leftBelowMax2 (max2 a b) (max2 c d))

fourthBelowMax4 : ∀ a b c d → d ≤ max4 a b c d
fourthBelowMax4 a b c d =
  ℚP.≤-trans
    (rightBelowMax2 c d)
    (rightBelowMax2 (max2 a b) (max2 c d))

min2Greatest : ∀ {z x y} → z ≤ x → z ≤ y → z ≤ min2 x y
min2Greatest {z} {x} {y} zx zy with ℚP.≤-total x y
... | inj₁ _ = zx
... | inj₂ _ = zy

max2Least : ∀ {x y z} → x ≤ z → y ≤ z → max2 x y ≤ z
max2Least {x} {y} {z} xz yz with ℚP.≤-total x y
... | inj₁ _ = yz
... | inj₂ _ = xz

min4Greatest : ∀ {z a b c d} →
  z ≤ a → z ≤ b → z ≤ c → z ≤ d → z ≤ min4 a b c d
min4Greatest za zb zc zd =
  min2Greatest (min2Greatest za zb) (min2Greatest zc zd)

max4Least : ∀ {a b c d z} →
  a ≤ z → b ≤ z → c ≤ z → d ≤ z → max4 a b c d ≤ z
max4Least az bz cz dz =
  max2Least (max2Least az bz) (max2Least cz dz)

mulRightNN : ∀ scalar {left right} →
  0ℚ ≤ scalar → left ≤ right → left * scalar ≤ right * scalar
mulRightNN scalar scalarNN inequality =
  let
    instance
      scalarNonnegative : NonNegative scalar
      scalarNonnegative = ℚ.nonNegative scalarNN
  in
  ℚP.*-monoʳ-≤-nonNeg scalar inequality

mulLeftNN : ∀ scalar {left right} →
  0ℚ ≤ scalar → left ≤ right → scalar * left ≤ scalar * right
mulLeftNN scalar scalarNN inequality =
  let
    instance
      scalarNonnegative : NonNegative scalar
      scalarNonnegative = ℚ.nonNegative scalarNN
  in
  ℚP.*-monoˡ-≤-nonNeg scalar inequality

mulRightNP : ∀ scalar {left right} →
  scalar ≤ 0ℚ → left ≤ right → right * scalar ≤ left * scalar
mulRightNP scalar scalarNP inequality =
  let
    instance
      scalarNonpositive : NonPositive scalar
      scalarNonpositive = ℚ.nonPositive scalarNP
  in
  ℚP.*-monoʳ-≤-nonPos scalar inequality

mulLeftNP : ∀ scalar {left right} →
  scalar ≤ 0ℚ → left ≤ right → scalar * right ≤ scalar * left
mulLeftNP scalar scalarNP inequality =
  let
    instance
      scalarNonpositive : NonPositive scalar
      scalarNonpositive = ℚ.nonPositive scalarNP
  in
  ℚP.*-monoˡ-≤-nonPos scalar inequality

caseSum : ∀ {A B C : Set} → A ⊎ B → (A → C) → (B → C) → C
caseSum (inj₁ a) left _ = left a
caseSum (inj₂ b) _ right = right b

negativeEqualsZeroPlusNegative : ∀ (value : ℚ) → - value ≡ 0ℚ + - value
negativeEqualsZeroPlusNegative = ℚRing.solve-∀

addZeroRight : ∀ (value : ℚ) → value + 0ℚ ≡ value
addZeroRight = ℚRing.solve-∀

subtractOneAddOne : ∀ (value : ℚ) → value - 1ℚ + 1ℚ ≡ value
subtractOneAddOne = ℚRing.solve-∀

zeroMultiplyRight : ∀ (value : ℚ) → 0ℚ * value ≡ 0ℚ
zeroMultiplyRight = ℚRing.solve-∀

zeroMultiplyLeft : ∀ (value : ℚ) → value * 0ℚ ≡ 0ℚ
zeroMultiplyLeft = ℚRing.solve-∀

multiplyOneRight : ∀ (value : ℚ) → value * 1ℚ ≡ value
multiplyOneRight = ℚRing.solve-∀

subtractAddSubtract : ∀ (a b c d : ℚ) → (a - b) + (c - d) ≡ (a + c) - (b + d)
subtractAddSubtract = ℚRing.solve-∀

weightedShiftStep : ∀ (weight observed center totalWeighted totalWeight : ℚ) →
  weight * (observed - center) + (totalWeighted - center * totalWeight)
  ≡ (weight * observed + totalWeighted) - center * (weight + totalWeight)
weightedShiftStep = ℚRing.solve-∀

sumRationalNil : ∀ {A : Set} (term : A → ℚ) → sumRational [] term ≡ 0ℚ
sumRationalNil _ = refl

centeredProductStep :
  ∀ (weight observedLeft observedRight leftMean rightMean
       tailLR tailRW tailRL tailWeight : ℚ) →
    weight * ((observedLeft - leftMean) * (observedRight - rightMean))
      + (tailLR - leftMean * tailRW - rightMean * tailRL
        + leftMean * rightMean * tailWeight)
    ≡ (weight * (observedLeft * observedRight) + tailLR)
      - leftMean * (weight * observedRight + tailRW)
      - rightMean * (weight * observedLeft + tailRL)
      + leftMean * rightMean * (weight + tailWeight)
centeredProductStep = ℚRing.solve-∀

centeredProductNil : ∀ (leftMean rightMean : ℚ) →
  0ℚ ≡ 0ℚ - leftMean * 0ℚ - rightMean * 0ℚ + leftMean * rightMean * 0ℚ
centeredProductNil = ℚRing.solve-∀

expectationDifferenceStep : ∀ (leftWeight rightWeight observed tailLeft tailRight : ℚ) →
  (leftWeight * observed + tailLeft) - (rightWeight * observed + tailRight)
  ≡ (leftWeight - rightWeight) * observed + (tailLeft - tailRight)
expectationDifferenceStep = ℚRing.solve-∀

addOneSubtract : ∀ (m : ℚ) → (m + 1ℚ) + - m ≡ 1ℚ
addOneSubtract = ℚRing.solve-∀

subtractSameRight : ∀ (a b c : ℚ) → (a - c) - (b - c) ≡ a - b
subtractSameRight = ℚRing.solve-∀

halfDouble : ∀ (bound : ℚ) → halfℚ * (bound + bound) ≡ bound
halfDouble = ℚRing.solve-∀

negativeOnePlusOne : - 1ℚ + 1ℚ ≡ 0ℚ
negativeOnePlusOne = ℚRing.solve-∀

addCommOne : ∀ (value : ℚ) → 1ℚ + value ≡ value + 1ℚ
addCommOne = ℚRing.solve-∀

halfTwo : halfℚ * (1ℚ + 1ℚ) ≡ 1ℚ
halfTwo = ℚRing.solve-∀

negNeg : ∀ (value : ℚ) → - (- value) ≡ value
negNeg = ℚRing.solve-∀

affineRawNil : ∀ (scale shift : ℚ) → 0ℚ ≡ scale * 0ℚ + shift * 0ℚ
affineRawNil = ℚRing.solve-∀

affineRawStep :
  ∀ (weight observed scale shift tailObserved tailWeight : ℚ) →
    weight * (scale * observed + shift)
      + (scale * tailObserved + shift * tailWeight)
    ≡ scale * (weight * observed + tailObserved)
      + shift * (weight + tailWeight)
affineRawStep = ℚRing.solve-∀

affineProductRawNil :
  ∀ (scale leftShift rightShift : ℚ) →
    0ℚ ≡ scale * scale * 0ℚ
      + scale * leftShift * 0ℚ
      + scale * rightShift * 0ℚ
      + leftShift * rightShift * 0ℚ
affineProductRawNil = ℚRing.solve-∀

affineProductRawStep :
  ∀ (weight left right scale leftShift rightShift
       tailLR tailR tailL tailWeight : ℚ) →
    weight * ((scale * left + leftShift) * (scale * right + rightShift))
      + (scale * scale * tailLR
        + scale * leftShift * tailR
        + scale * rightShift * tailL
        + leftShift * rightShift * tailWeight)
    ≡ scale * scale * (weight * (left * right) + tailLR)
      + scale * leftShift * (weight * right + tailR)
      + scale * rightShift * (weight * left + tailL)
      + leftShift * rightShift * (weight + tailWeight)
affineProductRawStep = ℚRing.solve-∀

scaleSumNil : ∀ (scale : ℚ) → 0ℚ ≡ scale * 0ℚ
scaleSumNil = ℚRing.solve-∀

scaleSumStep :
  ∀ (scale weight tail : ℚ) →
    scale * weight + scale * tail ≡ scale * (weight + tail)
scaleSumStep = ℚRing.solve-∀

sumRationalScale :
  ∀ {State} (states : List State) (weight : State → ℚ) (scale : ℚ) →
    sumRational states (λ state → scale * weight state)
    ≡ scale * sumRational states weight
sumRationalScale [] weight scale = scaleSumNil scale
sumRationalScale (state ∷ states) weight scale
  rewrite sumRationalScale states weight scale =
    scaleSumStep scale (weight state)
      (sumRational states weight)

covarianceAffineAlgebra :
  ∀ (scale leftShift rightShift expLeft expRight expProduct : ℚ) →
    (scale * scale * expProduct
      + scale * leftShift * expRight
      + scale * rightShift * expLeft
      + leftShift * rightShift * 1ℚ)
    - (scale * expLeft + leftShift * 1ℚ)
      * (scale * expRight + rightShift * 1ℚ)
    ≡ scale * scale * (expProduct - expLeft * expRight)
covarianceAffineAlgebra = ℚRing.solve-∀

scaleDifference : ∀ (scale left right : ℚ) →
  scale * left - scale * right ≡ scale * (left - right)
scaleDifference = ℚRing.solve-∀

fourCoeffAbs : ∀ (value : ℚ) → fourℚ * (coeffℚ * value) ≡ value
fourCoeffAbs = ℚRing.solve-∀

covarianceGapAlgebra :
  ∀ (leftMean rightMean leftRightMean rightRightMean
       leftProduct rightProduct : ℚ) →
    (leftProduct - leftRightMean * leftMean)
      - (rightProduct - rightRightMean * rightMean)
    ≡ halfℚ *
      ( ((leftProduct
          - leftMean * leftRightMean
          - leftRightMean * leftMean
          + leftMean * leftRightMean)
        - (rightProduct
          - leftMean * rightRightMean
          - leftRightMean * rightMean
          + leftMean * leftRightMean))
      + ((leftProduct
          - rightMean * leftRightMean
          - rightRightMean * leftMean
          + rightMean * rightRightMean)
        - (rightProduct
          - rightMean * rightRightMean
          - rightRightMean * rightMean
          + rightMean * rightRightMean)) )
covarianceGapAlgebra = ℚRing.solve-∀

productNN : ∀ left right →
  0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
productNN left right leftNN rightNN =
  subst
    (λ lower → lower ≤ left * right)
    (zeroMultiplyRight right)
    (mulRightNN right rightNN leftNN)

productNP : ∀ left right →
  left ≤ 0ℚ → 0ℚ ≤ right → left * right ≤ 0ℚ
productNP left right leftNP rightNN =
  subst
    (λ upper → left * right ≤ upper)
    (zeroMultiplyRight right)
    (mulRightNN right rightNN leftNP)

productPN : ∀ left right →
  0ℚ ≤ left → right ≤ 0ℚ → left * right ≤ 0ℚ
productPN left right leftNN rightNP =
  subst
    (λ upper → left * right ≤ upper)
    (zeroMultiplyLeft left)
    (mulLeftNN left leftNN rightNP)

productPP : ∀ left right →
  left ≤ 0ℚ → right ≤ 0ℚ → 0ℚ ≤ left * right
productPP left right leftNP rightNP =
  subst
    (λ lower → lower ≤ left * right)
    (zeroMultiplyRight right)
    (mulRightNP right rightNP leftNP)

multiplyInterval : RationalInterval → RationalInterval → RationalInterval
multiplyInterval left right =
  let
    c00 = lower left * lower right
    c01 = lower left * upper right
    c10 = upper left * lower right
    c11 = upper left * upper right
  in
  interval
    (min4 c00 c01 c10 c11)
    (max4 c00 c01 c10 c11)
    (ℚP.≤-trans
      (min4BelowFirst c00 c01 c10 c11)
      (firstBelowMax4 c00 c01 c10 c11))

unitInterval : RationalInterval
unitInterval = interval 0ℚ 1ℚ oneNonnegative

liesUnit : ∀ {value : ℚ} → 0ℚ ≤ value → value ≤ 1ℚ → LiesIn value unitInterval
liesUnit valueNN value≤1 = liesIn valueNN value≤1

liesConstant : ∀ (value : ℚ) → LiesIn value (constantInterval value)
liesConstant value = liesIn ℚP.≤-refl ℚP.≤-refl

addZeroLeftNN : ∀ (c slack : ℚ) → 0ℚ ≤ slack → c ≤ c + slack
addZeroLeftNN c slack slackNN =
  subst (λ left → left ≤ c + slack) (addZeroRight c)
    (ℚP.+-mono-≤ (ℚP.≤-refl {c}) slackNN)

lowerBySlack :
  ∀ {c d slack : ℚ} → 0ℚ ≤ slack → (c - 1ℚ) + slack ≡ d →
  c - 1ℚ ≤ d
lowerBySlack {c} {d} {slack} slackNN equality =
  subst (λ upper → c - 1ℚ ≤ upper) equality
    (addZeroLeftNN (c - 1ℚ) slack slackNN)

cornerBelowMinPlusOne :
  ∀ {c m : ℚ} → c - 1ℚ ≤ m → c ≤ m + 1ℚ
cornerBelowMinPlusOne {c} {m} below =
  let
    shifted : (c - 1ℚ) + 1ℚ ≤ m + 1ℚ
    shifted = ℚP.+-mono-≤ below ℚP.≤-refl
  in
  subst (λ left → left ≤ m + 1ℚ) (subtractOneAddOne c) shifted

c00Below00 : ∀ (a b : ℚ) → ((0ℚ + - a) * (0ℚ + - b) - 1ℚ) + 1ℚ ≡ (0ℚ + - a) * (0ℚ + - b)
c00Below00 = ℚRing.solve-∀

c00Below01 : ∀ (a b : ℚ) →
  ((0ℚ + - a) * (0ℚ + - b) - 1ℚ) + (1ℚ + - a) ≡ (0ℚ + - a) * (1ℚ + - b)
c00Below01 = ℚRing.solve-∀

c00Below10 : ∀ (a b : ℚ) →
  ((0ℚ + - a) * (0ℚ + - b) - 1ℚ) + (1ℚ + - b) ≡ (1ℚ + - a) * (0ℚ + - b)
c00Below10 = ℚRing.solve-∀

c00Below11 : ∀ (a b : ℚ) →
  ((0ℚ + - a) * (0ℚ + - b) - 1ℚ) + ((1ℚ + - a) + (1ℚ + - b)) ≡ (1ℚ + - a) * (1ℚ + - b)
c00Below11 = ℚRing.solve-∀

c01Below00 : ∀ (a b : ℚ) →
  ((0ℚ + - a) * (1ℚ + - b) - 1ℚ) + (1ℚ + a) ≡ (0ℚ + - a) * (0ℚ + - b)
c01Below00 = ℚRing.solve-∀

c01Below01 : ∀ (a b : ℚ) → ((0ℚ + - a) * (1ℚ + - b) - 1ℚ) + 1ℚ ≡ (0ℚ + - a) * (1ℚ + - b)
c01Below01 = ℚRing.solve-∀

c01Below10 : ∀ (a b : ℚ) →
  ((0ℚ + - a) * (1ℚ + - b) - 1ℚ) + (a + (1ℚ + - b)) ≡ (1ℚ + - a) * (0ℚ + - b)
c01Below10 = ℚRing.solve-∀

c01Below11 : ∀ (a b : ℚ) →
  ((0ℚ + - a) * (1ℚ + - b) - 1ℚ) + (1ℚ + (1ℚ + - b)) ≡ (1ℚ + - a) * (1ℚ + - b)
c01Below11 = ℚRing.solve-∀

c10Below00 : ∀ (a b : ℚ) →
  ((1ℚ + - a) * (0ℚ + - b) - 1ℚ) + (1ℚ + b) ≡ (0ℚ + - a) * (0ℚ + - b)
c10Below00 = ℚRing.solve-∀

c10Below01 : ∀ (a b : ℚ) →
  ((1ℚ + - a) * (0ℚ + - b) - 1ℚ) + (b + (1ℚ + - a)) ≡ (0ℚ + - a) * (1ℚ + - b)
c10Below01 = ℚRing.solve-∀

c10Below10 : ∀ (a b : ℚ) → ((1ℚ + - a) * (0ℚ + - b) - 1ℚ) + 1ℚ ≡ (1ℚ + - a) * (0ℚ + - b)
c10Below10 = ℚRing.solve-∀

c10Below11 : ∀ (a b : ℚ) →
  ((1ℚ + - a) * (0ℚ + - b) - 1ℚ) + (1ℚ + (1ℚ + - a)) ≡ (1ℚ + - a) * (1ℚ + - b)
c10Below11 = ℚRing.solve-∀

c11Below00 : ∀ (a b : ℚ) →
  ((1ℚ + - a) * (1ℚ + - b) - 1ℚ) + (a + b) ≡ (0ℚ + - a) * (0ℚ + - b)
c11Below00 = ℚRing.solve-∀

c11Below01 : ∀ (a b : ℚ) →
  ((1ℚ + - a) * (1ℚ + - b) - 1ℚ) + b ≡ (0ℚ + - a) * (1ℚ + - b)
c11Below01 = ℚRing.solve-∀

c11Below10 : ∀ (a b : ℚ) →
  ((1ℚ + - a) * (1ℚ + - b) - 1ℚ) + a ≡ (1ℚ + - a) * (0ℚ + - b)
c11Below10 = ℚRing.solve-∀

c11Below11 : ∀ (a b : ℚ) → ((1ℚ + - a) * (1ℚ + - b) - 1ℚ) + 1ℚ ≡ (1ℚ + - a) * (1ℚ + - b)
c11Below11 = ℚRing.solve-∀

fourCornerWidth :
  ∀ (a b : ℚ) →
  0ℚ ≤ a → a ≤ 1ℚ → 0ℚ ≤ b → b ≤ 1ℚ →
  max4
    ((0ℚ + - a) * (0ℚ + - b))
    ((0ℚ + - a) * (1ℚ + - b))
    ((1ℚ + - a) * (0ℚ + - b))
    ((1ℚ + - a) * (1ℚ + - b))
  ≤
  min4
    ((0ℚ + - a) * (0ℚ + - b))
    ((0ℚ + - a) * (1ℚ + - b))
    ((1ℚ + - a) * (0ℚ + - b))
    ((1ℚ + - a) * (1ℚ + - b))
  + 1ℚ
fourCornerWidth a b aNN a≤1 bNN b≤1 =
  let
    oneMinusA : 0ℚ ≤ 1ℚ + - a
    oneMinusA = subtractNonnegative a≤1

    oneMinusB : 0ℚ ≤ 1ℚ + - b
    oneMinusB = subtractNonnegative b≤1

    oneA : 0ℚ ≤ 1ℚ + a
    oneA = ℚP.+-mono-≤ oneNonnegative aNN

    oneB : 0ℚ ≤ 1ℚ + b
    oneB = ℚP.+-mono-≤ oneNonnegative bNN

    aOneB : 0ℚ ≤ a + (1ℚ + - b)
    aOneB = ℚP.+-mono-≤ aNN oneMinusB

    bOneA : 0ℚ ≤ b + (1ℚ + - a)
    bOneA = ℚP.+-mono-≤ bNN oneMinusA

    oneOneB : 0ℚ ≤ 1ℚ + (1ℚ + - b)
    oneOneB = ℚP.+-mono-≤ oneNonnegative oneMinusB

    oneOneA : 0ℚ ≤ 1ℚ + (1ℚ + - a)
    oneOneA = ℚP.+-mono-≤ oneNonnegative oneMinusA

    aB : 0ℚ ≤ a + b
    aB = ℚP.+-mono-≤ aNN bNN

    c00 : ℚ
    c00 = (0ℚ + - a) * (0ℚ + - b)

    c01 : ℚ
    c01 = (0ℚ + - a) * (1ℚ + - b)

    c10 : ℚ
    c10 = (1ℚ + - a) * (0ℚ + - b)

    c11 : ℚ
    c11 = (1ℚ + - a) * (1ℚ + - b)

    m : ℚ
    m = min4 c00 c01 c10 c11

    c00Below : c00 - 1ℚ ≤ m
    c00Below = min4Greatest
      (lowerBySlack {c = c00}
        {d = (0ℚ + - a) * (0ℚ + - b)} {slack = 1ℚ}
        oneNonnegative (c00Below00 a b))
      (lowerBySlack {c = c00}
        {d = (0ℚ + - a) * (1ℚ + - b)} {slack = 1ℚ + - a}
        oneMinusA (c00Below01 a b))
      (lowerBySlack {c = c00}
        {d = (1ℚ + - a) * (0ℚ + - b)} {slack = 1ℚ + - b}
        oneMinusB (c00Below10 a b))
      (lowerBySlack {c = c00}
        {d = (1ℚ + - a) * (1ℚ + - b)}
        {slack = (1ℚ + - a) + (1ℚ + - b)}
        (ℚP.+-mono-≤ oneMinusA oneMinusB) (c00Below11 a b))

    c01Below : c01 - 1ℚ ≤ m
    c01Below = min4Greatest
      (lowerBySlack {c = c01}
        {d = (0ℚ + - a) * (0ℚ + - b)} {slack = 1ℚ + a}
        oneA (c01Below00 a b))
      (lowerBySlack {c = c01}
        {d = (0ℚ + - a) * (1ℚ + - b)} {slack = 1ℚ}
        oneNonnegative (c01Below01 a b))
      (lowerBySlack {c = c01}
        {d = (1ℚ + - a) * (0ℚ + - b)} {slack = a + (1ℚ + - b)}
        aOneB (c01Below10 a b))
      (lowerBySlack {c = c01}
        {d = (1ℚ + - a) * (1ℚ + - b)} {slack = 1ℚ + (1ℚ + - b)}
        oneOneB (c01Below11 a b))

    c10Below : c10 - 1ℚ ≤ m
    c10Below = min4Greatest
      (lowerBySlack {c = c10}
        {d = (0ℚ + - a) * (0ℚ + - b)} {slack = 1ℚ + b}
        oneB (c10Below00 a b))
      (lowerBySlack {c = c10}
        {d = (0ℚ + - a) * (1ℚ + - b)} {slack = b + (1ℚ + - a)}
        bOneA (c10Below01 a b))
      (lowerBySlack {c = c10}
        {d = (1ℚ + - a) * (0ℚ + - b)} {slack = 1ℚ}
        oneNonnegative (c10Below10 a b))
      (lowerBySlack {c = c10}
        {d = (1ℚ + - a) * (1ℚ + - b)} {slack = 1ℚ + (1ℚ + - a)}
        oneOneA (c10Below11 a b))

    c11Below : c11 - 1ℚ ≤ m
    c11Below = min4Greatest
      (lowerBySlack {c = c11}
        {d = (0ℚ + - a) * (0ℚ + - b)} {slack = a + b}
        aB (c11Below00 a b))
      (lowerBySlack {c = c11}
        {d = (0ℚ + - a) * (1ℚ + - b)} {slack = b}
        bNN (c11Below01 a b))
      (lowerBySlack {c = c11}
        {d = (1ℚ + - a) * (0ℚ + - b)} {slack = a}
        aNN (c11Below10 a b))
      (lowerBySlack {c = c11}
        {d = (1ℚ + - a) * (1ℚ + - b)} {slack = 1ℚ}
        oneNonnegative (c11Below11 a b))
  in
  max4Least
    {a = c00} {b = c01} {c = c10} {d = c11} {z = m + 1ℚ}
    (cornerBelowMinPlusOne c00Below)
    (cornerBelowMinPlusOne c01Below)
    (cornerBelowMinPlusOne c10Below)
    (cornerBelowMinPlusOne c11Below)

centeredBox : ℚ → ℚ → RationalInterval
centeredBox a b =
  multiplyInterval
    (subtractInterval unitInterval (constantInterval a))
    (subtractInterval unitInterval (constantInterval b))

centeredProductLiesInBox :
  ∀ {a b x y : ℚ} →
  0ℚ ≤ a → a ≤ 1ℚ → 0ℚ ≤ b → b ≤ 1ℚ →
  0ℚ ≤ x → x ≤ 1ℚ → 0ℚ ≤ y → y ≤ 1ℚ →
  LiesIn ((x - a) * (y - b)) (centeredBox a b)
centeredProductLiesInBox {a} {b} {x} {y}
    aNN a≤1 bNN b≤1 xNN x≤1 yNN y≤1 =
  let
    c00 : ℚ
    c00 = (0ℚ + - a) * (0ℚ + - b)

    c01 : ℚ
    c01 = (0ℚ + - a) * (1ℚ + - b)

    c10 : ℚ
    c10 = (1ℚ + - a) * (0ℚ + - b)

    c11 : ℚ
    c11 = (1ℚ + - a) * (1ℚ + - b)

    oneMinusA : 0ℚ ≤ 1ℚ + - a
    oneMinusA = subtractNonnegative a≤1

    oneMinusB : 0ℚ ≤ 1ℚ + - b
    oneMinusB = subtractNonnegative b≤1

    negA : (0ℚ + - a) ≤ 0ℚ
    negA =
      subst (λ left → left ≤ 0ℚ)
        (negativeEqualsZeroPlusNegative a)
        (negMono aNN)

    negB : (0ℚ + - b) ≤ 0ℚ
    negB =
      subst (λ left → left ≤ 0ℚ)
        (negativeEqualsZeroPlusNegative b)
        (negMono bNN)

    xDif≤oneMinusA : (x + - a) ≤ (1ℚ + - a)
    xDif≤oneMinusA = ℚP.+-mono-≤ x≤1 ℚP.≤-refl

    yDif≤oneMinusB : (y + - b) ≤ (1ℚ + - b)
    yDif≤oneMinusB = ℚP.+-mono-≤ y≤1 ℚP.≤-refl

    negA≤xDif : (0ℚ + - a) ≤ (x + - a)
    negA≤xDif = ℚP.+-mono-≤ xNN ℚP.≤-refl

    negB≤yDif : (0ℚ + - b) ≤ (y + - b)
    negB≤yDif = ℚP.+-mono-≤ yNN ℚP.≤-refl

    lowerBox≤Zero : lower (centeredBox a b) ≤ 0ℚ
    lowerBox≤Zero =
      ℚP.≤-trans
        (min4BelowSecond c00 c01 c10 c11)
        (productNP (0ℚ + - a) (1ℚ + - b) negA oneMinusB)

    zero≤UpperBox : 0ℚ ≤ upper (centeredBox a b)
    zero≤UpperBox =
      ℚP.≤-trans
        (productNN (1ℚ + - a) (1ℚ + - b) oneMinusA oneMinusB)
        (fourthBelowMax4 c00 c01 c10 c11)

    lowerFromZero : 0ℚ ≤ (x + - a) * (y + - b) →
      lower (centeredBox a b) ≤ (x + - a) * (y + - b)
    lowerFromZero = ℚP.≤-trans lowerBox≤Zero

    upperFromZero : (x + - a) * (y + - b) ≤ 0ℚ →
      (x + - a) * (y + - b) ≤ upper (centeredBox a b)
    upperFromZero product≤Zero =
      ℚP.≤-trans product≤Zero zero≤UpperBox
  in
  caseSum (ℚP.≤-total 0ℚ (x + - a))
    (λ xDifNN →
      caseSum (ℚP.≤-total 0ℚ (y + - b))
        (λ yDifNN →
          liesIn
            (lowerFromZero
              (productNN (x + - a) (y + - b) xDifNN yDifNN))
            (ℚP.≤-trans
              (ℚP.≤-trans
                (mulRightNN (y + - b) yDifNN xDif≤oneMinusA)
                (mulLeftNN (1ℚ + - a) oneMinusA yDif≤oneMinusB))
              (fourthBelowMax4 c00 c01 c10 c11)))
        (λ yDifNP →
          liesIn
            (ℚP.≤-trans
              (min4BelowThird c00 c01 c10 c11)
              (ℚP.≤-trans
                (mulLeftNN (1ℚ + - a) oneMinusA negB≤yDif)
                (mulRightNP (y + - b) yDifNP xDif≤oneMinusA)))
            (upperFromZero
              (productPN (x + - a) (y + - b) xDifNN yDifNP))))
    (λ xDifNP →
      caseSum (ℚP.≤-total 0ℚ (y + - b))
        (λ yDifNN →
          liesIn
            (ℚP.≤-trans
              (min4BelowSecond c00 c01 c10 c11)
              (ℚP.≤-trans
                (mulRightNN (1ℚ + - b) oneMinusB negA≤xDif)
                (mulLeftNP (x + - a) xDifNP yDif≤oneMinusB)))
            (upperFromZero
              (productNP (x + - a) (y + - b) xDifNP yDifNN)))
        (λ yDifNP →
          liesIn
            (lowerFromZero
              (productPP (x + - a) (y + - b) xDifNP yDifNP))
            (ℚP.≤-trans
              (ℚP.≤-trans
                (mulRightNP (y + - b) yDifNP negA≤xDif)
                (mulLeftNP (0ℚ + - a) negA negB≤yDif))
              (firstBelowMax4 c00 c01 c10 c11))))

centeredBoxWidth :
  ∀ (a b : ℚ) →
  0ℚ ≤ a → a ≤ 1ℚ → 0ℚ ≤ b → b ≤ 1ℚ →
  upper (centeredBox a b) ≤ lower (centeredBox a b) + 1ℚ
centeredBoxWidth a b aNN a≤1 bNN b≤1 =
  fourCornerWidth a b aNN a≤1 bNN b≤1

sumRationalNonnegative :
  ∀ {A : Set} (values : List A) (term : A → ℚ) →
  (∀ value → 0ℚ ≤ term value) → 0ℚ ≤ sumRational values term
sumRationalNonnegative [] term pointwise = ℚP.≤-refl
sumRationalNonnegative (value ∷ values) term pointwise =
  ℚP.+-mono-≤ (pointwise value)
    (sumRationalNonnegative values term pointwise)

sumRationalMono :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  (∀ value → left value ≤ right value) →
  sumRational values left ≤ sumRational values right
sumRationalMono [] left right pointwise = ℚP.≤-refl
sumRationalMono (value ∷ values) left right pointwise =
  ℚP.+-mono-≤ (pointwise value)
    (sumRationalMono values left right pointwise)

sumRationalSub :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  sumRational values (λ value → left value - right value)
  ≡ sumRational values left - sumRational values right
sumRationalSub [] left right = ℚRing.solve-∀
sumRationalSub (value ∷ values) left right
  rewrite sumRationalSub values left right =
    subtractAddSubtract (left value) (right value)
      (sumRational values left) (sumRational values right)

expectationShiftRaw :
  ∀ {State} (states : List State) (weight observable : State → ℚ) (center : ℚ) →
  sumRational states (λ state → weight state * (observable state - center))
  ≡ sumRational states (λ state → weight state * observable state)
    - center * sumRational states weight
expectationShiftRaw [] weight observable center
  rewrite zeroMultiplyLeft center = ℚRing.solve-∀
expectationShiftRaw (state ∷ states) weight observable center
  rewrite expectationShiftRaw states weight observable center =
    weightedShiftStep
      (weight state) (observable state) center
      (sumRational states (λ s → weight s * observable s))
      (sumRational states weight)

expectationShift :
  ∀ {State}
    (probability : FiniteRationalProbability State)
    (observable : Observable State) (center : ℚ) →
  expectation probability (λ state → observable state - center)
  ≡ expectation probability observable - center
expectationShift probability observable center
  rewrite expectationShiftRaw
      (states probability)
      (weight probability)
      observable center
      | normalized probability
      | multiplyOneRight center = ℚRing.solve-∀

expectationCenteredProductRaw :
  ∀ {State} (states : List State)
    (weight left right : State → ℚ) (leftMean rightMean : ℚ) →
  sumRational states
    (λ state → weight state * ((left state - leftMean) * (right state - rightMean)))
  ≡ sumRational states (λ state → weight state * (left state * right state))
    - leftMean * sumRational states (λ state → weight state * right state)
    - rightMean * sumRational states (λ state → weight state * left state)
    + leftMean * rightMean * sumRational states weight
expectationCenteredProductRaw [] weight left right leftMean rightMean =
  centeredProductNil leftMean rightMean
expectationCenteredProductRaw (state ∷ states) weight left right leftMean rightMean
  rewrite expectationCenteredProductRaw states weight left right leftMean rightMean =
    centeredProductStep
      (weight state) (left state) (right state) leftMean rightMean
      (sumRational states (λ s → weight s * (left s * right s)))
      (sumRational states (λ s → weight s * right s))
      (sumRational states (λ s → weight s * left s))
      (sumRational states weight)

expectationCenteredProduct :
  ∀ {State}
    (probability : FiniteRationalProbability State)
    (left right : Observable State) (leftMean rightMean : ℚ) →
  expectation probability
    (λ state → (left state - leftMean) * (right state - rightMean))
  ≡ expectation probability (λ state → left state * right state)
    - leftMean * expectation probability right
    - rightMean * expectation probability left
    + leftMean * rightMean
expectationCenteredProduct probability left right leftMean rightMean
  rewrite expectationCenteredProductRaw
      (states probability)
      (weight probability)
      left right leftMean rightMean
      | normalized probability
      | multiplyOneRight (leftMean * rightMean) = ℚRing.solve-∀

expectationNonnegative :
  ∀ {State}
    (probability : FiniteRationalProbability State)
    (observable : Observable State) →
  (∀ state → 0ℚ ≤ observable state) →
  0ℚ ≤ expectation probability observable
expectationNonnegative probability observable observableNN =
  sumRationalNonnegative
    (states probability)
    (λ state → weight probability state * observable state)
    (λ state →
      productNN
        (weight probability state)
        (observable state)
        (weightNonnegative probability state)
        (observableNN state))

expectationBelowOne :
  ∀ {State}
    (probability : FiniteRationalProbability State)
    (observable : Observable State) →
  (∀ state → 0ℚ ≤ observable state) →
  (∀ state → observable state ≤ 1ℚ) →
  expectation probability observable ≤ 1ℚ
expectationBelowOne probability observable observableNN observable≤1 =
  let
    raised :
      sumRational
        (states probability)
        (λ state → weight probability state * observable state)
      ≤ sumRational
        (states probability)
        (λ state → weight probability state * 1ℚ)
    raised =
      sumRationalMono
        (states probability)
        (λ state → weight probability state * observable state)
        (λ state → weight probability state * 1ℚ)
        (λ state →
          mulLeftNN
            (weight probability state)
            (weightNonnegative probability state)
            (observable≤1 state))

    massOne :
      sumRational
        (states probability)
        (λ state → weight probability state * 1ℚ)
      ≡ 1ℚ
    massOne =
      trans
        (sumRationalCong
          (states probability)
          (λ state → weight probability state * 1ℚ)
          (weight probability)
          (λ state → ℚP.*-identityʳ (weight probability state)))
        (normalized probability)
  in
  subst (λ upper → expectation probability observable ≤ upper) massOne raised

record FiniteRationalLawPair (State : Set) : Set₁ where
  field
    left : FiniteRationalProbability State
    right : FiniteRationalProbability State

open FiniteRationalLawPair public

LocalTotalVariation :
  ∀ {State} → FiniteRationalLawPair State → ℚ → Set
LocalTotalVariation pair bound =
  ∀ observable →
  (∀ state → 0ℚ ≤ observable state) →
  (∀ state → observable state ≤ 1ℚ) →
  ∣ expectation (left pair) observable
    - expectation (right pair) observable ∣ ≤ bound

sumRationalAbsBound :
  ∀ {A : Set} (values : List A) (term majorant : A → ℚ) →
  (∀ value → 0ℚ ≤ majorant value) →
  (∀ value → ∣ term value ∣ ≤ majorant value) →
  ∣ sumRational values term ∣ ≤ sumRational values majorant
sumRationalAbsBound [] term majorant majorantNN termBound =
  subst (λ left → left ≤ 0ℚ)
    (sym (ℚP.0≤p⇒∣p∣≡p ℚP.≤-refl))
    ℚP.≤-refl
sumRationalAbsBound (value ∷ values) term majorant majorantNN termBound =
  ℚP.≤-trans
    (ℚP.∣p+q∣≤∣p∣+∣q∣
      (term value) (sumRational values term))
    (ℚP.+-mono-≤
      (termBound value)
      (sumRationalAbsBound values term majorant majorantNN termBound))

expectationDifferenceRaw :
  ∀ {State} (states : List State)
    (leftWeight rightWeight observable : State → ℚ) →
  sumRational states (λ state → leftWeight state * observable state)
  - sumRational states (λ state → rightWeight state * observable state)
  ≡ sumRational states
      (λ state → (leftWeight state - rightWeight state) * observable state)
expectationDifferenceRaw [] leftWeight rightWeight observable = ℚRing.solve-∀
expectationDifferenceRaw (state ∷ states) leftWeight rightWeight observable
  rewrite sym (expectationDifferenceRaw states leftWeight rightWeight observable) =
    expectationDifferenceStep
      (leftWeight state) (rightWeight state) (observable state)
      (sumRational states (λ s → leftWeight s * observable s))
      (sumRational states (λ s → rightWeight s * observable s))

record BadEventDecomposition (State : Set) : Set₁ where
  field
    lawPair : FiniteRationalLawPair State
    badMass : ℚ
    badMassNonnegative : 0ℚ ≤ badMass
    badWeight : State → ℚ
    badWeightNonnegative : ∀ state → 0ℚ ≤ badWeight state
    badMassIsSum :
      sumRational (states (left lawPair)) badWeight ≡ badMass
    statesAgree :
      states (left lawPair) ≡ states (right lawPair)
    weightDifferenceBound :
      ∀ state →
      ∣ weight (left lawPair) state
        - weight (right lawPair) state ∣
      ≤ badWeight state

open BadEventDecomposition public

badEventLocalTotalVariation :
  ∀ {State} (decomposition : BadEventDecomposition State) →
  LocalTotalVariation
    (lawPair decomposition)
    (badMass decomposition)
badEventLocalTotalVariation decomposition observable observableNN observable≤1 =
  let
    pair = lawPair decomposition
    leftStates = states (left pair)
    rightStates = states (right pair)

    leftExpectationRaw :
      expectation (left pair) observable
      ≡ sumRational leftStates
          (λ state → weight (left pair) state * observable state)
    leftExpectationRaw = refl

    rightExpectationRaw :
      expectation (right pair) observable
      ≡ sumRational leftStates
          (λ state → weight (right pair) state * observable state)
    rightExpectationRaw =
      trans
        refl
        (cong
          (λ states → sumRational states
            (λ state → weight (right pair) state * observable state))
          (sym (statesAgree decomposition)))

    differenceRaw :
      expectation (left pair) observable
      - expectation (right pair) observable
      ≡ sumRational leftStates
          (λ state →
            (weight (left pair) state
              - weight (right pair) state)
            * observable state)
    differenceRaw =
      trans
        (cong₂ _-_ leftExpectationRaw rightExpectationRaw)
        (expectationDifferenceRaw
          leftStates
          (weight (left pair))
          (weight (right pair))
          observable)

    termBound :
      ∀ state →
      ∣ (weight (left pair) state
          - weight (right pair) state)
        * observable state ∣
      ≤ badWeight decomposition state
    termBound state =
      let
        productBound =
          ℚP.∣p*q∣≡∣p∣*∣q∣
            (weight (left pair) state
              - weight (right pair) state)
            (observable state)

        observableAbs : ∣ observable state ∣ ≡ observable state
        observableAbs = ℚP.0≤p⇒∣p∣≡p (observableNN state)

        differenceAbsNN :
          0ℚ ≤ ∣ weight (left pair) state
            - weight (right pair) state ∣
        differenceAbsNN =
          ℚP.0≤∣p∣
            (weight (left pair) state
              - weight (right pair) state)

        observableAbs≤1 : ∣ observable state ∣ ≤ 1ℚ
        observableAbs≤1 =
          subst (λ left → left ≤ 1ℚ)
            (sym observableAbs)
            (observable≤1 state)

        multiplied =
          mulLeftNN
            (∣ weight (left pair) state
                - weight (right pair) state ∣)
            differenceAbsNN
            observableAbs≤1

        adjusted =
          subst (λ lower →
            lower
            ≤ ∣ weight (left pair) state
                - weight (right pair) state ∣ * 1ℚ)
            (sym productBound)
            multiplied

        badBound =
          weightDifferenceBound decomposition state
      in
      ℚP.≤-trans adjusted
        (subst
          (λ upper → upper ≤ badWeight decomposition state)
          (sym
            (ℚP.*-identityʳ
              (∣ weight (left pair) state
                - weight (right pair) state ∣)))
          badBound)

    summedBound =
      sumRationalAbsBound
        leftStates
        (λ state →
          (weight (left pair) state
            - weight (right pair) state)
          * observable state)
        (badWeight decomposition)
        (badWeightNonnegative decomposition)
        termBound
  in
  subst
    (λ difference → ∣ difference ∣ ≤ badMass decomposition)
    (sym differenceRaw)
    (subst
      (λ upper →
        ∣ sumRational leftStates
            (λ state →
              (weight (left pair) state
                - weight (right pair) state)
              * observable state) ∣
        ≤ upper)
      (badMassIsSum decomposition)
      summedBound)

centeredShiftNonnegative :
  ∀ {value m : ℚ} → m ≤ value → 0ℚ ≤ value - m
centeredShiftNonnegative {value} {m} below = subtractNonnegative below

subtractBelowOne :
  ∀ {value m : ℚ} → value ≤ m + 1ℚ → value - m ≤ 1ℚ
subtractBelowOne {value} {m} below =
  subst (λ upper → value - m ≤ upper)
    (addOneSubtract m)
    (ℚP.+-mono-≤ below ℚP.≤-refl)

centeredDifferenceBound :
  ∀ {State}
    (pair : FiniteRationalLawPair State) {bound : ℚ} →
  0ℚ ≤ bound →
  LocalTotalVariation pair bound →
  (leftObservable rightObservable : Observable State) →
  (∀ state → 0ℚ ≤ leftObservable state) →
  (∀ state → leftObservable state ≤ 1ℚ) →
  (∀ state → 0ℚ ≤ rightObservable state) →
  (∀ state → rightObservable state ≤ 1ℚ) →
  (leftMean rightMean : ℚ) →
  0ℚ ≤ leftMean → leftMean ≤ 1ℚ →
  0ℚ ≤ rightMean → rightMean ≤ 1ℚ →
  ∣ expectation (left pair)
      (λ state → (leftObservable state - leftMean)
        * (rightObservable state - rightMean))
    - expectation (right pair)
      (λ state → (leftObservable state - leftMean)
        * (rightObservable state - rightMean)) ∣
  ≤ bound
centeredDifferenceBound pair {bound} boundNN tv
    leftObservable rightObservable
    leftNN left≤1 rightNN right≤1
    leftMean rightMean leftMeanNN leftMean≤1 rightMeanNN rightMean≤1 =
  let
    box = centeredBox leftMean rightMean
    lowerEnd = lower box
    upperEnd = upper box

    upperGap : upper box ≤ lower box + 1ℚ
    upperGap = centeredBoxWidth leftMean rightMean
      leftMeanNN leftMean≤1 rightMeanNN rightMean≤1

    productIn :
      ∀ state → LiesIn
        ((leftObservable state - leftMean) * (rightObservable state - rightMean))
        box
    productIn state =
      centeredProductLiesInBox
        {a = leftMean} {b = rightMean}
        {x = leftObservable state} {y = rightObservable state}
        leftMeanNN leftMean≤1 rightMeanNN rightMean≤1
        (leftNN state) (left≤1 state) (rightNN state) (right≤1 state)

    shiftedObservable : Observable _
    shiftedObservable state =
      (leftObservable state - leftMean) * (rightObservable state - rightMean)
      - lowerEnd

    shiftedNN : ∀ state → 0ℚ ≤ shiftedObservable state
    shiftedNN state =
      centeredShiftNonnegative
        {value = (leftObservable state - leftMean)
          * (rightObservable state - rightMean)}
        {m = lowerEnd}
        (lowerSound (productIn state))

    shifted≤1 : ∀ state → shiftedObservable state ≤ 1ℚ
    shifted≤1 state =
      subtractBelowOne
        {value = (leftObservable state - leftMean)
          * (rightObservable state - rightMean)}
        {m = lowerEnd}
        (ℚP.≤-trans
          (upperSound (productIn state))
          upperGap)

    rawBound :
      ∣ expectation (left pair) shiftedObservable
        - expectation (right pair) shiftedObservable ∣ ≤ bound
    rawBound =
      tv shiftedObservable shiftedNN shifted≤1

    shiftedDifference :
      expectation (left pair) shiftedObservable
      - expectation (right pair) shiftedObservable
      ≡ expectation (left pair)
          (λ state → (leftObservable state - leftMean)
            * (rightObservable state - rightMean))
        - expectation (right pair)
          (λ state → (leftObservable state - leftMean)
            * (rightObservable state - rightMean))
    shiftedDifference =
      trans
        (cong₂ _-_
          (expectationShift (left pair)
            (λ state → (leftObservable state - leftMean)
              * (rightObservable state - rightMean))
            lowerEnd)
          (expectationShift (right pair)
            (λ state → (leftObservable state - leftMean)
              * (rightObservable state - rightMean))
            lowerEnd))
        (subtractSameRight
          (expectation (left pair)
            (λ state → (leftObservable state - leftMean)
              * (rightObservable state - rightMean)))
          (expectation (right pair)
            (λ state → (leftObservable state - leftMean)
              * (rightObservable state - rightMean)))
          lowerEnd)
  in
  subst
    (λ difference → ∣ difference ∣ ≤ bound)
    shiftedDifference
    rawBound

covarianceGapIdentity :
  ∀ {State}
    (pair : FiniteRationalLawPair State)
    (leftObservable rightObservable : Observable State) →
  covariance (left pair) leftObservable rightObservable
  - covariance (right pair) leftObservable rightObservable
  ≡ halfℚ *
    ( ( expectation (left pair)
          (λ state →
            (leftObservable state
              - expectation (left pair) leftObservable)
            * (rightObservable state
              - expectation (left pair) rightObservable))
      - expectation (right pair)
          (λ state →
            (leftObservable state
              - expectation (left pair) leftObservable)
            * (rightObservable state
              - expectation (left pair) rightObservable)) )
    + ( expectation (left pair)
          (λ state →
            (leftObservable state
              - expectation (right pair) leftObservable)
            * (rightObservable state
              - expectation (right pair) rightObservable))
      - expectation (right pair)
          (λ state →
            (leftObservable state
              - expectation (right pair) leftObservable)
            * (rightObservable state
              - expectation (right pair) rightObservable)) ) )
covarianceGapIdentity pair leftObservable rightObservable =
  let
    leftLeftMean = expectation (left pair) leftObservable
    leftRightMean = expectation (left pair) rightObservable
    rightLeftMean = expectation (right pair) leftObservable
    rightRightMean = expectation (right pair) rightObservable

    leftProduct =
      expectation (left pair)
        (λ state → leftObservable state * rightObservable state)
    rightProduct =
      expectation (right pair)
        (λ state → leftObservable state * rightObservable state)

    covarianceLeft :
      covariance (left pair) leftObservable rightObservable
      ≡ leftProduct - leftRightMean * leftLeftMean
    covarianceLeft =
      cong₂ _-_ (refl {x = leftProduct})
        (ℚP.*-comm leftLeftMean leftRightMean)

    covarianceRight :
      covariance (right pair) leftObservable rightObservable
      ≡ rightProduct - rightRightMean * rightLeftMean
    covarianceRight =
      cong₂ _-_ (refl {x = rightProduct})
        (ℚP.*-comm rightLeftMean rightRightMean)

    algebraStep :
      covariance (left pair) leftObservable rightObservable
        - covariance (right pair) leftObservable rightObservable
      ≡ halfℚ *
        ( ((leftProduct
            - leftLeftMean * leftRightMean
            - leftRightMean * leftLeftMean
            + leftLeftMean * leftRightMean)
          - (rightProduct
            - leftLeftMean * rightRightMean
            - leftRightMean * rightLeftMean
            + leftLeftMean * leftRightMean))
        + ((leftProduct
            - rightLeftMean * leftRightMean
            - rightRightMean * leftLeftMean
            + rightLeftMean * rightRightMean)
          - (rightProduct
            - rightLeftMean * rightRightMean
            - rightRightMean * rightLeftMean
            + rightLeftMean * rightRightMean)) )
    algebraStep =
      trans
        (cong₂ _-_ covarianceLeft covarianceRight)
        (covarianceGapAlgebra
          leftLeftMean rightLeftMean leftRightMean rightRightMean
          leftProduct rightProduct)

    centeredStep :
      halfℚ *
        ( ((leftProduct
            - leftLeftMean * leftRightMean
            - leftRightMean * leftLeftMean
            + leftLeftMean * leftRightMean)
          - (rightProduct
            - leftLeftMean * rightRightMean
            - leftRightMean * rightLeftMean
            + leftLeftMean * leftRightMean))
        + ((leftProduct
            - rightLeftMean * leftRightMean
            - rightRightMean * leftLeftMean
            + rightLeftMean * rightRightMean)
          - (rightProduct
            - rightLeftMean * rightRightMean
            - rightRightMean * rightLeftMean
            + rightLeftMean * rightRightMean)) )
      ≡ halfℚ *
        ( ( expectation (left pair)
              (λ state →
                (leftObservable state - leftLeftMean)
                * (rightObservable state - leftRightMean))
          - expectation (right pair)
              (λ state →
                (leftObservable state - leftLeftMean)
                * (rightObservable state - leftRightMean)) )
        + ( expectation (left pair)
              (λ state →
                (leftObservable state - rightLeftMean)
                * (rightObservable state - rightRightMean))
          - expectation (right pair)
              (λ state →
                (leftObservable state - rightLeftMean)
                * (rightObservable state - rightRightMean)) ) )
    centeredStep =
      cong (halfℚ *_)
        (cong₂ _+_
          (cong₂ _-_
            (sym (expectationCenteredProduct
              (left pair) leftObservable rightObservable
              leftLeftMean leftRightMean))
            (sym (expectationCenteredProduct
              (right pair) leftObservable rightObservable
              leftLeftMean leftRightMean)))
          (cong₂ _-_
            (sym (expectationCenteredProduct
              (left pair) leftObservable rightObservable
              rightLeftMean rightRightMean))
            (sym (expectationCenteredProduct
              (right pair) leftObservable rightObservable
              rightLeftMean rightRightMean))))
  in
  trans algebraStep centeredStep

sharpUnitIntervalCovarianceGap :
  ∀ {State}
    (pair : FiniteRationalLawPair State) {bound : ℚ} →
  0ℚ ≤ bound →
  LocalTotalVariation pair bound →
  (leftObservable rightObservable : Observable State) →
  (∀ state → 0ℚ ≤ leftObservable state) →
  (∀ state → leftObservable state ≤ 1ℚ) →
  (∀ state → 0ℚ ≤ rightObservable state) →
  (∀ state → rightObservable state ≤ 1ℚ) →
  ∣ covariance (left pair) leftObservable rightObservable
    - covariance (right pair) leftObservable rightObservable ∣
  ≤ bound
sharpUnitIntervalCovarianceGap pair {bound} boundNN tv
    leftObservable rightObservable
    leftNN left≤1 rightNN right≤1 =
  let
    leftLeftMean = expectation (left pair) leftObservable
    leftRightMean = expectation (left pair) rightObservable
    rightLeftMean = expectation (right pair) leftObservable
    rightRightMean = expectation (right pair) rightObservable

    leftLeftMeanNN = expectationNonnegative (left pair) leftObservable leftNN
    leftRightMeanNN = expectationNonnegative (left pair) rightObservable rightNN
    rightLeftMeanNN = expectationNonnegative (right pair) leftObservable leftNN
    rightRightMeanNN = expectationNonnegative (right pair) rightObservable rightNN

    leftLeftMean≤1 = expectationBelowOne (left pair) leftObservable leftNN left≤1
    leftRightMean≤1 = expectationBelowOne (left pair) rightObservable rightNN right≤1
    rightLeftMean≤1 = expectationBelowOne (right pair) leftObservable leftNN left≤1
    rightRightMean≤1 = expectationBelowOne (right pair) rightObservable rightNN right≤1

    centeredLeft :
      ∣ expectation (left pair)
          (λ state →
            (leftObservable state - leftLeftMean)
            * (rightObservable state - leftRightMean))
        - expectation (right pair)
          (λ state →
            (leftObservable state - leftLeftMean)
            * (rightObservable state - leftRightMean)) ∣
      ≤ bound
    centeredLeft =
      centeredDifferenceBound pair boundNN tv
        leftObservable rightObservable
        leftNN left≤1 rightNN right≤1
        leftLeftMean leftRightMean
        leftLeftMeanNN leftLeftMean≤1 leftRightMeanNN leftRightMean≤1

    centeredRight :
      ∣ expectation (left pair)
          (λ state →
            (leftObservable state - rightLeftMean)
            * (rightObservable state - rightRightMean))
        - expectation (right pair)
          (λ state →
            (leftObservable state - rightLeftMean)
            * (rightObservable state - rightRightMean)) ∣
      ≤ bound
    centeredRight =
      centeredDifferenceBound pair boundNN tv
        leftObservable rightObservable
        leftNN left≤1 rightNN right≤1
        rightLeftMean rightRightMean
        rightLeftMeanNN rightLeftMean≤1 rightRightMeanNN rightRightMean≤1

    leftCenteredGap : ℚ
    leftCenteredGap =
      expectation (left pair)
        (λ state →
          (leftObservable state - leftLeftMean)
          * (rightObservable state - leftRightMean))
      - expectation (right pair)
        (λ state →
          (leftObservable state - leftLeftMean)
          * (rightObservable state - leftRightMean))

    rightCenteredGap : ℚ
    rightCenteredGap =
      expectation (left pair)
        (λ state →
          (leftObservable state - rightLeftMean)
          * (rightObservable state - rightRightMean))
      - expectation (right pair)
        (λ state →
          (leftObservable state - rightLeftMean)
          * (rightObservable state - rightRightMean))

    sumBound :
      ∣ leftCenteredGap + rightCenteredGap ∣
      ≤ bound + bound
    sumBound =
      ℚP.≤-trans
        (ℚP.∣p+q∣≤∣p∣+∣q∣ leftCenteredGap rightCenteredGap)
        (ℚP.+-mono-≤ centeredLeft centeredRight)

    centeredSum : ℚ
    centeredSum = leftCenteredGap + rightCenteredGap

    scaledBound : halfℚ * ∣ centeredSum ∣ ≤ bound
    scaledBound =
      let
        multiplied =
          mulLeftNN halfℚ halfNonnegative sumBound
      in
      subst
        (λ upper → halfℚ * ∣ centeredSum ∣ ≤ upper)
        (halfDouble bound)
        multiplied

    gapIsScaled :
      ∣ covariance (left pair) leftObservable rightObservable
        - covariance (right pair) leftObservable rightObservable ∣
      ≡ halfℚ * ∣ centeredSum ∣
    gapIsScaled =
      trans
        (cong ∣_∣ (covarianceGapIdentity pair leftObservable rightObservable))
        (trans
          (ℚP.∣p*q∣≡∣p∣*∣q∣ halfℚ centeredSum)
          (halfAbsMul centeredSum))
  in
  subst
    (λ magnitude → magnitude ≤ bound)
    (sym gapIsScaled)
    scaledBound

signedToUnit : ℚ → ℚ
signedToUnit value = halfℚ * value + halfℚ

signedToUnitAffine : ∀ (value : ℚ) → signedToUnit value ≡ halfℚ * value + halfℚ
signedToUnitAffine value = refl

halfDistribute : ∀ (value : ℚ) → halfℚ * value + halfℚ ≡ halfℚ * (value + 1ℚ)
halfDistribute = ℚRing.solve-∀

signedToUnitDistributed : ∀ (value : ℚ) → signedToUnit value ≡ halfℚ * (value + 1ℚ)
signedToUnitDistributed value =
  trans (signedToUnitAffine value) (halfDistribute value)

signedToUnitNonnegative :
  ∀ {value : ℚ} → - 1ℚ ≤ value → 0ℚ ≤ signedToUnit value
signedToUnitNonnegative {value} lower =
  let
    oneHalfNN : 0ℚ ≤ halfℚ
    oneHalfNN = ℚP.nonNegative⁻¹ (halfℚ)

    valuePlusOneNN : 0ℚ ≤ value + 1ℚ
    valuePlusOneNN =
      subst (λ left → left ≤ value + 1ℚ)
        negativeOnePlusOne
        (ℚP.+-mono-≤ lower ℚP.≤-refl)

    productNN : 0ℚ ≤ (halfℚ) * (value + 1ℚ)
    productNN =
      productNN
        (halfℚ) (value + 1ℚ)
        oneHalfNN valuePlusOneNN
   in
   subst (λ value → 0ℚ ≤ value)
     (sym (signedToUnitDistributed value))
     productNN

signedToUnitBelowOne :
  ∀ {value : ℚ} → value ≤ 1ℚ → signedToUnit value ≤ 1ℚ
signedToUnitBelowOne {value} upper =
  let
    oneHalfNN : 0ℚ ≤ halfℚ
    oneHalfNN = ℚP.nonNegative⁻¹ (halfℚ)

    valuePlusOneLeTwo : value + 1ℚ ≤ 1ℚ + 1ℚ
    valuePlusOneLeTwo =
      ℚP.+-mono-≤ upper ℚP.≤-refl

    scaled : (halfℚ) * (value + 1ℚ) ≤ (halfℚ) * (1ℚ + 1ℚ)
    scaled =
      mulLeftNN (halfℚ) oneHalfNN valuePlusOneLeTwo
   in
   subst
     (λ upperBound → signedToUnit value ≤ upperBound)
     halfTwo
     (subst
       (λ left → left ≤ halfℚ * (1ℚ + 1ℚ))
       (sym (signedToUnitDistributed value))
       scaled)

valueBelowAbs : ∀ (value : ℚ) → value ≤ ∣ value ∣
valueBelowAbs value with ℚP.≤-total 0ℚ value
... | inj₁ valueNN =
  subst (λ abs → value ≤ abs)
    (sym (ℚP.0≤p⇒∣p∣≡p valueNN))
    ℚP.≤-refl
... | inj₂ valueNP =
  let
    negValueNN : 0ℚ ≤ - value
    negValueNN = negMono valueNP
  in
  subst (λ abs → value ≤ abs)
    (ℚP.∣-p∣≡∣p∣ value)
    (ℚP.≤-trans valueNP
      (ℚP.≤-trans negValueNN
        (subst (λ abs → - value ≤ abs)
          (sym (ℚP.0≤p⇒∣p∣≡p negValueNN))
          ℚP.≤-refl)))

lowerFromAbsBound : ∀ {value : ℚ} → ∣ value ∣ ≤ 1ℚ → - 1ℚ ≤ value
lowerFromAbsBound {value} bound =
  ℚP.≤-trans
    (negMono bound)
    (subst
      (λ right → - ∣ value ∣ ≤ right)
      (negNeg value)
      (subst
        (λ abs → - abs ≤ - (- value))
        (ℚP.∣-p∣≡∣p∣ value)
        (negMono (valueBelowAbs (- value)))))

upperFromAbsBound : ∀ {value : ℚ} → ∣ value ∣ ≤ 1ℚ → value ≤ 1ℚ
upperFromAbsBound {value} bound =
  ℚP.≤-trans (valueBelowAbs value) bound

oneAddComm : ∀ (value : ℚ) → 1ℚ + value ≡ value + 1ℚ
oneAddComm = ℚRing.solve-∀

oneBelowAdd : ∀ {value : ℚ} → 0ℚ ≤ value → 1ℚ ≤ value + 1ℚ
oneBelowAdd {value} valueNN =
  subst
    (λ right → 1ℚ ≤ right)
    (oneAddComm value)
    (subst
      (λ left → left ≤ 1ℚ + value)
      (sym (addZeroRight 1ℚ))
      (ℚP.+-mono-≤ ℚP.≤-refl valueNN))

negDifference : ∀ (a b : ℚ) → - (a - b) ≡ b - a
negDifference = ℚRing.solve-∀

mixtureGapAlgebra :
  ∀ (p good bad : ℚ) →
  ((1ℚ - p) * good + p * bad) - good ≡ p * (bad - good)
mixtureGapAlgebra = ℚRing.solve-∀

absDiffUnitBound :
  ∀ {a b : ℚ} →
  0ℚ ≤ a → a ≤ 1ℚ →
  0ℚ ≤ b → b ≤ 1ℚ →
  ∣ a - b ∣ ≤ 1ℚ
absDiffUnitBound {a} {b} aNN a≤1 bNN b≤1 with ℚP.≤-total 0ℚ (a - b)
... | inj₁ differenceNN =
  subst
    (λ magnitude → magnitude ≤ 1ℚ)
    (sym (ℚP.0≤p⇒∣p∣≡p differenceNN))
    (subtractBelowOne (ℚP.≤-trans a≤1 (oneBelowAdd bNN)))
... | inj₂ differenceNP =
  let
    negNN : 0ℚ ≤ - (a - b)
    negNN = negMono differenceNP

    absNeg :
      ∣ - (a - b) ∣ ≡ - (a - b)
    absNeg = ℚP.0≤p⇒∣p∣≡p negNN

    absOriginal :
      ∣ a - b ∣ ≡ - (a - b)
    absOriginal =
      trans (sym (ℚP.∣-p∣≡∣p∣ (a - b))) absNeg

    upperNeg :
      - (a - b) ≤ 1ℚ
    upperNeg =
      subst
        (λ value → value ≤ 1ℚ)
        (sym (negDifference a b))
        (subtractBelowOne (ℚP.≤-trans b≤1 (oneBelowAdd aNN)))
  in
  subst (λ magnitude → magnitude ≤ 1ℚ) (sym absOriginal) upperNeg

sumRationalAffineRaw :
  ∀ {State} (states : List State)
    (weight observable : State → ℚ) (scale shift : ℚ) →
  sumRational states
    (λ state → weight state * (scale * observable state + shift))
  ≡ scale * sumRational states (λ state → weight state * observable state)
    + shift * sumRational states weight
sumRationalAffineRaw [] weight observable scale shift = affineRawNil scale shift
sumRationalAffineRaw (state ∷ states) weight observable scale shift
  rewrite sumRationalAffineRaw states weight observable scale shift =
    affineRawStep
      (weight state) (observable state) scale shift
      (sumRational states (λ s → weight s * observable s))
      (sumRational states weight)

sumRationalAffineProductRaw :
  ∀ {State} (states : List State)
    (weight left right : State → ℚ) (scale leftShift rightShift : ℚ) →
  sumRational states
    (λ state → weight state *
      ((scale * left state + leftShift) * (scale * right state + rightShift)))
  ≡ scale * scale *
      sumRational states (λ state → weight state * (left state * right state))
    + scale * leftShift *
      sumRational states (λ state → weight state * right state)
    + scale * rightShift *
      sumRational states (λ state → weight state * left state)
    + leftShift * rightShift * sumRational states weight
sumRationalAffineProductRaw [] weight left right scale leftShift rightShift =
  affineProductRawNil scale leftShift rightShift
sumRationalAffineProductRaw (state ∷ states) weight left right scale leftShift rightShift
  rewrite sumRationalAffineProductRaw states weight left right scale leftShift rightShift =
    affineProductRawStep
      (weight state) (left state) (right state)
      scale leftShift rightShift
      (sumRational states (λ s → weight s * (left s * right s)))
      (sumRational states (λ s → weight s * right s))
      (sumRational states (λ s → weight s * left s))
      (sumRational states weight)

covarianceAffineScale :
  ∀ {State}
    (probability : FiniteRationalProbability State)
    (left right : Observable State) (leftShift rightShift scale : ℚ) →
  covariance probability
    (λ state → scale * left state + leftShift)
    (λ state → scale * right state + rightShift)
  ≡ scale * scale * covariance probability left right
covarianceAffineScale probability left right leftShift rightShift scale
  rewrite sumRationalAffineProductRaw
      (states probability)
      (weight probability)
      left right scale leftShift rightShift
    | sumRationalAffineRaw
      (states probability)
      (weight probability)
      left scale leftShift
    | sumRationalAffineRaw
      (states probability)
      (weight probability)
      right scale rightShift
    | normalized probability =
    covarianceAffineAlgebra
      scale leftShift rightShift
      (sumRational (states probability)
        (λ state → weight probability state * left state))
      (sumRational (states probability)
        (λ state → weight probability state * right state))
      (sumRational (states probability)
        (λ state → weight probability state * (left state * right state)))

sharpSignedCovarianceGap :
  ∀ {State}
    (pair : FiniteRationalLawPair State) {bound : ℚ} →
  0ℚ ≤ bound →
  LocalTotalVariation pair bound →
  (leftObservable rightObservable : Observable State) →
  (∀ state → ∣ leftObservable state ∣ ≤ 1ℚ) →
  (∀ state → ∣ rightObservable state ∣ ≤ 1ℚ) →
  ∣ covariance (left pair) leftObservable rightObservable
    - covariance (right pair) leftObservable rightObservable ∣
  ≤ fourℚ * bound
sharpSignedCovarianceGap pair {bound} boundNN tv
    leftObservable rightObservable leftBound rightBound =
  let
    unitLeft : Observable _
    unitLeft state = halfℚ * leftObservable state + halfℚ

    unitRight : Observable _
    unitRight state = halfℚ * rightObservable state + halfℚ

    unitLeftNN : ∀ state → 0ℚ ≤ unitLeft state
    unitLeftNN state =
      subst (λ value → 0ℚ ≤ value)
        (signedToUnitAffine (leftObservable state))
        (signedToUnitNonnegative (lowerFromAbsBound (leftBound state)))

    unitLeft≤1 : ∀ state → unitLeft state ≤ 1ℚ
    unitLeft≤1 state =
      subst (λ value → value ≤ 1ℚ)
        (signedToUnitAffine (leftObservable state))
        (signedToUnitBelowOne (upperFromAbsBound (leftBound state)))

    unitRightNN : ∀ state → 0ℚ ≤ unitRight state
    unitRightNN state =
      subst (λ value → 0ℚ ≤ value)
        (signedToUnitAffine (rightObservable state))
        (signedToUnitNonnegative (lowerFromAbsBound (rightBound state)))

    unitRight≤1 : ∀ state → unitRight state ≤ 1ℚ
    unitRight≤1 state =
      subst (λ value → value ≤ 1ℚ)
        (signedToUnitAffine (rightObservable state))
        (signedToUnitBelowOne (upperFromAbsBound (rightBound state)))

    unitGap =
      sharpUnitIntervalCovarianceGap pair boundNN tv
        unitLeft unitRight
        unitLeftNN unitLeft≤1 unitRightNN unitRight≤1

    signedCovarianceLeft =
      covarianceAffineScale
        (left pair) leftObservable rightObservable
        (halfℚ) (halfℚ) (halfℚ)

    signedCovarianceRight =
      covarianceAffineScale
        (right pair) leftObservable rightObservable
        (halfℚ) (halfℚ) (halfℚ)

    signedGap : ℚ
    signedGap =
      covariance (left pair) leftObservable rightObservable
      - covariance (right pair) leftObservable rightObservable

    unitGapEquality :
      covariance (left pair) unitLeft unitRight
      - covariance (right pair) unitLeft unitRight
      ≡ coeffℚ *
        (covariance (left pair) leftObservable rightObservable
        - covariance (right pair) leftObservable rightObservable)
    unitGapEquality =
      trans
        (cong₂ _-_ signedCovarianceLeft signedCovarianceRight)
        (scaleDifference coeffℚ
          (covariance (left pair) leftObservable rightObservable)
          (covariance (right pair) leftObservable rightObservable))

    unitAbsEquality :
      ∣ covariance (left pair) unitLeft unitRight
        - covariance (right pair) unitLeft unitRight ∣
      ≡ coeffℚ *
        ∣ covariance (left pair) leftObservable rightObservable
          - covariance (right pair) leftObservable rightObservable ∣
    unitAbsEquality =
      trans
        (cong ∣_∣ unitGapEquality)
        (trans
          (ℚP.∣p*q∣≡∣p∣*∣q∣ coeffℚ
            (covariance (left pair) leftObservable rightObservable
              - covariance (right pair) leftObservable rightObservable))
          (absMulLeft coeffNN signedGap))

    fourUnitAbs :
      fourℚ *
        ∣ covariance (left pair) unitLeft unitRight
          - covariance (right pair) unitLeft unitRight ∣
      ≡ ∣ covariance (left pair) leftObservable rightObservable
          - covariance (right pair) leftObservable rightObservable ∣
    fourUnitAbs =
      trans
        (cong (fourℚ *_) unitAbsEquality)
        (fourCoeffAbs
          ∣ covariance (left pair) leftObservable rightObservable
            - covariance (right pair) leftObservable rightObservable ∣)

    scaledGap :
      ∣ covariance (left pair) leftObservable rightObservable
        - covariance (right pair) leftObservable rightObservable ∣
      ≡ fourℚ *
        ∣ covariance (left pair) unitLeft unitRight
          - covariance (right pair) unitLeft unitRight ∣
    scaledGap = sym fourUnitAbs

    scaledBound :
      fourℚ *
        ∣ covariance (left pair) unitLeft unitRight
          - covariance (right pair) unitLeft unitRight ∣
      ≤ fourℚ * bound
    scaledBound =
      mulLeftNN fourℚ fourNN unitGap
  in
  subst
    (λ magnitude → magnitude ≤ fourℚ * bound)
    (sym scaledGap)
    scaledBound

badEventSharpSignedCovarianceGap :
  ∀ {State}
    (decomposition : BadEventDecomposition State)
    (leftObservable rightObservable : Observable State) →
  (∀ state → ∣ leftObservable state ∣ ≤ 1ℚ) →
  (∀ state → ∣ rightObservable state ∣ ≤ 1ℚ) →
  ∣ covariance
      (left (lawPair decomposition))
      leftObservable rightObservable
    - covariance
      (right (lawPair decomposition))
      leftObservable rightObservable ∣
  ≤ fourℚ * badMass decomposition
badEventSharpSignedCovarianceGap decomposition leftObservable rightObservable
    leftBound rightBound =
  sharpSignedCovarianceGap
    (lawPair decomposition)
    (badMassNonnegative decomposition)
     (badEventLocalTotalVariation decomposition)
     leftObservable rightObservable
     leftBound rightBound

record ConvexBadEventMixture (State : Set) : Set₁ where
  field
    fullLaw : FiniteRationalProbability State
    goodLaw : FiniteRationalProbability State
    badLaw : FiniteRationalProbability State
    badMass : ℚ
    badMassNonnegative : 0ℚ ≤ badMass
    mixture :
      ∀ observable →
      expectation fullLaw observable
        ≡ (1ℚ - badMass) * expectation goodLaw observable
          + badMass * expectation badLaw observable

open ConvexBadEventMixture public

convexMixtureLocalTotalVariation :
  ∀ {State} (mixtureData : ConvexBadEventMixture State) →
  LocalTotalVariation
    (record
      { left = fullLaw mixtureData
      ; right = goodLaw mixtureData
      })
    (badMass mixtureData)
convexMixtureLocalTotalVariation {State} mixtureData observable observableNN observable≤1 =
  let
    fullMean : ℚ
    fullMean = expectation (fullLaw mixtureData) observable

    goodMean : ℚ
    goodMean = expectation (goodLaw mixtureData) observable

    badMean : ℚ
    badMean = expectation (badLaw mixtureData) observable

    p : ℚ
    p = badMass mixtureData

    pNN : 0ℚ ≤ p
    pNN = badMassNonnegative mixtureData

    goodNN : 0ℚ ≤ goodMean
    goodNN = expectationNonnegative (goodLaw mixtureData) observable observableNN

    good≤1 : goodMean ≤ 1ℚ
    good≤1 = expectationBelowOne (goodLaw mixtureData) observable observableNN observable≤1

    badNN : 0ℚ ≤ badMean
    badNN = expectationNonnegative (badLaw mixtureData) observable observableNN

    bad≤1 : badMean ≤ 1ℚ
    bad≤1 = expectationBelowOne (badLaw mixtureData) observable observableNN observable≤1

    meanGap : fullMean - goodMean ≡ p * (badMean - goodMean)
    meanGap =
      trans
        (cong (λ value → value - goodMean) (mixture mixtureData observable))
        (mixtureGapAlgebra p goodMean badMean)

    absMeanGap :
      ∣ fullMean - goodMean ∣ ≡ p * ∣ badMean - goodMean ∣
    absMeanGap =
      trans
        (cong ∣_∣ meanGap)
        (trans
          (ℚP.∣p*q∣≡∣p∣*∣q∣ p (badMean - goodMean))
          (absMulLeft pNN (badMean - goodMean)))

    rawGap : ∣ badMean - goodMean ∣ ≤ 1ℚ
    rawGap = absDiffUnitBound badNN bad≤1 goodNN good≤1

    productBound : p * ∣ badMean - goodMean ∣ ≤ p
    productBound =
      subst (λ value → p * ∣ badMean - goodMean ∣ ≤ value)
        (multiplyOneRight p)
        (mulLeftNN p pNN rawGap)
  in
  subst (λ magnitude → magnitude ≤ p) (sym absMeanGap) productBound

convexBadEventSharpCovarianceGap :
  ∀ {State}
    (mixtureData : ConvexBadEventMixture State)
    (leftObservable rightObservable : Observable State) →
  (∀ state → ∣ leftObservable state ∣ ≤ 1ℚ) →
  (∀ state → ∣ rightObservable state ∣ ≤ 1ℚ) →
  ∣ covariance
      (fullLaw mixtureData)
      leftObservable rightObservable
    - covariance
      (goodLaw mixtureData)
      leftObservable rightObservable ∣
  ≤ fourℚ * badMass mixtureData
convexBadEventSharpCovarianceGap mixtureData leftObservable rightObservable
    leftBound rightBound =
  sharpSignedCovarianceGap
    (record
      { left = fullLaw mixtureData
      ; right = goodLaw mixtureData
      })
    (badMassNonnegative mixtureData)
    (convexMixtureLocalTotalVariation mixtureData)
    leftObservable rightObservable
    leftBound rightBound

------------------------------------------------------------------------
-- Source-facing conditional Gibbs weld.
--
-- Source calibration: the original finite Wilson/CMP119 conditional-row
-- owner is `DASHI/Physics/YangMills/YMClayPhysicalCubeDobrushinFromGibbsExact.agda`
-- (`OriginalPhysicalCubeConditionals`, `originalConditionalRowsUniformlyContract`),
-- itself based on the original Wilson conditional fibre and CMP119 source.
-- The sharp `[0,1]` constant is calibrated by PR #1536 doc commit
-- 5407fb27e1f5826759d1568b32fb472eb1d3677a cited above.  The record below is
-- the DASHI interface receiving those source estimates; it does not assert
-- that the physical estimates are available by definition.
------------------------------------------------------------------------

record OriginalWilsonConditionalBadEventData (Local Boundary : Set) : Set₁ where
  field
    states : List Local
    rawWeight : Boundary → Local → ℚ
    normalizer : Boundary → ℚ
    rawWeightNonnegative : ∀ boundary local → 0ℚ ≤ rawWeight boundary local
    normalizerNonnegative : ∀ boundary → 0ℚ ≤ normalizer boundary
    normalized :
      ∀ boundary →
        normalizer boundary * sumRational states (rawWeight boundary) ≡ 1ℚ
    commonInfluence : ℚ
    commonInfluenceNonnegative : 0ℚ ≤ commonInfluence
    rowDistanceBound :
      ∀ left right →
        sumRational states
          (λ local →
            ∣ normalizer left * rawWeight left local
              - normalizer right * rawWeight right local ∣)
        ≤ commonInfluence

open OriginalWilsonConditionalBadEventData public

originalWilsonConditionalBadEventDecomposition :
  ∀ {Local Boundary}
    (dataSet : OriginalWilsonConditionalBadEventData Local Boundary)
    (left right : Boundary) →
  BadEventDecomposition Local
originalWilsonConditionalBadEventDecomposition {Local} {Boundary} dataSet left right =
  let
    leftLaw : FiniteRationalProbability Local
    leftLaw = record
      { states = states dataSet
      ; weight = λ local →
          normalizer dataSet left * rawWeight dataSet left local
      ; weightNonnegative = λ local →
          productNN
            (normalizer dataSet left)
            (rawWeight dataSet left local)
            (normalizerNonnegative dataSet left)
            (rawWeightNonnegative dataSet left local)
      ; normalized =
          trans
            (sumRationalScale
              (states dataSet) (rawWeight dataSet left)
              (normalizer dataSet left))
            (normalized dataSet left)
      }

    rightLaw : FiniteRationalProbability Local
    rightLaw = record
      { states = states dataSet
      ; weight = λ local →
          normalizer dataSet right * rawWeight dataSet right local
      ; weightNonnegative = λ local →
          productNN
            (normalizer dataSet right)
            (rawWeight dataSet right local)
            (normalizerNonnegative dataSet right)
            (rawWeightNonnegative dataSet right local)
      ; normalized =
          trans
            (sumRationalScale
              (states dataSet) (rawWeight dataSet right)
              (normalizer dataSet right))
            (normalized dataSet right)
      }
  in
  record
    { lawPair = record { left = leftLaw ; right = rightLaw }
    ; badMass =
        sumRational (states dataSet)
          (λ local →
            ∣ normalizer dataSet left * rawWeight dataSet left local
              - normalizer dataSet right * rawWeight dataSet right local ∣)
    ; badMassNonnegative =
        sumRationalNonnegative (states dataSet)
          (λ local →
            ∣ normalizer dataSet left * rawWeight dataSet left local
              - normalizer dataSet right * rawWeight dataSet right local ∣)
          (λ local → ℚP.0≤∣p∣
            (normalizer dataSet left * rawWeight dataSet left local
              - normalizer dataSet right * rawWeight dataSet right local))
    ; badWeight = λ local →
        ∣ normalizer dataSet left * rawWeight dataSet left local
          - normalizer dataSet right * rawWeight dataSet right local ∣
    ; badWeightNonnegative = λ local → ℚP.0≤∣p∣
        (normalizer dataSet left * rawWeight dataSet left local
          - normalizer dataSet right * rawWeight dataSet right local)
    ; badMassIsSum = refl
    ; statesAgree = refl
    ; weightDifferenceBound = λ local → ℚP.≤-refl
    }

originalWilsonConditionalSharpCovarianceGap :
  ∀ {Local Boundary}
    (dataSet : OriginalWilsonConditionalBadEventData Local Boundary)
    (left right : Boundary)
    (observable₁ observable₂ : Observable Local) →
  (∀ local → ∣ observable₁ local ∣ ≤ 1ℚ) →
  (∀ local → ∣ observable₂ local ∣ ≤ 1ℚ) →
  ∣ covariance
      (FiniteRationalLawPair.left
        (lawPair (originalWilsonConditionalBadEventDecomposition
          dataSet left right)))
      observable₁ observable₂
    - covariance
      (FiniteRationalLawPair.right
        (lawPair (originalWilsonConditionalBadEventDecomposition
          dataSet left right)))
      observable₁ observable₂ ∣
  ≤ fourℚ * commonInfluence dataSet
originalWilsonConditionalSharpCovarianceGap dataSet left right
    observable₁ observable₂ bound₁ bound₂ =
  ℚP.≤-trans
    (badEventSharpSignedCovarianceGap
      (originalWilsonConditionalBadEventDecomposition dataSet left right)
      observable₁ observable₂
      bound₁ bound₂)
    (mulLeftNN fourℚ fourNN (rowDistanceBound dataSet left right))
