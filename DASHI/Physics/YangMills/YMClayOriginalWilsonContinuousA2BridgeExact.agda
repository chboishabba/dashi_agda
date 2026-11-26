module DASHI.Physics.YangMills.YMClayOriginalWilsonContinuousA2BridgeExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (subst; sym; cong)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _-ℝ_; _*ℝ_; _/ℝ_; -ℝ_; absℝ; _≤ℝ_; _<ℝ_;
   ≤ℝ-refl; ≤ℝ-trans; ≤ℝ-antisym; ≤ℝ-total; +-mono-≤; addRightCancelLe;
   zeroLtOne; subPositiveOfLt; notLeOfLt;
   negℝ-involutive; negEqSubZero; subEqAddNeg; negℝ-add; negℝ-sub;
      negℝ-mulʳ; negℝ-mulˡ; negℝ-mul-neg; negℝ-order;
 subRightMono; subLeftMono;
    mulNonnegative;
    mulOneʳ; mulZeroʳ; oneNonnegative; subSelf;
    +-identityˡ; +-identityʳ; +-assoc; +-comm; subAddCancel;
    addSubAssoc; subSubComm; predSucc; addThreeSubTwoPlus; addThreeSubTwoMinus;
    negOneMinusPlus; lowerPlusFourEq;
    oneMinusMulOneMinus; onePlusMulOnePlus;
    oneMinusMulOnePlus; onePlusMulOneMinus;
    absZero; absAddSubadditive; absSubadditive; absMul; absNeg;
    absNonnegative; leAbs; negLeAbs; absOfNonnegative; absOfNonpositive;
    mulMonotoneNonnegative;
    divℝ-nonnegative; divℝ-nonpositive; divℝ-le-one; divℝ-one-le;
    divℝ-positive; divℝ-lt-one)

import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient

continuousWilsonA2OriginalOwner : String
continuousWilsonA2OriginalOwner =
  "DASHI.Physics.YangMills.YMClayOriginalVariableWilsonCovarianceSourceExact"

continuousWilsonA2HaarOwner : String
continuousWilsonA2HaarOwner =
  "DASHI.Physics.YangMills.YMClaySUNVariablePeriodicProductHaarExact"

continuousWilsonA2IntegrationOwner : String
continuousWilsonA2IntegrationOwner =
  "DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact"

continuousWilsonA2FiniteRegressionOwner : String
continuousWilsonA2FiniteRegressionOwner =
  "DASHI.Physics.YangMills.YMClaySharpFiniteTotalVariationCovarianceExact"

continuousWilsonA2ContourSumStatus : String
continuousWilsonA2ContourSumStatus =
  "source contour-product rate remains unpaid; this module proves only the q-to-contour-sum transport"

continuousWilsonA2ContourSumSourceOwner : String
continuousWilsonA2ContourSumSourceOwner =
  "Docs/physics/YMClayP0R445TwoMarkJointTVSharpCovarianceAndPhysicalW3RateCut20261124.md"

continuousWilsonA2ContourSumRateStatus : String
continuousWilsonA2ContourSumRateStatus =
  "conditional source rate; C(beta)=8+(2/3)log(24)+log(beta) is not cutoff-uniform"

continuousWilsonA2GoodFieldComparisonStatus : String
continuousWilsonA2GoodFieldComparisonStatus =
  "source-weighted good measure vs CMP116 good-field measure remains unpaid"

twoℝ : ℝ
twoℝ = 1ℝ +ℝ 1ℝ

fourℝ : ℝ
fourℝ = twoℝ +ℝ twoℝ

RangeNegOneOne : ℝ → Set
RangeNegOneOne value = ((0ℝ -ℝ 1ℝ) ≤ℝ value) × (value ≤ℝ 1ℝ)

minusOneℝ : ℝ
minusOneℝ = 0ℝ -ℝ 1ℝ

threeℝ : ℝ
threeℝ = twoℝ +ℝ 1ℝ

negZeroℝ : -ℝ 0ℝ ≡ 0ℝ
negZeroℝ = trans (negEqSubZero 0ℝ) (subSelf 0ℝ)

negMinusOneℝ : -ℝ minusOneℝ ≡ 1ℝ
negMinusOneℝ =
  trans (cong (λ t → -ℝ t) (sym (negEqSubZero 1ℝ))) (negℝ-involutive 1ℝ)

negNonnegativeOfNonpositive : ∀ {a : ℝ} → a ≤ℝ 0ℝ → 0ℝ ≤ℝ -ℝ a
negNonnegativeOfNonpositive {a} ha =
  subst (λ t → t ≤ℝ -ℝ a) negZeroℝ (negℝ-order ha)

nonpositiveOfNegativeNonnegative : ∀ {a : ℝ} → 0ℝ ≤ℝ -ℝ a → a ≤ℝ 0ℝ
nonpositiveOfNegativeNonnegative {a} ha =
  subst (λ t → t ≤ℝ 0ℝ) (negℝ-involutive a)
    (subst (λ t → -ℝ (-ℝ a) ≤ℝ t) negZeroℝ (negℝ-order ha))

addLeftMono : ∀ {a b : ℝ} (c : ℝ) → a ≤ℝ b → c +ℝ a ≤ℝ c +ℝ b
addLeftMono c h = +-mono-≤ ≤ℝ-refl h

addRightMono : ∀ {a b : ℝ} (c : ℝ) → a ≤ℝ b → a +ℝ c ≤ℝ b +ℝ c
addRightMono c h = +-mono-≤ h ≤ℝ-refl

addNegSelf : ∀ (a : ℝ) → a +ℝ (-ℝ a) ≡ 0ℝ
addNegSelf a = trans (sym (subEqAddNeg a a)) (subSelf a)

addNonpos : ∀ {a b : ℝ} → a ≤ℝ 0ℝ → b ≤ℝ 0ℝ → a +ℝ b ≤ℝ 0ℝ
addNonpos {a} {b} ha hb =
  let hna = negNonnegativeOfNonpositive ha
      hnb = negNonnegativeOfNonpositive hb
      hsum = DASHI.Foundations.RealAnalysisAxioms.addNonnegative hna hnb
      hneg =
        subst (λ t → 0ℝ ≤ℝ t) (sym (negℝ-add a b)) hsum
  in nonpositiveOfNegativeNonnegative hneg

subNonpos : ∀ {a b : ℝ} → a ≤ℝ b → a -ℝ b ≤ℝ 0ℝ
subNonpos {a} {b} hab =
  let hneg = negℝ-order hab
      hsum = addLeftMono a hneg
      hsum' =
        subst (λ t → t ≤ℝ a +ℝ (-ℝ a)) (sym (subEqAddNeg a b)) hsum
  in subst (λ t → a -ℝ b ≤ℝ t) (addNegSelf a) hsum'

negAbsLe : ∀ (x : ℝ) → -ℝ (absℝ x) ≤ℝ x
negAbsLe x =
  let h = negℝ-order (leAbs (-ℝ x))
      h' =
        subst (λ t → -ℝ t ≤ℝ -ℝ (-ℝ x)) (absNeg x) h
  in subst (λ t → -ℝ (absℝ x) ≤ℝ t) (negℝ-involutive x) h'

absOneℝ : absℝ 1ℝ ≡ 1ℝ
absOneℝ = absOfNonnegative oneNonnegative

negOneLeOfRange : ∀ {x : ℝ} → RangeNegOneOne x → -ℝ 1ℝ ≤ℝ x
negOneLeOfRange {x} hx =
  subst (λ t → t ≤ℝ x) (sym (negEqSubZero 1ℝ)) (proj₁ hx)

twiceLeTwo : ∀ {x : ℝ} → x ≤ℝ 1ℝ → x +ℝ x ≤ℝ twoℝ
twiceLeTwo {x} hx = +-mono-≤ hx hx

leTwoMinusSelf : ∀ {x : ℝ} → x ≤ℝ 1ℝ → x ≤ℝ twoℝ -ℝ x
leTwoMinusSelf {x} hx =
  let hxx = twiceLeTwo hx
      hsub = subRightMono x hxx
  in subst (λ t → t ≤ℝ twoℝ -ℝ x) (DASHI.Foundations.RealAnalysisAxioms.addSubCancel x x) hsub

negLeOneOfLower : ∀ {x : ℝ} → -ℝ 1ℝ ≤ℝ x → -ℝ x ≤ℝ 1ℝ
negLeOneOfLower {x} hx =
  subst (λ t → -ℝ x ≤ℝ t) (negℝ-involutive 1ℝ) (negℝ-order hx)

subMinusOneEqAddOne : ∀ (x : ℝ) → x -ℝ minusOneℝ ≡ x +ℝ 1ℝ
subMinusOneEqAddOne x =
  let h0 = sym (negEqSubZero 1ℝ)
      h1 = cong (λ t → x -ℝ t) h0
      h2 = subEqAddNeg x (-ℝ 1ℝ)
      h3 =
        cong (λ t → x +ℝ t) (negℝ-involutive 1ℝ)
  in trans h1 (trans h2 h3)

oneLeTwoPlusOfLower : ∀ {x : ℝ} → -ℝ 1ℝ ≤ℝ x → 1ℝ ≤ℝ twoℝ +ℝ x
oneLeTwoPlusOfLower {x} hx =
  let hx' = subst (λ t → t ≤ℝ x) (negEqSubZero 1ℝ) hx
      h0' = DASHI.Foundations.RealAnalysisAxioms.subNonnegative hx'
      h0'' =
        subst (λ t → 0ℝ ≤ℝ t) (subMinusOneEqAddOne x) h0'
      h0 = subst (λ t → 0ℝ ≤ℝ t) (+-comm x 1ℝ) h0''
      h1 = addLeftMono 1ℝ h0
      h1' =
        subst (λ t → t ≤ℝ 1ℝ +ℝ (1ℝ +ℝ x)) (+-identityʳ 1ℝ) h1
      h2 = sym (+-assoc 1ℝ 1ℝ x)
  in subst (λ t → 1ℝ ≤ℝ t) h2 h1'

absLeOneOfRange : ∀ {x : ℝ} → RangeNegOneOne x → absℝ x ≤ℝ 1ℝ
absLeOneOfRange {x} hx with ≤ℝ-total 0ℝ x
... | inj₁ h0 =
  subst (λ t → t ≤ℝ 1ℝ) (sym (absOfNonnegative h0)) (proj₂ hx)
... | inj₂ h0 =
  let hneg =
        subst (λ t → -ℝ x ≤ℝ t) negMinusOneℝ (negℝ-order (proj₁ hx))
  in subst (λ t → t ≤ℝ 1ℝ) (sym (absOfNonpositive h0)) hneg

absSubSym : ∀ (a b : ℝ) → absℝ (a -ℝ b) ≡ absℝ (b -ℝ a)
absSubSym a b =
  trans (sym (absNeg (a -ℝ b))) (cong absℝ (negℝ-sub a b))

absSubLeTwo : ∀ {a b : ℝ} → RangeNegOneOne a → RangeNegOneOne b →
  absℝ (a -ℝ b) ≤ℝ twoℝ
absSubLeTwo {a} {b} ha hb =
  let htri = absSubadditive a b
      hsum =
        +-mono-≤ (absLeOneOfRange ha) (absLeOneOfRange hb)
  in ≤ℝ-trans htri hsum

absDiffEqOfLe : ∀ {a b : ℝ} → b ≤ℝ a → absℝ (a -ℝ b) ≡ a -ℝ b
absDiffEqOfLe hba = absOfNonnegative (DASHI.Foundations.RealAnalysisAxioms.subNonnegative hba)

absDiffEqOfGe : ∀ {a b : ℝ} → a ≤ℝ b → absℝ (a -ℝ b) ≡ b -ℝ a
absDiffEqOfGe {a} {b} hab =
  trans (absSubSym a b) (absOfNonnegative (DASHI.Foundations.RealAnalysisAxioms.subNonnegative hab))

productAbsLeOne : ∀ {a b : ℝ} → RangeNegOneOne a → RangeNegOneOne b →
  absℝ (a *ℝ b) ≤ℝ 1ℝ
productAbsLeOne {a} {b} ha hb =
  let hprod =
        mulMonotoneNonnegative (absNonnegative a) (absLeOneOfRange ha)
          (absNonnegative b) (absLeOneOfRange hb)
      hprod' =
        subst (λ t → t ≤ℝ 1ℝ *ℝ 1ℝ) (sym (absMul a b)) hprod
  in subst (λ t → absℝ (a *ℝ b) ≤ℝ t) (mulOneʳ 1ℝ) hprod'

productLeOneRange : ∀ {a b : ℝ} → RangeNegOneOne a → RangeNegOneOne b →
  a *ℝ b ≤ℝ 1ℝ
productLeOneRange {a} {b} ha hb =
  ≤ℝ-trans (leAbs (a *ℝ b)) (productAbsLeOne ha hb)

negOneLeProduct : ∀ {a b : ℝ} → RangeNegOneOne a → RangeNegOneOne b →
  -ℝ 1ℝ ≤ℝ a *ℝ b
negOneLeProduct {a} {b} ha hb =
  let hneg =
        negℝ-order (productAbsLeOne ha hb)
  in ≤ℝ-trans hneg (negAbsLe (a *ℝ b))

absDiffLeTwoMinusSum : ∀ {a b : ℝ} → RangeNegOneOne a → RangeNegOneOne b →
  absℝ (a -ℝ b) ≤ℝ twoℝ -ℝ a -ℝ b
absDiffLeTwoMinusSum {a} {b} ha hb with ≤ℝ-total a b
... | inj₁ hab =
  let hb2 = leTwoMinusSelf (proj₂ hb)
      h = subRightMono a hb2
      h' =
        subst (λ t → b -ℝ a ≤ℝ t) (subSubComm twoℝ b a) h
      habs = absDiffEqOfGe hab
  in subst (λ t → t ≤ℝ twoℝ -ℝ a -ℝ b) (sym habs) h'
... | inj₂ hba =
  let ha2 = leTwoMinusSelf (proj₂ ha)
      h = subRightMono b ha2
      habs = absDiffEqOfLe hba
  in subst (λ t → t ≤ℝ twoℝ -ℝ a -ℝ b) (sym habs) h

absDiffLeTwoPlusSum : ∀ {a b : ℝ} → RangeNegOneOne a → RangeNegOneOne b →
  absℝ (a -ℝ b) ≤ℝ twoℝ +ℝ a +ℝ b
absDiffLeTwoPlusSum {a} {b} ha hb with ≤ℝ-total a b
... | inj₁ hab =
  let hnegA = negLeOneOfLower (negOneLeOfRange ha)
      h1 = addLeftMono b hnegA
      h1' =
        subst (λ t → t ≤ℝ b +ℝ 1ℝ) (sym (subEqAddNeg b a)) h1
      hone = oneLeTwoPlusOfLower (negOneLeOfRange ha)
      h2 = addLeftMono b hone
      h2' =
        subst (λ t → b +ℝ 1ℝ ≤ℝ t) (+-comm b (twoℝ +ℝ a)) h2
      h = ≤ℝ-trans h1' h2'
      habs = absDiffEqOfGe hab
  in subst (λ t → t ≤ℝ twoℝ +ℝ a +ℝ b) (sym habs) h
... | inj₂ hba =
  let hnegB = negLeOneOfLower (negOneLeOfRange hb)
      h1 = addLeftMono a hnegB
      h1' =
        subst (λ t → t ≤ℝ a +ℝ 1ℝ) (sym (subEqAddNeg a b)) h1
      hone = oneLeTwoPlusOfLower (negOneLeOfRange hb)
      h2 = addLeftMono a hone
      hrew =
        trans (sym (+-assoc a twoℝ b))
          (cong (λ t → t +ℝ b) (+-comm a twoℝ))
      h2' =
        subst (λ t → a +ℝ 1ℝ ≤ℝ t) hrew h2
      h = ≤ℝ-trans h1' h2'
      habs = absDiffEqOfLe hba
  in subst (λ t → t ≤ℝ twoℝ +ℝ a +ℝ b) (sym habs) h

lowerNonpos : ∀ {a b : ℝ} → RangeNegOneOne a → RangeNegOneOne b →
  a *ℝ b -ℝ 1ℝ -ℝ absℝ (a -ℝ b) ≤ℝ 0ℝ
lowerNonpos {a} {b} ha hb =
  let hp1 = subNonpos (productLeOneRange ha hb)
      hpAbs =
        ≤ℝ-trans hp1 (absNonnegative (a -ℝ b))
  in subNonpos hpAbs

zeroLeUpper : ∀ {a b : ℝ} → RangeNegOneOne a → RangeNegOneOne b →
  0ℝ ≤ℝ a *ℝ b +ℝ threeℝ -ℝ absℝ (a -ℝ b)
zeroLeUpper {a} {b} ha hb =
  let hd2 = absSubLeTwo ha hb
      hbase = DASHI.Foundations.RealAnalysisAxioms.subNonnegative hd2
      hnegOne =
        subst (λ t → t ≤ℝ a *ℝ b) (negEqSubZero 1ℝ) (negOneLeProduct ha hb)
      hmono =
        addRightMono (threeℝ -ℝ absℝ (a -ℝ b)) hnegOne
      hleftEq =
        trans (addSubAssoc minusOneℝ threeℝ (absℝ (a -ℝ b)))
          (cong (λ t → t -ℝ absℝ (a -ℝ b)) (predSucc twoℝ))
      hleft =
        subst (λ t → 0ℝ ≤ℝ t) (sym hleftEq) hbase
      hright =
        subst (λ t → minusOneℝ +ℝ (threeℝ -ℝ absℝ (a -ℝ b)) ≤ℝ t)
          (addSubAssoc (a *ℝ b) threeℝ (absℝ (a -ℝ b))) hmono
  in ≤ℝ-trans hleft hright

mixedRightCornerLe : ∀ {a b : ℝ} →
  (1ℝ -ℝ a) *ℝ (1ℝ +ℝ b)
    ≤ℝ 1ℝ -ℝ a *ℝ b +ℝ absℝ (a -ℝ b)
mixedRightCornerLe {a} {b} =
  let h =
        addLeftMono (1ℝ -ℝ a *ℝ b) (negLeAbs (a -ℝ b))
      h' =
        subst (λ t → t ≤ℝ 1ℝ -ℝ a *ℝ b +ℝ absℝ (a -ℝ b))
          (sym (subEqAddNeg (1ℝ -ℝ a *ℝ b) (a -ℝ b))) h
  in subst (λ t → t ≤ℝ 1ℝ -ℝ a *ℝ b +ℝ absℝ (a -ℝ b))
       (sym (oneMinusMulOnePlus a b)) h'

mixedLeftCornerLe : ∀ {a b : ℝ} →
  (1ℝ +ℝ a) *ℝ (1ℝ -ℝ b)
    ≤ℝ 1ℝ -ℝ a *ℝ b +ℝ absℝ (a -ℝ b)
mixedLeftCornerLe {a} {b} =
  let h =
        addLeftMono (1ℝ -ℝ a *ℝ b) (leAbs (a -ℝ b))
  in subst (λ t → t ≤ℝ 1ℝ -ℝ a *ℝ b +ℝ absℝ (a -ℝ b))
       (sym (onePlusMulOneMinus a b)) h

sameLeftCornerLe : ∀ {a b : ℝ} → RangeNegOneOne a → RangeNegOneOne b →
  (1ℝ -ℝ a) *ℝ (1ℝ -ℝ b)
    ≤ℝ a *ℝ b +ℝ threeℝ -ℝ absℝ (a -ℝ b)
sameLeftCornerLe {a} {b} ha hb =
  let hd = absDiffLeTwoPlusSum ha hb
      hbase =
        subLeftMono (a *ℝ b +ℝ threeℝ) hd
      hleft =
        subst (λ t → t ≤ℝ a *ℝ b +ℝ threeℝ -ℝ absℝ (a -ℝ b))
          (addThreeSubTwoPlus (a *ℝ b) a b) hbase
      hleft' = hleft
  in subst (λ t → t ≤ℝ a *ℝ b +ℝ threeℝ -ℝ absℝ (a -ℝ b))
       (sym (oneMinusMulOneMinus a b)) hleft'

sameRightCornerLe : ∀ {a b : ℝ} → RangeNegOneOne a → RangeNegOneOne b →
  (1ℝ +ℝ a) *ℝ (1ℝ +ℝ b)
    ≤ℝ a *ℝ b +ℝ threeℝ -ℝ absℝ (a -ℝ b)
sameRightCornerLe {a} {b} ha hb =
  let hd = absDiffLeTwoMinusSum ha hb
      hbase =
        subLeftMono (a *ℝ b +ℝ threeℝ) hd
      hleft =
        subst (λ t → t ≤ℝ a *ℝ b +ℝ threeℝ -ℝ absℝ (a -ℝ b))
          (addThreeSubTwoMinus (a *ℝ b) a b) hbase
  in subst (λ t → t ≤ℝ a *ℝ b +ℝ threeℝ -ℝ absℝ (a -ℝ b))
       (sym (onePlusMulOnePlus a b)) hleft

lowerVsMixedRight : ∀ {a b : ℝ} →
  a *ℝ b -ℝ 1ℝ -ℝ absℝ (a -ℝ b)
    ≤ℝ -ℝ ((1ℝ -ℝ a) *ℝ (1ℝ +ℝ b))
lowerVsMixedRight {a} {b} =
  let h =
        negℝ-order (mixedRightCornerLe {a} {b})
  in subst (λ t → t ≤ℝ -ℝ ((1ℝ -ℝ a) *ℝ (1ℝ +ℝ b)))
       (negOneMinusPlus (a *ℝ b) (absℝ (a -ℝ b))) h

lowerVsMixedLeft : ∀ {a b : ℝ} →
  a *ℝ b -ℝ 1ℝ -ℝ absℝ (a -ℝ b)
    ≤ℝ -ℝ ((1ℝ +ℝ a) *ℝ (1ℝ -ℝ b))
lowerVsMixedLeft {a} {b} =
  let h =
        negℝ-order (mixedLeftCornerLe {a} {b})
  in subst (λ t → t ≤ℝ -ℝ ((1ℝ +ℝ a) *ℝ (1ℝ -ℝ b)))
       (negOneMinusPlus (a *ℝ b) (absℝ (a -ℝ b))) h

negOnePlusEqMinusOneMinus : ∀ (a : ℝ) → -ℝ (1ℝ +ℝ a) ≡ minusOneℝ -ℝ a
negOnePlusEqMinusOneMinus a =
  let h1 = negℝ-add 1ℝ a
      h2 =
        cong (λ t → t +ℝ (-ℝ a)) (negEqSubZero 1ℝ)
      h3 =
        sym (subEqAddNeg minusOneℝ a)
  in trans h1 (trans h2 h3)

uUpperBound : ∀ {x a : ℝ} → RangeNegOneOne x → x -ℝ a ≤ℝ 1ℝ -ℝ a
uUpperBound {x} {a} hx = subRightMono a (proj₂ hx)

uLowerBound : ∀ {x a : ℝ} → RangeNegOneOne x → -ℝ (1ℝ +ℝ a) ≤ℝ x -ℝ a
uLowerBound {x} {a} hx =
  let h = subRightMono a (proj₁ hx)
  in subst (λ t → t ≤ℝ x -ℝ a) (sym (negOnePlusEqMinusOneMinus a)) h

negUBound : ∀ {x a : ℝ} → RangeNegOneOne x → -ℝ (x -ℝ a) ≤ℝ 1ℝ +ℝ a
negUBound {x} {a} hx =
  subst (λ t → -ℝ (x -ℝ a) ≤ℝ t) (negℝ-involutive (1ℝ +ℝ a))
    (negℝ-order (uLowerBound {x} {a} hx))

uvUpperSame : ∀ {u v β δ : ℝ} →
  0ℝ ≤ℝ u → u ≤ℝ β → 0ℝ ≤ℝ v → v ≤ℝ δ → u *ℝ v ≤ℝ β *ℝ δ
uvUpperSame = mulMonotoneNonnegative

uvLowerMixedRight : ∀ {u v β γ : ℝ} →
  0ℝ ≤ℝ u → u ≤ℝ β → v ≤ℝ 0ℝ → -ℝ v ≤ℝ γ →
  -ℝ (β *ℝ γ) ≤ℝ u *ℝ v
uvLowerMixedRight {u} {v} {β} {γ} hu huβ hv hnvγ =
  let hnv = negNonnegativeOfNonpositive hv
      hprod = mulMonotoneNonnegative hu huβ hnv hnvγ
      hneg = negℝ-order hprod
      huv =
        trans (sym (negℝ-mulʳ u (-ℝ v)))
          (cong (λ t → u *ℝ t) (negℝ-involutive v))
  in subst (λ t → -ℝ (β *ℝ γ) ≤ℝ t) huv hneg

uvLowerMixedLeft : ∀ {u v α δ : ℝ} →
  u ≤ℝ 0ℝ → -ℝ u ≤ℝ α → 0ℝ ≤ℝ v → v ≤ℝ δ →
  -ℝ (α *ℝ δ) ≤ℝ u *ℝ v
uvLowerMixedLeft {u} {v} {α} {δ} hu hnuα hv hvδ =
  let hnu = negNonnegativeOfNonpositive hu
      hprod = mulMonotoneNonnegative hnu hnuα hv hvδ
      hneg = negℝ-order hprod
      huv =
        trans (sym (negℝ-mulˡ (-ℝ u) v))
          (cong (λ t → t *ℝ v) (negℝ-involutive u))
  in subst (λ t → -ℝ (α *ℝ δ) ≤ℝ t) huv hneg

uvUpperMixedBothNeg : ∀ {u v α γ : ℝ} →
  u ≤ℝ 0ℝ → -ℝ u ≤ℝ α → v ≤ℝ 0ℝ → -ℝ v ≤ℝ γ →
  u *ℝ v ≤ℝ α *ℝ γ
uvUpperMixedBothNeg {u} {v} {α} {γ} hu hnuα hv hnvγ =
  let hnu = negNonnegativeOfNonpositive hu
      hnv = negNonnegativeOfNonpositive hv
      hprod =
        mulMonotoneNonnegative hnu hnuα hnv hnvγ
  in subst (λ t → t ≤ℝ α *ℝ γ) (negℝ-mul-neg u v) hprod

lowerPlusFourIsUpper : ∀ (p d : ℝ) →
  (p -ℝ 1ℝ -ℝ d) +ℝ fourℝ ≡ p +ℝ threeℝ -ℝ d
lowerPlusFourIsUpper = lowerPlusFourEq

upperMinusLowerEqFour : ∀ (l : ℝ) → (l +ℝ fourℝ) -ℝ l ≡ fourℝ
upperMinusLowerEqFour l =
  trans (cong (λ t → t -ℝ l) (+-comm l fourℝ)) (DASHI.Foundations.RealAnalysisAxioms.addSubCancel fourℝ l)

lowerBoundConstructed :
  ∀ a b → RangeNegOneOne a → RangeNegOneOne b →
  ∀ x y → RangeNegOneOne x → RangeNegOneOne y →
  a *ℝ b -ℝ 1ℝ -ℝ absℝ (a -ℝ b) ≤ℝ (x -ℝ a) *ℝ (y -ℝ b)
lowerBoundConstructed a b ha hb x y hx hy
  with ≤ℝ-total 0ℝ (x -ℝ a) | ≤ℝ-total 0ℝ (y -ℝ b)
... | inj₁ hu | inj₁ hv =
  ≤ℝ-trans (lowerNonpos ha hb) (mulNonnegative hu hv)
... | inj₁ hu | inj₂ hv =
  let hcorner =
        uvLowerMixedRight hu (uUpperBound hx) hv (negUBound {y} {b} hy)
  in ≤ℝ-trans (lowerVsMixedRight {a} {b}) hcorner
... | inj₂ hu | inj₁ hv =
  let hcorner =
        uvLowerMixedLeft hu (negUBound {x} {a} hx) hv (uUpperBound {y} {b} hy)
  in ≤ℝ-trans (lowerVsMixedLeft {a} {b}) hcorner
... | inj₂ hu | inj₂ hv =
  let hprod =
        mulNonnegative (negNonnegativeOfNonpositive hu)
          (negNonnegativeOfNonpositive hv)
      hnonneg =
        subst (λ t → 0ℝ ≤ℝ t) (negℝ-mul-neg (x -ℝ a) (y -ℝ b)) hprod
  in ≤ℝ-trans (lowerNonpos ha hb) hnonneg

upperTargetConstructed :
  ∀ a b → RangeNegOneOne a → RangeNegOneOne b →
  ∀ x y → RangeNegOneOne x → RangeNegOneOne y →
  (x -ℝ a) *ℝ (y -ℝ b) ≤ℝ a *ℝ b +ℝ threeℝ -ℝ absℝ (a -ℝ b)
upperTargetConstructed a b ha hb x y hx hy
  with ≤ℝ-total 0ℝ (x -ℝ a) | ≤ℝ-total 0ℝ (y -ℝ b)
... | inj₁ hu | inj₁ hv =
  let hcorner =
        uvUpperSame hu (uUpperBound hx) hv (uUpperBound {y} {b} hy)
  in ≤ℝ-trans hcorner (sameLeftCornerLe ha hb)
... | inj₁ hu | inj₂ hv =
  let hw =
        mulNonnegative hu (negNonnegativeOfNonpositive hv)
      hneg =
        subst (λ t → -ℝ ((x -ℝ a) *ℝ (-ℝ (y -ℝ b))) ≤ℝ t)
          negZeroℝ (negℝ-order hw)
      huv =
        trans (sym (negℝ-mulʳ (x -ℝ a) (-ℝ (y -ℝ b))))
          (cong (λ t → (x -ℝ a) *ℝ t) (negℝ-involutive (y -ℝ b)))
      hnonpos =
        subst (λ t → t ≤ℝ 0ℝ) huv hneg
  in ≤ℝ-trans hnonpos (zeroLeUpper ha hb)
... | inj₂ hu | inj₁ hv =
  let hw =
        mulNonnegative (negNonnegativeOfNonpositive hu) hv
      hneg =
        subst (λ t → -ℝ ((-ℝ (x -ℝ a)) *ℝ (y -ℝ b)) ≤ℝ t)
          negZeroℝ (negℝ-order hw)
      huv =
        trans (sym (negℝ-mulˡ (-ℝ (x -ℝ a)) (y -ℝ b)))
          (cong (λ t → t *ℝ (y -ℝ b)) (negℝ-involutive (x -ℝ a)))
      hnonpos =
        subst (λ t → t ≤ℝ 0ℝ) huv hneg
  in ≤ℝ-trans hnonpos (zeroLeUpper ha hb)
... | inj₂ hu | inj₂ hv =
  let hcorner =
        uvUpperMixedBothNeg hu (negUBound {x} {a} hx) hv
          (negUBound {y} {b} hy)
  in ≤ℝ-trans hcorner (sameRightCornerLe ha hb)

record CenteredProductOscillation (a b : ℝ) : Set where
  field
    lower upper : ℝ
    lowerBound : ∀ x y → RangeNegOneOne x → RangeNegOneOne y →
      lower ≤ℝ (x -ℝ a) *ℝ (y -ℝ b)
    upperBound : ∀ x y → RangeNegOneOne x → RangeNegOneOne y →
      (x -ℝ a) *ℝ (y -ℝ b) ≤ℝ upper
    width : upper -ℝ lower ≡ fourℝ

constructCenteredProductOscillation :
  ∀ a b → RangeNegOneOne a → RangeNegOneOne b → CenteredProductOscillation a b
constructCenteredProductOscillation a b ha hb =
  record
    { lower = a *ℝ b -ℝ 1ℝ -ℝ absℝ (a -ℝ b)
    ; upper = (a *ℝ b -ℝ 1ℝ -ℝ absℝ (a -ℝ b)) +ℝ fourℝ
    ; lowerBound = lowerBoundConstructed a b ha hb
    ; upperBound = λ x y hx hy →
        subst (λ t → (x -ℝ a) *ℝ (y -ℝ b) ≤ℝ t)
          (sym (lowerPlusFourIsUpper (a *ℝ b) (absℝ (a -ℝ b))))
          (upperTargetConstructed a b ha hb x y hx hy)
    ; width = upperMinusLowerEqFour (a *ℝ b -ℝ 1ℝ -ℝ absℝ (a -ℝ b))
    }

open CenteredProductOscillation public

record ContinuousWilsonArithmetic
    {Converges : (Nat → ℝ) → ℝ → Set}
    (quotient : Quotient.RealQuotientConvergenceAuthority Converges) : Set₁ where
  field
    strictToNonnegative : ∀ {a : ℝ} → 0ℝ <ℝ a → 0ℝ ≤ℝ a
    strictToNonzero : ∀ {a : ℝ} → 0ℝ <ℝ a → Quotient.Nonzero quotient a
    positiveAddRight : ∀ {a b : ℝ} → 0ℝ <ℝ b → a <ℝ a +ℝ b
    twoNonzero : Quotient.Nonzero quotient (1ℝ +ℝ 1ℝ)
    divideZero : ∀ denominator → Quotient.Nonzero quotient denominator →
      Quotient.divide quotient 0ℝ denominator ≡ 0ℝ
    divideSelf : ∀ denominator → Quotient.Nonzero quotient denominator →
      Quotient.divide quotient denominator denominator ≡ 1ℝ
    divideAdd : ∀ numeratorLeft numeratorRight denominator →
      Quotient.Nonzero quotient denominator →
      Quotient.divide quotient (numeratorLeft +ℝ numeratorRight) denominator
      ≡ Quotient.divide quotient numeratorLeft denominator
        +ℝ Quotient.divide quotient numeratorRight denominator
    divideScale : ∀ scalar numerator denominator →
      Quotient.Nonzero quotient denominator →
      Quotient.divide quotient (scalar *ℝ numerator) denominator
      ≡ scalar *ℝ Quotient.divide quotient numerator denominator
    divideNonnegative : ∀ numerator denominator → 0ℝ ≤ℝ numerator →
      Quotient.Nonzero quotient denominator →
      0ℝ ≤ℝ Quotient.divide quotient numerator denominator
    goodMassEqOneMinus : ∀ {q m : ℝ} → q +ℝ m ≡ 1ℝ →
      m ≡ 1ℝ -ℝ q
    restrictedAddPointwise : ∀ {X : Set} (χ f g : X → ℝ) (x : X) →
      (1ℝ -ℝ χ x) *ℝ (f x +ℝ g x)
      ≡ (1ℝ -ℝ χ x) *ℝ f x +ℝ (1ℝ -ℝ χ x) *ℝ g x
    restrictedScalePointwise : ∀ {X : Set} (χ : X → ℝ) (scalar : ℝ)
      (f : X → ℝ) (x : X) →
      (1ℝ -ℝ χ x) *ℝ (scalar *ℝ f x)
      ≡ scalar *ℝ ((1ℝ -ℝ χ x) *ℝ f x)
    halfNonnegative : ∀ (x : ℝ) → 0ℝ ≤ℝ x →
      0ℝ ≤ℝ Quotient.divide quotient x (1ℝ +ℝ 1ℝ)
    addNonnegative : ∀ {a b : ℝ} → 0ℝ ≤ℝ a → 0ℝ ≤ℝ b → 0ℝ ≤ℝ a +ℝ b
    productNonnegative : ∀ {a b : ℝ} → 0ℝ ≤ℝ a → 0ℝ ≤ℝ b → 0ℝ ≤ℝ a *ℝ b
    productLeOne : ∀ {a b : ℝ} →
      0ℝ ≤ℝ a → a ≤ℝ 1ℝ → 0ℝ ≤ℝ b → b ≤ℝ 1ℝ → a *ℝ b ≤ℝ 1ℝ
    subNonnegative : ∀ {a b : ℝ} → b ≤ℝ a → 0ℝ ≤ℝ a -ℝ b
    subPositiveOfLess : ∀ {a b : ℝ} → a <ℝ b → 0ℝ <ℝ b -ℝ a
    leOfSubNonnegative : ∀ {a b : ℝ} → 0ℝ ≤ℝ a -ℝ b → b ≤ℝ a
    subLeFromAddLe : ∀ {a b c : ℝ} → a ≤ℝ b +ℝ c → a -ℝ b ≤ℝ c
    leAddNonnegative : ∀ {a b : ℝ} → 0ℝ ≤ℝ b → a ≤ℝ a +ℝ b
    oneMinusLeOne : ∀ {a : ℝ} → 0ℝ ≤ℝ a → 1ℝ -ℝ a ≤ℝ 1ℝ
    addSubCancel : ∀ (a b : ℝ) → a +ℝ (b -ℝ a) ≡ b
    partitionUnityExpand : ∀ (χ h : ℝ) →
      χ *ℝ h +ℝ (1ℝ -ℝ χ) *ℝ h ≡ h
    oneMinusMulLeSum : ∀ {a q s : ℝ} →
      0ℝ ≤ℝ a → a ≤ℝ 1ℝ → 0ℝ ≤ℝ q → q ≤ℝ 1ℝ →
      1ℝ -ℝ q ≤ℝ s →
      1ℝ -ℝ ((1ℝ -ℝ a) *ℝ q) ≤ℝ a +ℝ s
    absBound : ∀ (a r : ℝ) →
      0ℝ ≤ℝ r → (0ℝ -ℝ r) ≤ℝ a → a ≤ℝ r → absℝ a ≤ℝ r
    unitIntervalDifferenceBounds : ∀ {x y : ℝ} →
      0ℝ ≤ℝ x → x ≤ℝ 1ℝ → 0ℝ ≤ℝ y → y ≤ℝ 1ℝ →
      ((0ℝ -ℝ 1ℝ) ≤ℝ x -ℝ y) × (x -ℝ y ≤ℝ 1ℝ)
    negOneOneProductBounds : ∀ {x y : ℝ} →
      (0ℝ -ℝ 1ℝ) ≤ℝ x → x ≤ℝ 1ℝ →
      (0ℝ -ℝ 1ℝ) ≤ℝ y → y ≤ℝ 1ℝ →
      ((0ℝ -ℝ 1ℝ) ≤ℝ x *ℝ y) × (x *ℝ y ≤ℝ 1ℝ)
    signedMidpointBounds : ∀ x y →
      RangeNegOneOne x → RangeNegOneOne y →
      RangeNegOneOne (Quotient.divide quotient (x +ℝ y) twoℝ)
    signedDifferenceBounds : ∀ {x y : ℝ} →
      RangeNegOneOne x → RangeNegOneOne y →
      ((0ℝ -ℝ twoℝ) ≤ℝ x -ℝ y) × (x -ℝ y ≤ℝ twoℝ)
    signedProductBounds : ∀ {x y : ℝ} →
      (0ℝ -ℝ twoℝ) ≤ℝ x → x ≤ℝ twoℝ →
      (0ℝ -ℝ twoℝ) ≤ℝ y → y ≤ℝ twoℝ →
      ((0ℝ -ℝ fourℝ) ≤ℝ x *ℝ y) × (x *ℝ y ≤ℝ fourℝ)
    centeredProductOscillation : ∀ a b →
      RangeNegOneOne a → RangeNegOneOne b →
      CenteredProductOscillation a b
    shiftAbsoluteBoundOfInterval :
      ∀ (shift χhMean goodNumer q lower upper : ℝ) →
      shift ≡ χhMean -ℝ q *ℝ goodNumer →
      lower *ℝ q ≤ℝ χhMean →
      χhMean ≤ℝ upper *ℝ q →
      lower ≤ℝ goodNumer →
      goodNumer ≤ℝ upper →
      0ℝ ≤ℝ q →
      absℝ shift ≤ℝ (upper -ℝ lower) *ℝ q
    centeredProductExpectation :
      ∀ {Configuration : Set}
        (E : (Configuration → ℝ) → ℝ)
        (addLaw : ∀ f g → E (λ x → f x +ℝ g x) ≡ E f +ℝ E g)
        (scaleLaw : ∀ scalar f → E (λ x → scalar *ℝ f x) ≡ scalar *ℝ E f)
        (extLaw : ∀ f g → (∀ x → f x ≡ g x) → E f ≡ E g)
        (f g : Configuration → ℝ) (a b : ℝ) →
      E (λ x → (f x -ℝ a) *ℝ (g x -ℝ b))
      ≡ E (λ x → f x *ℝ g x) -ℝ a *ℝ E g -ℝ b *ℝ E f +ℝ a *ℝ b
    covarianceMidpointIdentity :
      ∀ (μF νF μG νG μFG νFG : ℝ) →
      (μFG -ℝ μG *ℝ μF) -ℝ (νFG -ℝ νG *ℝ νF)
      ≡
      let a = Quotient.divide quotient (μF +ℝ νF) (1ℝ +ℝ 1ℝ)
          b = Quotient.divide quotient (μG +ℝ νG) (1ℝ +ℝ 1ℝ)
      in
      (μFG -ℝ a *ℝ μG -ℝ b *ℝ μF +ℝ a *ℝ b)
        -ℝ (νFG -ℝ a *ℝ νG -ℝ b *ℝ νF +ℝ a *ℝ b)
    meanRestrictionBounds :
      ∀ {Configuration : Set}
        (E : (Configuration → ℝ) → ℝ)
        (addLaw : ∀ f g → E (λ x → f x +ℝ g x) ≡ E f +ℝ E g)
        (scaleLaw : ∀ scalar f → E (λ x → scalar *ℝ f x) ≡ scalar *ℝ E f)
        (positiveLaw : ∀ f → (∀ x → 0ℝ ≤ℝ f x) → 0ℝ ≤ℝ E f)
        (extLaw : ∀ f g → (∀ x → f x ≡ g x) → E f ≡ E g)
        (χ h : Configuration → ℝ) (q goodMean m M : ℝ) →
      (∀ x → 0ℝ ≤ℝ χ x) →
      (∀ x → χ x ≤ℝ 1ℝ) →
      (∀ x → m ≤ℝ h x) →
      (∀ x → h x ≤ℝ M) →
      goodMean ≡ E (λ x → (1ℝ -ℝ χ x) *ℝ h x) →
      q ≡ E χ →
      (m *ℝ q ≤ℝ E (λ x → χ x *ℝ h x)) ×
      (E (λ x → χ x *ℝ h x) ≤ℝ M *ℝ q) ×
      (m ≤ℝ Quotient.divide quotient goodMean (1ℝ -ℝ q)) ×
      (Quotient.divide quotient goodMean (1ℝ -ℝ q) ≤ℝ M)
    shiftIdentityAlgebra :
      ∀ (shift χhMean goodNumer goodMass q : ℝ) →
      shift ≡ χhMean +ℝ goodNumer -ℝ
        Quotient.divide quotient goodNumer (1ℝ -ℝ q) →
      q +ℝ goodMass ≡ 1ℝ →
      shift ≡ χhMean -ℝ q *ℝ
        Quotient.divide quotient goodNumer (1ℝ -ℝ q)
    unitShiftAbsoluteBound :
      ∀ (shift χhMean goodMean q : ℝ) →
      shift ≡ χhMean -ℝ q *ℝ goodMean →
      (0ℝ -ℝ 1ℝ) *ℝ q ≤ℝ χhMean →
      χhMean ≤ℝ 1ℝ *ℝ q →
      (0ℝ -ℝ 1ℝ) ≤ℝ goodMean →
      goodMean ≤ℝ 1ℝ →
      0ℝ ≤ℝ q →
      absℝ shift ≤ℝ (1ℝ +ℝ 1ℝ +ℝ (1ℝ +ℝ 1ℝ)) *ℝ q
    halfLeOneOfUnit : ∀ (x : ℝ) → 0ℝ ≤ℝ x → x ≤ℝ 1ℝ +ℝ 1ℝ →
      Quotient.divide quotient x (1ℝ +ℝ 1ℝ) ≤ℝ 1ℝ

open ContinuousWilsonArithmetic public

-- The low/high thresholds are SELECTED ONCE, not universally quantified
-- independently for every value.  The previous signatures let threshold =
-- value in both fields and thus forced 0ℝ ≡ 1ℝ in every inhabitant.
-- A true physical instantiation still requires an actual real, continuous
-- measurable interpolating function on the selected SU(N) test algebra.
record ContinuousClampSource : Set₁ where
  field
    lowerThreshold upperThreshold : ℝ
    lowerThresholdPositive : 0ℝ <ℝ lowerThreshold
    lowerBelowUpper : lowerThreshold <ℝ upperThreshold
    upperThresholdAtMostOne : upperThreshold ≤ℝ 1ℝ
    clamp : ℝ → ℝ
    congruent : ∀ {value value'} → value ≡ value' →
      clamp value ≡ clamp value'
    clampNonnegative : ∀ value → 0ℝ ≤ℝ clamp value
    clampLeOne : ∀ value → clamp value ≤ℝ 1ℝ
    clampZeroBelow : ∀ {value} →
      value ≤ℝ lowerThreshold → clamp value ≡ 0ℝ
    clampOneAbove : ∀ {value} →
      upperThreshold ≤ℝ value → clamp value ≡ 1ℝ

open ContinuousClampSource public

halfℝ : ℝ
halfℝ = 1ℝ /ℝ twoℝ

oneLtTwoℝ : 1ℝ <ℝ twoℝ
oneLtTwoℝ = DASHI.Foundations.RealAnalysisAxioms.positiveAddRight zeroLtOne

twoPositiveℝ : 0ℝ <ℝ twoℝ
twoPositiveℝ = DASHI.Foundations.RealAnalysisAxioms.addPositive zeroLtOne zeroLtOne

halfPositiveℝ : 0ℝ <ℝ halfℝ
halfPositiveℝ = divℝ-positive zeroLtOne twoPositiveℝ

halfLtOneℝ : halfℝ <ℝ 1ℝ
halfLtOneℝ = divℝ-lt-one oneLtTwoℝ twoPositiveℝ

clampHalfOneDenominatorPositive : 0ℝ <ℝ 1ℝ -ℝ halfℝ
clampHalfOneDenominatorPositive =
  subPositiveOfLt halfℝ 1ℝ halfLtOneℝ

clampHalfOne : ℝ → ℝ
clampHalfOne value with ≤ℝ-total value halfℝ | ≤ℝ-total 1ℝ value
... | inj₁ _ | _ = 0ℝ
... | inj₂ _ | inj₁ _ = 1ℝ
... | inj₂ _ | inj₂ _ =
  (value -ℝ halfℝ) /ℝ (1ℝ -ℝ halfℝ)

clampHalfOneNonnegative : ∀ value → 0ℝ ≤ℝ clampHalfOne value
clampHalfOneNonnegative value with ≤ℝ-total value halfℝ | ≤ℝ-total 1ℝ value
... | inj₁ _ | _ = ≤ℝ-refl
... | inj₂ _ | inj₁ _ =
  DASHI.Foundations.RealAnalysisAxioms.strictToNonnegative zeroLtOne
... | inj₂ halfLeValue | inj₂ _ =
  divℝ-nonnegative
    (DASHI.Foundations.RealAnalysisAxioms.subNonnegative halfLeValue)
    clampHalfOneDenominatorPositive

clampHalfOneLeOne : ∀ value → clampHalfOne value ≤ℝ 1ℝ
clampHalfOneLeOne value with ≤ℝ-total value halfℝ | ≤ℝ-total 1ℝ value
... | inj₁ _ | _ =
  DASHI.Foundations.RealAnalysisAxioms.strictToNonnegative zeroLtOne
... | inj₂ _ | inj₁ _ = ≤ℝ-refl
... | inj₂ _ | inj₂ valueLeOne =
  divℝ-le-one (subRightMono halfℝ valueLeOne)
    clampHalfOneDenominatorPositive

clampHalfOneZeroBelow : ∀ {value} → value ≤ℝ halfℝ → clampHalfOne value ≡ 0ℝ
clampHalfOneZeroBelow {value} valueLeHalf with
  ≤ℝ-total value halfℝ | ≤ℝ-total 1ℝ value
... | inj₁ _ | _ = refl
... | inj₂ halfLeValue | inj₁ oneLeValue =
  ⊥-elim (notLeOfLt halfLtOneℝ (≤ℝ-trans oneLeValue valueLeHalf))
... | inj₂ halfLeValue | inj₂ valueLeOne =
  let valueEqHalf = ≤ℝ-antisym valueLeHalf halfLeValue
      numeratorZero =
        subst (λ t → t -ℝ halfℝ ≡ 0ℝ) (sym valueEqHalf) (subSelf halfℝ)
      hnonneg =
        divℝ-nonnegative
          (DASHI.Foundations.RealAnalysisAxioms.subNonnegative halfLeValue)
          clampHalfOneDenominatorPositive
      hnonpos =
        subst (λ t → t /ℝ (1ℝ -ℝ halfℝ) ≤ℝ 0ℝ) (sym numeratorZero)
          (divℝ-nonpositive ≤ℝ-refl clampHalfOneDenominatorPositive)
  in ≤ℝ-antisym hnonpos hnonneg

clampHalfOneOneAbove : ∀ {value} → 1ℝ ≤ℝ value → clampHalfOne value ≡ 1ℝ
clampHalfOneOneAbove {value} oneLeValue with
  ≤ℝ-total value halfℝ | ≤ℝ-total 1ℝ value
... | inj₁ valueLeHalf | _ =
  ⊥-elim (notLeOfLt halfLtOneℝ (≤ℝ-trans oneLeValue valueLeHalf))
... | inj₂ _ | inj₁ _ = refl
... | inj₂ halfLeValue | inj₂ valueLeOne =
  let valueEqOne = ≤ℝ-antisym valueLeOne oneLeValue
      numeratorEqDen =
        cong (λ t → t -ℝ halfℝ) valueEqOne
      hle =
        divℝ-le-one (subRightMono halfℝ valueLeOne)
          clampHalfOneDenominatorPositive
      hge =
        subst (λ t → 1ℝ ≤ℝ t /ℝ (1ℝ -ℝ halfℝ)) (sym numeratorEqDen)
          (divℝ-one-le ≤ℝ-refl clampHalfOneDenominatorPositive)
  in ≤ℝ-antisym hle hge

minReal : ℝ → ℝ → ℝ
minReal a b with ≤ℝ-total a b
... | inj₁ _ = a
... | inj₂ _ = b

maxReal : ℝ → ℝ → ℝ
maxReal a b with ≤ℝ-total a b
... | inj₁ _ = b
... | inj₂ _ = a

minRealEqLeftOfLe : ∀ {a b : ℝ} → a ≤ℝ b → minReal a b ≡ a
minRealEqLeftOfLe {a} {b} hab with ≤ℝ-total a b
... | inj₁ _ = refl
... | inj₂ hba = ≤ℝ-antisym hba hab

minRealEqRightOfLe : ∀ {a b : ℝ} → b ≤ℝ a → minReal a b ≡ b
minRealEqRightOfLe {a} {b} hba with ≤ℝ-total a b
... | inj₁ hab = ≤ℝ-antisym hab hba
... | inj₂ _ = refl

maxRealEqLeftOfGe : ∀ {a b : ℝ} → b ≤ℝ a → maxReal a b ≡ a
maxRealEqLeftOfGe {a} {b} hba with ≤ℝ-total a b
... | inj₁ hab = ≤ℝ-antisym hba hab
... | inj₂ _ = refl

maxRealEqRightOfLe : ∀ {a b : ℝ} → a ≤ℝ b → maxReal a b ≡ b
maxRealEqRightOfLe {a} {b} hab with ≤ℝ-total a b
... | inj₁ _ = refl
... | inj₂ hba = ≤ℝ-antisym hab hba

clampHalfOneFormula : ∀ value →
  clampHalfOne value ≡
  maxReal 0ℝ (minReal 1ℝ ((value -ℝ halfℝ) /ℝ (1ℝ -ℝ halfℝ)))
clampHalfOneFormula value with ≤ℝ-total value halfℝ | ≤ℝ-total 1ℝ value
... | inj₁ valueLeHalf | _ =
  let tNonpos =
        divℝ-nonpositive (subNonpos valueLeHalf)
          clampHalfOneDenominatorPositive
      tLeOne =
        ≤ℝ-trans tNonpos
          (DASHI.Foundations.RealAnalysisAxioms.strictToNonnegative zeroLtOne)
      minEq = minRealEqRightOfLe tLeOne
      maxEq = maxRealEqLeftOfGe tNonpos
  in sym (trans (cong (λ z → maxReal 0ℝ z) minEq) maxEq)
... | inj₂ _ | inj₁ oneLeValue =
  let tGeOne =
        divℝ-one-le (subRightMono halfℝ oneLeValue)
          clampHalfOneDenominatorPositive
      minEq = minRealEqLeftOfLe tGeOne
      maxEq =
        maxRealEqRightOfLe
          (DASHI.Foundations.RealAnalysisAxioms.strictToNonnegative zeroLtOne)
  in sym (trans (cong (λ z → maxReal 0ℝ z) minEq) maxEq)
... | inj₂ halfLeValue | inj₂ valueLeOne =
  let tNonneg =
        divℝ-nonnegative
          (DASHI.Foundations.RealAnalysisAxioms.subNonnegative halfLeValue)
          clampHalfOneDenominatorPositive
      tLeOne =
        divℝ-le-one (subRightMono halfℝ valueLeOne)
          clampHalfOneDenominatorPositive
      minEq = minRealEqRightOfLe tLeOne
      maxEq = maxRealEqRightOfLe tNonneg
  in sym (trans (cong (λ z → maxReal 0ℝ z) minEq) maxEq)

constructContinuousClampSource : ContinuousClampSource
constructContinuousClampSource =
  record
    { lowerThreshold = halfℝ
    ; upperThreshold = 1ℝ
    ; lowerThresholdPositive = halfPositiveℝ
    ; lowerBelowUpper = halfLtOneℝ
    ; upperThresholdAtMostOne = ≤ℝ-refl
    ; clamp = clampHalfOne
    ; congruent = λ { refl → refl }
    ; clampNonnegative = clampHalfOneNonnegative
    ; clampLeOne = clampHalfOneLeOne
    ; clampZeroBelow = clampHalfOneZeroBelow
    ; clampOneAbove = clampHalfOneOneAbove
    }

------------------------------------------------------------------------
-- Exact source-repair check: a strict lower threshold is explicit and
-- may never be replaced by a universally quantified comparison cutoff.
-- This is a field projection, NOT the construction of physical Haar or
-- CMP116 source estimates.
------------------------------------------------------------------------

continuousClampFixedThresholds :
  (cut : ContinuousClampSource) →
  (0ℝ <ℝ ContinuousClampSource.lowerThreshold cut) ×
  (ContinuousClampSource.lowerThreshold cut
     <ℝ ContinuousClampSource.upperThreshold cut)
continuousClampFixedThresholds cut =
  ContinuousClampSource.lowerThresholdPositive cut ,
  ContinuousClampSource.lowerBelowUpper cut


record ContinuousExpectationAlgebra (Configuration : Set) : Set₁ where
  field
    E : (Configuration → ℝ) → ℝ
    EZero : E (λ _ → 0ℝ) ≡ 0ℝ
    EOne : E (λ _ → 1ℝ) ≡ 1ℝ
    EAdd : ∀ f g → E (λ x → f x +ℝ g x) ≡ E f +ℝ E g
    EScale : ∀ scalar f → E (λ x → scalar *ℝ f x) ≡ scalar *ℝ E f
    EPositive : ∀ f → (∀ x → 0ℝ ≤ℝ f x) → 0ℝ ≤ℝ E f
    EExt : ∀ f g → (∀ x → f x ≡ g x) → E f ≡ E g
    ECenteredProduct : ∀ f g a b →
      E (λ x → (f x -ℝ a) *ℝ (g x -ℝ b))
      ≡ E (λ x → f x *ℝ g x) -ℝ a *ℝ E g -ℝ b *ℝ E f +ℝ a *ℝ b

open ContinuousExpectationAlgebra public

record ContinuousWilsonSourceContract : Set₁ where
  field
    Configuration : Set
    PlaquetteIndex : Set
    expectation : ContinuousExpectationAlgebra Configuration
    -- RAW Wilson plaquette deficit 1 - ReTr(U_p)/N belongs to [0,2],
    -- NOT [0,1] (for SU(2), U_p=-I gives 2).  The clamp itself supplies
    -- the [0,1] range used by all contour and covariance proofs below.
    -- An actual instance must prove the source trace is the genuine
    -- normalized REAL complex matrix trace: cyclicity alone is insufficient.
    deficit : PlaquetteIndex → Configuration → ℝ
    deficitNonnegative : ∀ p links → 0ℝ ≤ℝ deficit p links
    deficitLeTwo : ∀ p links → deficit p links ≤ℝ (1ℝ +ℝ 1ℝ)
    gaugeInvariant : (Configuration → ℝ) → Set
    deficitGaugeInvariant : ∀ p → gaugeInvariant (deficit p)

data _∈List_ {A : Set} : A → List A → Set where
  here∈List : ∀ {x xs} → x ∈List (x ∷ xs)
  there∈List : ∀ {x y xs} → x ∈List xs → x ∈List (y ∷ xs)

absurdListMembership : ∀ {A : Set} {x : A} → x ∈List [] → Set
absurdListMembership ()

mapMembership :
  ∀ {A B : Set} (f : A → B) {x : B} {values : List A} →
  x ∈List map f values → Σ A (λ value → f value ≡ x × value ∈List values)
mapMembership f {x} {[]} ()
mapMembership f {x} {value ∷ values} (here∈List) =
  value , refl , here∈List
mapMembership f {x} {value ∷ values} (there∈List membership) =
  let previous = mapMembership f {x} {values} membership
  in proj₁ previous , proj₁ (proj₂ previous) ,
     there∈List (proj₂ (proj₂ previous))

productℝ : List ℝ → ℝ
productℝ [] = 1ℝ
productℝ (x ∷ xs) = x *ℝ productℝ xs

sumℝ : List ℝ → ℝ
sumℝ [] = 0ℝ
sumℝ (x ∷ xs) = x +ℝ sumℝ xs


-- Geometry-first multiplicative naturality on a finite original contour.
-- The proof uses no stochastic independence of SU(N) plaquettes.
productMapPointwiseCongruent :
  ∀ {A : Set} (f g : A → ℝ) (xs : List A) →
    (∀ x → f x ≡ g x) →
    productℝ (map f xs) ≡ productℝ (map g xs)
productMapPointwiseCongruent f g [] same = refl
productMapPointwiseCongruent f g (x ∷ xs) same =
  cong₂ _*ℝ_
    (same x)
    (productMapPointwiseCongruent f g xs same)


Range01 : ℝ → Set
Range01 value = (0ℝ ≤ℝ value) × (value ≤ℝ 1ℝ)


------------------------------------------------------------------------
-- Concrete soft curvature cut: divide the TRUE raw Wilson deficit by
-- two. This does not assume an arbitrary clamp, and the unit range is
-- a theorem from the physical [0,2] deficit bound.  It is a legitimate
-- continuous polynomial source observation once genuine matrix trace,
-- scalar division and compact Haar semantics are supplied; it is NOT
-- an indicator of a high-curvature event or a CMP116 source match.
------------------------------------------------------------------------

halfNormalizedDeficit :
  ∀ {Converges : (Nat → ℝ) → ℝ → Set}
    (quotient : Quotient.RealQuotientConvergenceAuthority Converges)
    (source : ContinuousWilsonSourceContract) →
    ContinuousWilsonSourceContract.PlaquetteIndex source →
    ContinuousWilsonSourceContract.Configuration source → ℝ
halfNormalizedDeficit quotient source p links =
  Quotient.divide quotient
    (ContinuousWilsonSourceContract.deficit source p links)
    (1ℝ +ℝ 1ℝ)

halfNormalizedDeficitRange :
  ∀ {Converges : (Nat → ℝ) → ℝ → Set}
    (quotient : Quotient.RealQuotientConvergenceAuthority Converges)
    (arithmetic : ContinuousWilsonArithmetic quotient)
    (source : ContinuousWilsonSourceContract)
    (p : ContinuousWilsonSourceContract.PlaquetteIndex source)
    (links : ContinuousWilsonSourceContract.Configuration source) →
    Range01 (halfNormalizedDeficit quotient source p links)
halfNormalizedDeficitRange quotient arithmetic source p links =
  ContinuousWilsonArithmetic.halfNonnegative arithmetic
    (ContinuousWilsonSourceContract.deficit source p links)
    (ContinuousWilsonSourceContract.deficitNonnegative source p links) ,
  ContinuousWilsonArithmetic.halfLeOneOfUnit arithmetic
    (ContinuousWilsonSourceContract.deficit source p links)
    (ContinuousWilsonSourceContract.deficitNonnegative source p links)
    (ContinuousWilsonSourceContract.deficitLeTwo source p links)



module _
    {Converges : (Nat → ℝ) → ℝ → Set}
    (quotient : Quotient.RealQuotientConvergenceAuthority Converges)
    (arithmetic : ContinuousWilsonArithmetic quotient)
    (clampSource : ContinuousClampSource)
    (source : ContinuousWilsonSourceContract)
  where

  Configuration : Set
  Configuration = ContinuousWilsonSourceContract.Configuration source

  PlaquetteIndex : Set
  PlaquetteIndex = ContinuousWilsonSourceContract.PlaquetteIndex source

  expectationAlgebra : ContinuousExpectationAlgebra Configuration
  expectationAlgebra = ContinuousWilsonSourceContract.expectation source

  μ : (Configuration → ℝ) → ℝ
  μ = ContinuousExpectationAlgebra.E expectationAlgebra

  covarianceμ : (Configuration → ℝ) → (Configuration → ℝ) → ℝ
  covarianceμ left right =
    μ (λ links → left links *ℝ right links) -ℝ μ right *ℝ μ left

  -- Apply the physically selected threshold on the normalized
  -- curvature in [0,1], NOT on the raw Wilson [0,2] deficit.
  curvatureCutoff : PlaquetteIndex → Configuration → ℝ
  curvatureCutoff p links =
    ContinuousClampSource.clamp clampSource
      (halfNormalizedDeficit quotient source p links)

  curvatureCutoffRange : ∀ p links → Range01 (curvatureCutoff p links)
  curvatureCutoffRange p links =
    let half = halfNormalizedDeficit quotient source p links
    in ContinuousClampSource.clampNonnegative clampSource half ,
       ContinuousClampSource.clampLeOne clampSource half

  productRangeNonnegative : ∀ values →
    (∀ value → value ∈List values → Range01 value) →
    0ℝ ≤ℝ productℝ values
  productRangeNonnegative [] memberships = oneNonnegative
  productRangeNonnegative (value ∷ values) memberships =
    ContinuousWilsonArithmetic.productNonnegative arithmetic
      (proj₁ (memberships value here∈List))
      (productRangeNonnegative values
        (λ tail tailIn → memberships tail (there∈List tailIn)))

  productRangeLeOne : ∀ values →
    (∀ value → value ∈List values → Range01 value) →
    productℝ values ≤ℝ 1ℝ
  productRangeLeOne [] memberships = ≤ℝ-refl
  productRangeLeOne (value ∷ values) memberships =
    ContinuousWilsonArithmetic.productLeOne arithmetic
      (proj₁ (memberships value here∈List))
      (proj₂ (memberships value here∈List))
      (productRangeNonnegative values
        (λ tail tailIn → memberships tail (there∈List tailIn)))
      (productRangeLeOne values
        (λ tail tailIn → memberships tail (there∈List tailIn)))

  productRange : ∀ values →
    (∀ value → value ∈List values → Range01 value) →
    Range01 (productℝ values)
  productRange values memberships =
    productRangeNonnegative values memberships ,
    productRangeLeOne values memberships

  contourProduct : List PlaquetteIndex → Configuration → ℝ
  contourProduct contour links =
    productℝ (map (λ p → curvatureCutoff p links) contour)

  contourProductRange : ∀ contour links → Range01 (contourProduct contour links)
  contourProductRange contour links =
    productRange
      (map (λ p → curvatureCutoff p links) contour)
      (λ value membership →
        let witness = mapMembership (λ p → curvatureCutoff p links) membership
        in subst Range01 (proj₁ (proj₂ witness))
             (curvatureCutoffRange (proj₁ witness) links))

  badContourCutoff : List (List PlaquetteIndex) → Configuration → ℝ
  badContourCutoff contours links =
    1ℝ -ℝ productℝ
      (map (λ contour → 1ℝ -ℝ contourProduct contour links) contours)


  -- If an original gauge action leaves every source plaquette cutoff
  -- unchanged, then it leaves every finite ordered contour product and
  -- its union cutoff unchanged.  No probabilistic premise occurs here.
  contourProductNaturality :
    (transform : Configuration → Configuration) →
    (cutoffNatural : ∀ p links →
      curvatureCutoff p (transform links) ≡ curvatureCutoff p links) →
    ∀ contour links →
      contourProduct contour (transform links) ≡
        contourProduct contour links
  contourProductNaturality transform cutoffNatural contour links =
    productMapPointwiseCongruent
      (λ p → curvatureCutoff p (transform links))
      (λ p → curvatureCutoff p links)
      contour (λ p → cutoffNatural p links)

  badContourCutoffNaturality :
    (transform : Configuration → Configuration) →
    (cutoffNatural : ∀ p links →
      curvatureCutoff p (transform links) ≡ curvatureCutoff p links) →
    ∀ contours links →
      badContourCutoff contours (transform links) ≡
        badContourCutoff contours links
  badContourCutoffNaturality transform cutoffNatural contours links =
    cong (λ value → 1ℝ -ℝ value)
      (productMapPointwiseCongruent
        (λ contour → 1ℝ -ℝ contourProduct contour (transform links))
        (λ contour → 1ℝ -ℝ contourProduct contour links)
        contours
        (λ contour → cong (λ value → 1ℝ -ℝ value)
          (contourProductNaturality
            transform cutoffNatural contour links)))


  contourFactorRange : ∀ contours links →
    Range01
      (productℝ
        (map (λ contour → 1ℝ -ℝ contourProduct contour links) contours))
  contourFactorRange [] links = oneNonnegative , ≤ℝ-refl
  contourFactorRange (contour ∷ contours) links =
    let previous = contourFactorRange contours links
        current = contourProductRange contour links
        oneMinusNN = ContinuousWilsonArithmetic.subNonnegative arithmetic (proj₂ current)
        oneMinus≤1 = ContinuousWilsonArithmetic.oneMinusLeOne arithmetic (proj₁ current)
    in
    ContinuousWilsonArithmetic.productNonnegative arithmetic oneMinusNN (proj₁ previous) ,
    ContinuousWilsonArithmetic.productLeOne arithmetic
      oneMinusNN oneMinus≤1 (proj₁ previous) (proj₂ previous)

  badContourCutoffRange : ∀ contours links → Range01 (badContourCutoff contours links)
  badContourCutoffRange contours links =
    let factors = contourFactorRange contours links
    in ContinuousWilsonArithmetic.subNonnegative arithmetic (proj₂ factors) ,
       ContinuousWilsonArithmetic.oneMinusLeOne arithmetic (proj₁ factors)

  oneMinusProductRange : ∀ values →
    (∀ value → value ∈List values → Range01 value) →
    Range01 (productℝ (map (λ value → 1ℝ -ℝ value) values))
  oneMinusProductRange values memberships =
    productRange
      (map (λ value → 1ℝ -ℝ value) values)
      (λ value membership →
        let witness = mapMembership (λ value → 1ℝ -ℝ value) membership
            original = proj₁ witness
            originalRange = memberships original (proj₂ (proj₂ witness))
            transformedRange =
              ContinuousWilsonArithmetic.subNonnegative arithmetic
                (proj₂ originalRange) ,
              ContinuousWilsonArithmetic.oneMinusLeOne arithmetic
                (proj₁ originalRange)
        in subst Range01 (proj₁ (proj₂ witness)) transformedRange)

  unionBoundProduct : ∀ values →
    (∀ value → value ∈List values → Range01 value) →
    1ℝ -ℝ productℝ (map (λ value → 1ℝ -ℝ value) values) ≤ℝ sumℝ values
  unionBoundProduct [] memberships =
    subst (λ value → value ≤ℝ 0ℝ) (sym (subSelf 1ℝ)) ≤ℝ-refl
  unionBoundProduct (value ∷ values) memberships =
    let tailMembership = λ tail tailIn → memberships tail (there∈List tailIn)
        tailProduct = oneMinusProductRange values tailMembership
        tailGap = unionBoundProduct values tailMembership
    in
    ContinuousWilsonArithmetic.oneMinusMulLeSum arithmetic
      (proj₁ (memberships value here∈List))
      (proj₂ (memberships value here∈List))
      (proj₁ tailProduct) (proj₂ tailProduct) tailGap

  mapOneMinusMap : ∀ {A : Set} (f : A → ℝ) xs →
    map (λ value → 1ℝ -ℝ value) (map f xs)
    ≡ map (λ x → 1ℝ -ℝ f x) xs
  mapOneMinusMap f [] = refl
  mapOneMinusMap f (x ∷ xs) =
    cong (λ rest → (1ℝ -ℝ f x) ∷ rest) (mapOneMinusMap f xs)

  mapContourProductApply : ∀ contours links →
    map (λ f → f links) (map (λ contour → contourProduct contour) contours)
    ≡ map (λ contour → contourProduct contour links) contours
  mapContourProductApply [] links = refl
  mapContourProductApply (contour ∷ contours) links =
    cong (λ rest → contourProduct contour links ∷ rest)
      (mapContourProductApply contours links)

  mapMuMapContour : ∀ contours →
    map μ (map (λ contour → contourProduct contour) contours)
    ≡ map (λ contour → μ (contourProduct contour)) contours
  mapMuMapContour [] = refl
  mapMuMapContour (contour ∷ contours) =
    cong (λ rest → μ (contourProduct contour) ∷ rest)
      (mapMuMapContour contours)

  badContourCutoffBelowContourSum :
    ∀ contours links →
    badContourCutoff contours links
    ≤ℝ sumℝ (map (λ contour → contourProduct contour links) contours)
  badContourCutoffBelowContourSum contours links =
    subst
      (λ values → 1ℝ -ℝ productℝ values
        ≤ℝ sumℝ (map (λ contour → contourProduct contour links) contours))
      (mapOneMinusMap (λ contour → contourProduct contour links) contours)
      (unionBoundProduct
        (map (λ contour → contourProduct contour links) contours)
        (λ value membership →
          let witness = mapMembership
                (λ contour → contourProduct contour links) membership
          in subst Range01 (proj₁ (proj₂ witness))
               (contourProductRange (proj₁ witness) links)))

  expectationMono : ∀ f g → (∀ links → f links ≤ℝ g links) → μ f ≤ℝ μ g
  expectationMono f g pointwise =
    let differenceNonnegative =
          ContinuousExpectationAlgebra.EPositive expectationAlgebra
            (λ links → g links -ℝ f links)
            (λ links → ContinuousWilsonArithmetic.subNonnegative arithmetic (pointwise links))
        sumBound = ContinuousWilsonArithmetic.leAddNonnegative arithmetic differenceNonnegative
        sumEqualsG =
          ContinuousExpectationAlgebra.EExt expectationAlgebra
            (λ links → f links +ℝ (g links -ℝ f links)) g
            (λ links → ContinuousWilsonArithmetic.addSubCancel arithmetic (f links) (g links))
        sumValue =
          trans
            (ContinuousExpectationAlgebra.EAdd expectationAlgebra f
              (λ links → g links -ℝ f links))
            (cong (λ tail → μ f +ℝ tail) refl)
        sumUpper =
          subst (λ value → μ f +ℝ
            ContinuousExpectationAlgebra.E expectationAlgebra
              (λ links → g links -ℝ f links) ≤ℝ value)
            (trans (sym sumValue) sumEqualsG) ≤ℝ-refl
    in
    ≤ℝ-trans sumBound sumUpper

  expectationUnitBounds : ∀ h → (∀ links → 0ℝ ≤ℝ h links) →
    (∀ links → h links ≤ℝ 1ℝ) →
    (0ℝ ≤ℝ μ h) × (μ h ≤ℝ 1ℝ)
  expectationUnitBounds h lower upper =
    ContinuousExpectationAlgebra.EPositive expectationAlgebra h lower ,
    ≤ℝ-trans
      (expectationMono h (λ _ → 1ℝ) upper)
      (subst (λ value → μ (λ _ → 1ℝ) ≤ℝ value)
        (ContinuousExpectationAlgebra.EOne expectationAlgebra) ≤ℝ-refl)

  χ : List (List PlaquetteIndex) → Configuration → ℝ
  χ = badContourCutoff

  q : List (List PlaquetteIndex) → ℝ
  q contours = μ (χ contours)

  qRange : ∀ contours → Range01 (q contours)
  qRange contours =
    expectationUnitBounds (χ contours)
      (λ links → proj₁ (badContourCutoffRange contours links))
      (λ links → proj₂ (badContourCutoffRange contours links))

  signedCovarianceConstant : ℝ
  signedCovarianceConstant = fourℝ -ℝ (0ℝ -ℝ fourℝ)

  sharpSignedCovarianceConstant : ℝ
  sharpSignedCovarianceConstant = fourℝ

  expectationMonoFor :
    (Ealg : ContinuousExpectationAlgebra Configuration) →
    ∀ f g → (∀ links → f links ≤ℝ g links) →
    ContinuousExpectationAlgebra.E Ealg f ≤ℝ
      ContinuousExpectationAlgebra.E Ealg g
  expectationMonoFor Ealg f g pointwise =
    let differenceNonnegative =
          ContinuousExpectationAlgebra.EPositive Ealg
            (λ links → g links -ℝ f links)
            (λ links → ContinuousWilsonArithmetic.subNonnegative arithmetic
              (pointwise links))
        sumBound = ContinuousWilsonArithmetic.leAddNonnegative arithmetic
          differenceNonnegative
        sumEqualsG =
          ContinuousExpectationAlgebra.EExt Ealg
            (λ links → f links +ℝ (g links -ℝ f links)) g
            (λ links → ContinuousWilsonArithmetic.addSubCancel arithmetic
              (f links) (g links))
        sumValue =
          trans
            (ContinuousExpectationAlgebra.EAdd Ealg f
              (λ links → g links -ℝ f links))
            refl
        sumUpper =
          subst
            (λ value → ContinuousExpectationAlgebra.E Ealg f +ℝ
              ContinuousExpectationAlgebra.E Ealg
                (λ links → g links -ℝ f links) ≤ℝ value)
            (trans (sym sumValue) sumEqualsG) ≤ℝ-refl
    in ≤ℝ-trans sumBound sumUpper

  expectationMinusOneFor :
    (Ealg : ContinuousExpectationAlgebra Configuration) →
    ContinuousExpectationAlgebra.E Ealg (λ _ → 0ℝ -ℝ 1ℝ) ≡ (0ℝ -ℝ 1ℝ)
  expectationMinusOneFor Ealg =
    let minusOne = 0ℝ -ℝ 1ℝ
        scaled =
          trans
            (ContinuousExpectationAlgebra.EScale Ealg minusOne (λ _ → 1ℝ))
            (trans
              (cong (λ value → minusOne *ℝ value)
                (ContinuousExpectationAlgebra.EOne Ealg))
              (mulOneʳ minusOne))
        sameFunction =
          ContinuousExpectationAlgebra.EExt Ealg
            (λ _ → minusOne *ℝ 1ℝ) (λ _ → minusOne)
            (λ _ → mulOneʳ minusOne)
    in trans (sym sameFunction) scaled

  expectationSignedBoundsFor :
    (Ealg : ContinuousExpectationAlgebra Configuration) →
    ∀ f → (∀ links → RangeNegOneOne (f links)) →
    RangeNegOneOne (ContinuousExpectationAlgebra.E Ealg f)
  expectationSignedBoundsFor Ealg f fRange =
    let lowerBase =
          expectationMonoFor Ealg (λ _ → 0ℝ -ℝ 1ℝ) f
            (λ links → proj₁ (fRange links))
        lower =
          subst
            (λ value → value ≤ℝ ContinuousExpectationAlgebra.E Ealg f)
            (expectationMinusOneFor Ealg) lowerBase
        upperBase =
          expectationMonoFor Ealg f (λ _ → 1ℝ)
            (λ links → proj₂ (fRange links))
        upper =
          subst
            (λ value → ContinuousExpectationAlgebra.E Ealg f ≤ℝ value)
            (ContinuousExpectationAlgebra.EOne Ealg) upperBase
    in lower , upper

  goodMass : List (List PlaquetteIndex) → ℝ
  goodMass contours = μ (λ links → 1ℝ -ℝ χ contours links)

  qPlusGoodMass : ∀ contours → q contours +ℝ goodMass contours ≡ 1ℝ
  qPlusGoodMass contours =
    trans
      (sym (ContinuousExpectationAlgebra.EAdd expectationAlgebra
        (χ contours) (λ links → 1ℝ -ℝ χ contours links)))
      (trans
        (ContinuousExpectationAlgebra.EExt expectationAlgebra
          (λ links → χ contours links +ℝ (1ℝ -ℝ χ contours links))
          (λ _ → 1ℝ)
          (λ links → ContinuousWilsonArithmetic.addSubCancel arithmetic (χ contours links) 1ℝ))
        (ContinuousExpectationAlgebra.EOne expectationAlgebra))

  qLessOne : ∀ contours → 0ℝ <ℝ goodMass contours → q contours <ℝ 1ℝ
  qLessOne contours strictGood =
    subst (λ value → q contours <ℝ value)
      (qPlusGoodMass contours)
      (ContinuousWilsonArithmetic.positiveAddRight arithmetic strictGood)

  ν : List (List PlaquetteIndex) → (Configuration → ℝ) → ℝ
  ν contours h =
    Quotient.divide quotient
      (μ (λ links → (1ℝ -ℝ χ contours links) *ℝ h links))
      (1ℝ -ℝ q contours)

  denominatorNonzero : ∀ contours → 0ℝ <ℝ goodMass contours →
    Quotient.Nonzero quotient (1ℝ -ℝ q contours)
  denominatorNonzero contours strictGood =
    ContinuousWilsonArithmetic.strictToNonzero arithmetic
      (ContinuousWilsonArithmetic.subPositiveOfLess arithmetic
        (qLessOne contours strictGood))

  νZero : ∀ (contours : List (List PlaquetteIndex))
    (strictGood : 0ℝ <ℝ goodMass contours) →
    ν contours (λ _ → 0ℝ) ≡ 0ℝ
  νZero contours strictGood =
    let nonzero = denominatorNonzero contours strictGood
        numeratorZero =
          trans
            (ContinuousExpectationAlgebra.EExt expectationAlgebra
              (λ links → (1ℝ -ℝ χ contours links) *ℝ 0ℝ)
              (λ _ → 0ℝ)
              (λ links → mulZeroʳ (1ℝ -ℝ χ contours links)))
            (ContinuousExpectationAlgebra.EZero expectationAlgebra)
    in trans (cong (λ numerator →
         Quotient.divide quotient numerator (1ℝ -ℝ q contours))
         numeratorZero)
       (ContinuousWilsonArithmetic.divideZero arithmetic (1ℝ -ℝ q contours) nonzero)

  νOne : ∀ (contours : List (List PlaquetteIndex))
    (strictGood : 0ℝ <ℝ goodMass contours) →
    ν contours (λ _ → 1ℝ) ≡ 1ℝ
  νOne contours strictGood =
    let nonzero = denominatorNonzero contours strictGood
        numeratorGood =
          trans
            (ContinuousExpectationAlgebra.EExt expectationAlgebra
              (λ links → (1ℝ -ℝ χ contours links) *ℝ 1ℝ)
              (λ links → 1ℝ -ℝ χ contours links)
              (λ links → mulOneʳ (1ℝ -ℝ χ contours links)))
            refl
        numeratorEqualsDenominator =
          trans numeratorGood
            (ContinuousWilsonArithmetic.goodMassEqOneMinus arithmetic
              (qPlusGoodMass contours))
    in trans (cong (λ numerator →
         Quotient.divide quotient numerator (1ℝ -ℝ q contours))
         numeratorEqualsDenominator)
       (ContinuousWilsonArithmetic.divideSelf arithmetic (1ℝ -ℝ q contours) nonzero)

  νAdd : ∀ (contours : List (List PlaquetteIndex))
    (strictGood : 0ℝ <ℝ goodMass contours) (f g : Configuration → ℝ) →
    ν contours (λ links → f links +ℝ g links) ≡ ν contours f +ℝ ν contours g
  νAdd contours strictGood f g =
    let nonzero = denominatorNonzero contours strictGood
        numeratorAdd =
          trans
            (cong (λ numerator →
              Quotient.divide quotient numerator (1ℝ -ℝ q contours))
              (ContinuousExpectationAlgebra.EExt expectationAlgebra
                (λ links → (1ℝ -ℝ χ contours links) *ℝ (f links +ℝ g links))
                (λ links → (1ℝ -ℝ χ contours links) *ℝ f links
                  +ℝ (1ℝ -ℝ χ contours links) *ℝ g links)
                (ContinuousWilsonArithmetic.restrictedAddPointwise arithmetic (χ contours) f g)))
            (trans
              (cong (λ numerator →
                Quotient.divide quotient numerator (1ℝ -ℝ q contours))
                (ContinuousExpectationAlgebra.EAdd expectationAlgebra
                  (λ links → (1ℝ -ℝ χ contours links) *ℝ f links)
                  (λ links → (1ℝ -ℝ χ contours links) *ℝ g links)))
              (ContinuousWilsonArithmetic.divideAdd arithmetic
                (μ (λ links → (1ℝ -ℝ χ contours links) *ℝ f links))
                (μ (λ links → (1ℝ -ℝ χ contours links) *ℝ g links))
                (1ℝ -ℝ q contours) nonzero))
    in numeratorAdd

  νScale : ∀ (contours : List (List PlaquetteIndex))
    (strictGood : 0ℝ <ℝ goodMass contours) (scalar : ℝ)
    (f : Configuration → ℝ) →
    ν contours (λ links → scalar *ℝ f links)
    ≡ scalar *ℝ ν contours f
  νScale contours strictGood scalar f =
    let nonzero = denominatorNonzero contours strictGood
    in trans
      (cong (λ numerator →
        Quotient.divide quotient numerator (1ℝ -ℝ q contours))
        (ContinuousExpectationAlgebra.EExt expectationAlgebra
          (λ links → (1ℝ -ℝ χ contours links) *ℝ (scalar *ℝ f links))
          (λ links → scalar *ℝ ((1ℝ -ℝ χ contours links) *ℝ f links))
          (ContinuousWilsonArithmetic.restrictedScalePointwise arithmetic (χ contours) scalar f)))
      (trans
        (cong (λ numerator →
          Quotient.divide quotient numerator (1ℝ -ℝ q contours))
          (ContinuousExpectationAlgebra.EScale expectationAlgebra scalar
            (λ links → (1ℝ -ℝ χ contours links) *ℝ f links)))
        (ContinuousWilsonArithmetic.divideScale arithmetic scalar
          (μ (λ links → (1ℝ -ℝ χ contours links) *ℝ f links))
          (1ℝ -ℝ q contours) nonzero))

  νPositive : ∀ (contours : List (List PlaquetteIndex))
    (strictGood : 0ℝ <ℝ goodMass contours) (f : Configuration → ℝ) →
    (∀ links → 0ℝ ≤ℝ f links) →
    0ℝ ≤ℝ ν contours f
  νPositive contours strictGood f lower =
    ContinuousWilsonArithmetic.divideNonnegative arithmetic
      (μ (λ links → (1ℝ -ℝ χ contours links) *ℝ f links))
      (1ℝ -ℝ q contours)
      (ContinuousExpectationAlgebra.EPositive expectationAlgebra
        (λ links → (1ℝ -ℝ χ contours links) *ℝ f links)
        (λ links → ContinuousWilsonArithmetic.productNonnegative arithmetic
          (ContinuousWilsonArithmetic.subNonnegative arithmetic
            (proj₂ (badContourCutoffRange contours links))) (lower links)))
      (denominatorNonzero contours strictGood)

  νExt : ∀ (contours : List (List PlaquetteIndex))
    (strictGood : 0ℝ <ℝ goodMass contours) (f g : Configuration → ℝ) →
    (∀ links → f links ≡ g links) →
    ν contours f ≡ ν contours g
  νExt contours strictGood f g equal =
    cong (λ numerator →
      Quotient.divide quotient numerator (1ℝ -ℝ q contours))
      (ContinuousExpectationAlgebra.EExt expectationAlgebra
        (λ links → (1ℝ -ℝ χ contours links) *ℝ f links)
        (λ links → (1ℝ -ℝ χ contours links) *ℝ g links)
        (λ links → cong (λ value →
          (1ℝ -ℝ χ contours links) *ℝ value) (equal links)))

  νAlgebra : ∀ (contours : List (List PlaquetteIndex))
    (strictGood : 0ℝ <ℝ goodMass contours) →
    ContinuousExpectationAlgebra Configuration
  νAlgebra contours strictGood = record
    { E = ν contours
    ; EZero = νZero contours strictGood
    ; EOne = νOne contours strictGood
    ; EAdd = νAdd contours strictGood
    ; EScale = νScale contours strictGood
    ; EPositive = νPositive contours strictGood
    ; EExt = νExt contours strictGood
    ; ECenteredProduct = λ f g a b →
        ContinuousWilsonArithmetic.centeredProductExpectation arithmetic
          (ν contours)
          (νAdd contours strictGood)
          (νScale contours strictGood)
          (νExt contours strictGood)
          f g a b
    }

  restrictedBounds :
    ∀ contours h m M →
    (∀ links → m ≤ℝ h links) →
    (∀ links → h links ≤ℝ M) →
    (m *ℝ q contours ≤ℝ μ (λ links → χ contours links *ℝ h links)) ×
    (μ (λ links → χ contours links *ℝ h links) ≤ℝ M *ℝ q contours) ×
    (m ≤ℝ ν contours h) × (ν contours h ≤ℝ M)
  restrictedBounds contours h m M lower upper =
    ContinuousWilsonArithmetic.meanRestrictionBounds arithmetic
      μ
      (ContinuousExpectationAlgebra.EAdd expectationAlgebra)
      (ContinuousExpectationAlgebra.EScale expectationAlgebra)
      (ContinuousExpectationAlgebra.EPositive expectationAlgebra)
      (ContinuousExpectationAlgebra.EExt expectationAlgebra)
      (χ contours) h (q contours)
      (μ (λ links → (1ℝ -ℝ χ contours links) *ℝ h links)) m M
      (λ links → proj₁ (badContourCutoffRange contours links))
      (λ links → proj₂ (badContourCutoffRange contours links))
      lower upper refl refl

  νUnitBounds : ∀ contours h → (∀ links → 0ℝ ≤ℝ h links) →
    (∀ links → h links ≤ℝ 1ℝ) →
    (0ℝ ≤ℝ ν contours h) × (ν contours h ≤ℝ 1ℝ)
  νUnitBounds contours h lower upper =
    let bounds = restrictedBounds contours h 0ℝ 1ℝ lower upper
    in proj₁ (proj₂ (proj₂ bounds)) , proj₂ (proj₂ (proj₂ bounds))

  μMinusν : ∀ contours h →
    μ h -ℝ ν contours h
    ≡ μ (λ links → χ contours links *ℝ h links)
      -ℝ q contours *ℝ ν contours h
  μMinusν contours h =
    let
      chiLink = λ links → χ contours links *ℝ h links
      goodLink = λ links → (1ℝ -ℝ χ contours links) *ℝ h links
      μDecomposition =
        trans
          (sym (ContinuousExpectationAlgebra.EExt expectationAlgebra
            (λ links → chiLink links +ℝ goodLink links) h
            (λ links → ContinuousWilsonArithmetic.partitionUnityExpand arithmetic
              (χ contours links) (h links))))
          (ContinuousExpectationAlgebra.EAdd expectationAlgebra chiLink goodLink)
      shiftEquality =
        subst
          (λ value → μ h -ℝ ν contours h
            ≡ value -ℝ ν contours h)
          μDecomposition refl
    in
    ContinuousWilsonArithmetic.shiftIdentityAlgebra arithmetic
      (μ h -ℝ ν contours h)
      (μ chiLink)
      (μ goodLink)
      (goodMass contours)
      (q contours)
      shiftEquality
      (qPlusGoodMass contours)

  covarianceν : List (List PlaquetteIndex) →
    (Configuration → ℝ) → (Configuration → ℝ) → ℝ
  covarianceν contours left right =
    ν contours (λ links → left links *ℝ right links)
    -ℝ ν contours right *ℝ ν contours left

  covarianceMidpointGap : ∀ contours strictGood f g →
    covarianceμ f g -ℝ covarianceν contours f g
    ≡
    let a = Quotient.divide quotient (μ f +ℝ ν contours f) (1ℝ +ℝ 1ℝ)
        b = Quotient.divide quotient (μ g +ℝ ν contours g) (1ℝ +ℝ 1ℝ)
    in
    μ (λ links → (f links -ℝ a) *ℝ (g links -ℝ b))
      -ℝ ν contours (λ links → (f links -ℝ a) *ℝ (g links -ℝ b))
  covarianceMidpointGap contours strictGood f g =
    let a = Quotient.divide quotient (μ f +ℝ ν contours f) (1ℝ +ℝ 1ℝ)
        b = Quotient.divide quotient (μ g +ℝ ν contours g) (1ℝ +ℝ 1ℝ)
        algebraic = ContinuousWilsonArithmetic.covarianceMidpointIdentity arithmetic
          (μ f) (ν contours f) (μ g) (ν contours g)
          (μ (λ links → f links *ℝ g links))
          (ν contours (λ links → f links *ℝ g links))
        μCentered =
          ContinuousExpectationAlgebra.ECenteredProduct expectationAlgebra
            f g a b
        νCentered =
          ContinuousExpectationAlgebra.ECenteredProduct
            (νAlgebra contours strictGood) f g a b
    in trans algebraic
      (cong₂ _-ℝ_ (sym μCentered) (sym νCentered))

  covarianceGapBound :
    ∀ contours f g →
    (∀ links → 0ℝ ≤ℝ f links) →
    (∀ links → f links ≤ℝ 1ℝ) →
    (∀ links → 0ℝ ≤ℝ g links) →
    (∀ links → g links ≤ℝ 1ℝ) →
    0ℝ <ℝ goodMass contours →
    absℝ (covarianceμ f g -ℝ covarianceν contours f g)
      ≤ℝ (1ℝ +ℝ 1ℝ +ℝ (1ℝ +ℝ 1ℝ)) *ℝ q contours
  covarianceGapBound contours f g fLower fUpper gLower gUpper strictGood =
    let μfBounds = expectationUnitBounds f fLower fUpper
        μgBounds = expectationUnitBounds g gLower gUpper
        νfBounds = νUnitBounds contours f fLower fUpper
        νgBounds = νUnitBounds contours g gLower gUpper
        a = Quotient.divide quotient (μ f +ℝ ν contours f) (1ℝ +ℝ 1ℝ)
        b = Quotient.divide quotient (μ g +ℝ ν contours g) (1ℝ +ℝ 1ℝ)
        aNN = ContinuousWilsonArithmetic.halfNonnegative arithmetic
          (μ f +ℝ ν contours f)
          (ContinuousWilsonArithmetic.addNonnegative arithmetic
            (proj₁ μfBounds) (proj₁ νfBounds))
        bNN = ContinuousWilsonArithmetic.halfNonnegative arithmetic
          (μ g +ℝ ν contours g)
          (ContinuousWilsonArithmetic.addNonnegative arithmetic
            (proj₁ μgBounds) (proj₁ νgBounds))
        a≤1 = ContinuousWilsonArithmetic.halfLeOneOfUnit arithmetic
          (μ f +ℝ ν contours f)
          (ContinuousWilsonArithmetic.addNonnegative arithmetic
            (proj₁ μfBounds) (proj₁ νfBounds))
          (+-mono-≤ (proj₂ μfBounds) (proj₂ νfBounds))
        b≤1 = ContinuousWilsonArithmetic.halfLeOneOfUnit arithmetic
          (μ g +ℝ ν contours g)
          (ContinuousWilsonArithmetic.addNonnegative arithmetic
            (proj₁ μgBounds) (proj₁ νgBounds))
          (+-mono-≤ (proj₂ μgBounds) (proj₂ νgBounds))
        fDiffBounds = λ links →
          ContinuousWilsonArithmetic.unitIntervalDifferenceBounds arithmetic
            (fLower links) (fUpper links) aNN a≤1
        gDiffBounds = λ links →
          ContinuousWilsonArithmetic.unitIntervalDifferenceBounds arithmetic
            (gLower links) (gUpper links) bNN b≤1
        h = λ links → (f links -ℝ a) *ℝ (g links -ℝ b)
        hBounds = λ links →
          ContinuousWilsonArithmetic.negOneOneProductBounds arithmetic
            (proj₁ (fDiffBounds links)) (proj₂ (fDiffBounds links))
            (proj₁ (gDiffBounds links)) (proj₂ (gDiffBounds links))
        hRestricted = restrictedBounds contours h (0ℝ -ℝ 1ℝ) 1ℝ
          (λ links → proj₁ (hBounds links))
          (λ links → proj₂ (hBounds links))
        shiftEquality = μMinusν contours h
        μCentered =
          ContinuousExpectationAlgebra.ECenteredProduct expectationAlgebra
            f g a b
        νCentered =
          ContinuousExpectationAlgebra.ECenteredProduct
            (νAlgebra contours strictGood) f g a b
        centeredEquality =
          cong₂ _-ℝ_ (sym μCentered) (sym νCentered)
        bounded = ContinuousWilsonArithmetic.unitShiftAbsoluteBound arithmetic
          (μ h -ℝ ν contours h)
          (μ (λ links → χ contours links *ℝ h links))
          (ν contours h)
          (q contours)
          shiftEquality
          (proj₁ hRestricted)
          (proj₁ (proj₂ hRestricted))
          (proj₁ (proj₂ (proj₂ hRestricted)))
          (proj₂ (proj₂ (proj₂ hRestricted)))
          (proj₁ (qRange contours))
        centeredBound = bounded
    in subst (λ value → absℝ value
         ≤ℝ (1ℝ +ℝ 1ℝ +ℝ (1ℝ +ℝ 1ℝ)) *ℝ q contours)
       (sym (covarianceMidpointGap contours strictGood f g)) centeredBound

  covarianceSignedGapBound :
    ∀ contours f g →
    (∀ links → RangeNegOneOne (f links)) →
    (∀ links → RangeNegOneOne (g links)) →
    0ℝ <ℝ goodMass contours →
    absℝ (covarianceμ f g -ℝ covarianceν contours f g)
      ≤ℝ signedCovarianceConstant *ℝ q contours
  covarianceSignedGapBound contours f g fRange gRange strictGood =
    let μfBounds = expectationSignedBoundsFor expectationAlgebra f fRange
        μgBounds = expectationSignedBoundsFor expectationAlgebra g gRange
        νfBounds =
          expectationSignedBoundsFor (νAlgebra contours strictGood) f fRange
        νgBounds =
          expectationSignedBoundsFor (νAlgebra contours strictGood) g gRange
        a = Quotient.divide quotient (μ f +ℝ ν contours f) twoℝ
        b = Quotient.divide quotient (μ g +ℝ ν contours g) twoℝ
        aRange = ContinuousWilsonArithmetic.signedMidpointBounds arithmetic
          (μ f) (ν contours f) μfBounds νfBounds
        bRange = ContinuousWilsonArithmetic.signedMidpointBounds arithmetic
          (μ g) (ν contours g) μgBounds νgBounds
        fDiffBounds = λ links →
          ContinuousWilsonArithmetic.signedDifferenceBounds arithmetic
            (fRange links) aRange
        gDiffBounds = λ links →
          ContinuousWilsonArithmetic.signedDifferenceBounds arithmetic
            (gRange links) bRange
        h = λ links → (f links -ℝ a) *ℝ (g links -ℝ b)
        hBounds = λ links →
          ContinuousWilsonArithmetic.signedProductBounds arithmetic
            (proj₁ (fDiffBounds links)) (proj₂ (fDiffBounds links))
            (proj₁ (gDiffBounds links)) (proj₂ (gDiffBounds links))
        hRestricted = restrictedBounds contours h (0ℝ -ℝ fourℝ) fourℝ
          (λ links → proj₁ (hBounds links))
          (λ links → proj₂ (hBounds links))
        shiftEquality = μMinusν contours h
        bounded = ContinuousWilsonArithmetic.shiftAbsoluteBoundOfInterval
          arithmetic
          (μ h -ℝ ν contours h)
          (μ (λ links → χ contours links *ℝ h links))
          (ν contours h)
          (q contours)
          (0ℝ -ℝ fourℝ)
          fourℝ
          shiftEquality
          (proj₁ hRestricted)
          (proj₁ (proj₂ hRestricted))
          (proj₁ (proj₂ (proj₂ hRestricted)))
          (proj₂ (proj₂ (proj₂ hRestricted)))
          (proj₁ (qRange contours))
    in subst (λ value → absℝ value
         ≤ℝ signedCovarianceConstant *ℝ q contours)
       (sym (covarianceMidpointGap contours strictGood f g)) bounded

  covarianceSharpSignedGapBound :
    ∀ contours f g →
    (∀ links → RangeNegOneOne (f links)) →
    (∀ links → RangeNegOneOne (g links)) →
    0ℝ <ℝ goodMass contours →
    absℝ (covarianceμ f g -ℝ covarianceν contours f g)
      ≤ℝ sharpSignedCovarianceConstant *ℝ q contours
  covarianceSharpSignedGapBound contours f g fRange gRange strictGood =
    let a = Quotient.divide quotient (μ f +ℝ ν contours f) twoℝ
        b = Quotient.divide quotient (μ g +ℝ ν contours g) twoℝ
        νfBounds =
          expectationSignedBoundsFor (νAlgebra contours strictGood) f fRange
        νgBounds =
          expectationSignedBoundsFor (νAlgebra contours strictGood) g gRange
        aRange = ContinuousWilsonArithmetic.signedMidpointBounds arithmetic
          (μ f) (ν contours f)
          (expectationSignedBoundsFor expectationAlgebra f fRange) νfBounds
        bRange = ContinuousWilsonArithmetic.signedMidpointBounds arithmetic
          (μ g) (ν contours g)
          (expectationSignedBoundsFor expectationAlgebra g gRange) νgBounds
        oscillation =
          ContinuousWilsonArithmetic.centeredProductOscillation arithmetic
            a b aRange bRange
        lower = CenteredProductOscillation.lower oscillation
        upper = CenteredProductOscillation.upper oscillation
        h = λ links → (f links -ℝ a) *ℝ (g links -ℝ b)
        hRestricted = restrictedBounds contours h lower upper
          (λ links → CenteredProductOscillation.lowerBound oscillation
            (f links) (g links) (fRange links) (gRange links))
          (λ links → CenteredProductOscillation.upperBound oscillation
            (f links) (g links) (fRange links) (gRange links))
        shiftEquality = μMinusν contours h
        bounded = ContinuousWilsonArithmetic.shiftAbsoluteBoundOfInterval
          arithmetic
          (μ h -ℝ ν contours h)
          (μ (λ links → χ contours links *ℝ h links))
          (ν contours h)
          (q contours)
          lower
          upper
          shiftEquality
          (proj₁ hRestricted)
          (proj₁ (proj₂ hRestricted))
          (proj₁ (proj₂ (proj₂ hRestricted)))
          (proj₂ (proj₂ (proj₂ hRestricted)))
          (proj₁ (qRange contours))
        boundedSharp =
          subst
            (λ width → absℝ (μ h -ℝ ν contours h) ≤ℝ width *ℝ q contours)
            (CenteredProductOscillation.width oscillation) bounded
    in subst (λ value → absℝ value
         ≤ℝ sharpSignedCovarianceConstant *ℝ q contours)
       (sym (covarianceMidpointGap contours strictGood f g)) boundedSharp

  sumExpectation : ∀ functions →
    μ (λ links → sumℝ (map (λ f → f links) functions))
    ≡ sumℝ (map (λ f → μ f) functions)
  sumExpectation [] =
    trans
      (ContinuousExpectationAlgebra.EExt expectationAlgebra
        (λ _ → 0ℝ) (λ _ → sumℝ [])
        (λ _ → refl))
      (ContinuousExpectationAlgebra.EZero expectationAlgebra)
  sumExpectation (f ∷ functions) =
    trans
      (ContinuousExpectationAlgebra.EExt expectationAlgebra
        (λ links → f links +ℝ sumℝ (map (λ g → g links) functions))
        (λ links → sumℝ (map (λ g → g links) (f ∷ functions)))
        (λ links → refl))
      (trans
        (ContinuousExpectationAlgebra.EAdd expectationAlgebra f
          (λ links → sumℝ (map (λ g → g links) functions)))
        (cong (λ tail → μ f +ℝ tail) (sumExpectation functions)))

  contourMassBound : ∀ contours →
    μ (χ contours)
    ≤ℝ sumℝ (map (λ contour → μ (contourProduct contour)) contours)
  contourMassBound contours =
    let
      targetSum = λ links → sumℝ
        (map (λ contour → contourProduct contour links) contours)
      sourceSum = λ links → sumℝ
        (map (λ f → f links) (map (λ contour → contourProduct contour) contours))
      sumBridge =
        trans
          (trans
            (ContinuousExpectationAlgebra.EExt expectationAlgebra
              targetSum sourceSum
              (λ links → cong sumℝ
                (sym (mapContourProductApply contours links))))
            (sumExpectation (map (λ contour → contourProduct contour) contours)))
          (cong sumℝ
            (mapMuMapContour contours))
    in
    ≤ℝ-trans
      (expectationMono (χ contours) targetSum
        (badContourCutoffBelowContourSum contours))
      (subst
        (λ value → μ targetSum ≤ℝ value) sumBridge ≤ℝ-refl)
