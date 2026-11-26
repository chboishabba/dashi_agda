module DASHI.Physics.YangMills.YMClayContinuousWilsonArithmeticScalarLemmasExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _-ℝ_; _*ℝ_; -ℝ_; absℝ; _≤ℝ_; _<ℝ_;
   ≤ℝ-refl; ≤ℝ-trans; ≤ℝ-total; +-mono-≤; zeroLtOne; strictToNonnegative;
   negEqSubZero; negℝ-involutive; negℝ-order; subEqAddNeg; negℝ-sub;
   subRightMono; subLeftMono; subNonnegative; mulNonnegative;
   mulMonotoneNonnegative; mulOneʳ; oneNonnegative; +-identityˡ;
   +-identityʳ; +-assoc; +-comm; subAddCancel; addSubCancel; addSubAssoc;
   subMulDistributes; *-comm; onePlusMulOnePlus;
    absOfNonnegative; absOfNonpositive; absNonnegative;
    leAbs; negLeAbs; absMul)

import DASHI.Physics.YangMills.YMClayOriginalWilsonContinuousA2BridgeExact as A2

addLeftMono : ∀ {a b : ℝ} (c : ℝ) → a ≤ℝ b → c +ℝ a ≤ℝ c +ℝ b
addLeftMono c h = +-mono-≤ ≤ℝ-refl h

addRightMono : ∀ {a b : ℝ} (c : ℝ) → a ≤ℝ b → a +ℝ c ≤ℝ b +ℝ c
addRightMono c h = +-mono-≤ h ≤ℝ-refl

subZero : ∀ a → a -ℝ 0ℝ ≡ a
subZero a =
  trans
    (sym (cong (λ t → t -ℝ 0ℝ) (+-identityʳ a)))
    (addSubCancel a 0ℝ)

addSubCancelToRight : ∀ a b → a +ℝ (b -ℝ a) ≡ b
addSubCancelToRight a b = trans (+-comm a (b -ℝ a)) (subAddCancel b a)

oneMul : ∀ a → 1ℝ *ℝ a ≡ a
oneMul a = trans (*-comm 1ℝ a) (mulOneʳ a)

subLeSub : ∀ {a b c d : ℝ} → a ≤ℝ b → d ≤ℝ c → a -ℝ c ≤ℝ b -ℝ d
subLeSub {a} {b} {c} {d} hab hdc =
  ≤ℝ-trans (subRightMono c hab) (subLeftMono b hdc)

leOfSubNonnegative : ∀ {a b : ℝ} → 0ℝ ≤ℝ a -ℝ b → b ≤ℝ a
leOfSubNonnegative {a} {b} h =
  let h' = subst (λ t → 0ℝ +ℝ b ≤ℝ t) (subAddCancel a b)
             (addRightMono b h)
  in subst (λ t → t ≤ℝ a) (+-identityˡ b) h'

mulRightMonoNonneg : ∀ {a b c : ℝ} → a ≤ℝ b → 0ℝ ≤ℝ c → a *ℝ c ≤ℝ b *ℝ c
mulRightMonoNonneg {a} {b} {c} hab hc =
  let hdiff = subNonnegative hab
      hprod = mulNonnegative hdiff hc
      hprod' = subst (λ t → 0ℝ ≤ℝ t) (subMulDistributes b a c) hprod
  in leOfSubNonnegative hprod'

subLeFromAddLe : ∀ {a b c : ℝ} → a ≤ℝ b +ℝ c → a -ℝ b ≤ℝ c
subLeFromAddLe {a} {b} {c} h =
  let h' = subRightMono b h
      h'' = trans (cong (λ t → t -ℝ b) (+-comm b c)) (addSubCancel c b)
  in subst (λ t → a -ℝ b ≤ℝ t) h'' h'

leAddNonnegative : ∀ {a b : ℝ} → 0ℝ ≤ℝ b → a ≤ℝ a +ℝ b
leAddNonnegative {a} {b} hb =
  subst (λ t → t ≤ℝ a +ℝ b) (+-identityʳ a) (addLeftMono a hb)

oneMinusLeOne : ∀ {a : ℝ} → 0ℝ ≤ℝ a → 1ℝ -ℝ a ≤ℝ 1ℝ
oneMinusLeOne {a} ha =
  let hneg = A2.subNonpos ha
      h' = addLeftMono 1ℝ hneg
      hleftEq =
        trans (cong (λ t → 1ℝ +ℝ t) (sym (negEqSubZero a)))
          (sym (subEqAddNeg 1ℝ a))
      h'' = subst (λ t → t ≤ℝ 1ℝ +ℝ 0ℝ) hleftEq h'
  in subst (λ t → 1ℝ -ℝ a ≤ℝ t) (+-identityʳ 1ℝ) h''

absBound : ∀ (a r : ℝ) →
  0ℝ ≤ℝ r → (0ℝ -ℝ r) ≤ℝ a → a ≤ℝ r → absℝ a ≤ℝ r
negAbsLeSelf : ∀ a → (-ℝ (absℝ a)) ≤ℝ a
negAbsLeSelf a =
  let h = negℝ-order (negLeAbs a)
  in subst (λ t → (-ℝ (absℝ a)) ≤ℝ t) (negℝ-involutive a) h

absBound a r hr hlower hupper with ≤ℝ-total 0ℝ a
... | inj₁ h0 = subst (λ t → t ≤ℝ r) (sym (absOfNonnegative h0)) hupper
... | inj₂ ha =
  let hneg = negℝ-order hlower
      hrhs = trans (cong (λ t → -ℝ t) (sym (negEqSubZero r))) (negℝ-involutive r)
      hneg' = subst (λ t → -ℝ a ≤ℝ t) hrhs hneg
  in subst (λ t → t ≤ℝ r) (sym (absOfNonpositive ha)) hneg'

negOnePlusLeXMinusOne : ∀ {x : ℝ} → 0ℝ ≤ℝ x → (0ℝ -ℝ 1ℝ) ≤ℝ x -ℝ 1ℝ
negOnePlusLeXMinusOne {x} hx =
  let h0 = addRightMono (-ℝ 1ℝ) hx
      h0' = subst (λ t → t ≤ℝ x +ℝ (-ℝ 1ℝ)) (+-identityˡ (-ℝ 1ℝ)) h0
      h0'' = subst (λ t → (-ℝ 1ℝ) ≤ℝ t) (sym (subEqAddNeg x 1ℝ)) h0'
  in subst (λ t → t ≤ℝ x -ℝ 1ℝ) (negEqSubZero 1ℝ) h0''

oneMinusYLeOne : ∀ {y : ℝ} → 0ℝ ≤ℝ y → 1ℝ -ℝ y ≤ℝ 1ℝ
oneMinusYLeOne {y} hy = oneMinusLeOne hy

unitIntervalDifferenceBounds : ∀ {x y : ℝ} →
  0ℝ ≤ℝ x → x ≤ℝ 1ℝ → 0ℝ ≤ℝ y → y ≤ℝ 1ℝ →
  ((0ℝ -ℝ 1ℝ) ≤ℝ x -ℝ y) × (x -ℝ y ≤ℝ 1ℝ)
unitIntervalDifferenceBounds {x} {y} hx0 hx1 hy0 hy1 =
  let hlow = ≤ℝ-trans (negOnePlusLeXMinusOne hx0) (subLeftMono x hy1)
      hup = ≤ℝ-trans (subRightMono y hx1) (oneMinusYLeOne hy0)
  in hlow , hup

negOneOneProductBounds : ∀ {x y : ℝ} →
  A2.RangeNegOneOne x → A2.RangeNegOneOne y →
  A2.RangeNegOneOne (x *ℝ y)
negOneOneProductBounds {x} {y} hx hy =
  let hlow = A2.negOneLeProduct hx hy
      hlow' = subst (λ t → t ≤ℝ x *ℝ y) (negEqSubZero 1ℝ) hlow
  in hlow' , A2.productLeOneRange hx hy

twoNonnegative : 0ℝ ≤ℝ A2.twoℝ
twoNonnegative = strictToNonnegative A2.twoPositiveℝ

absOfTwo : absℝ A2.twoℝ ≡ A2.twoℝ
absOfTwo = absOfNonnegative twoNonnegative

absLeTwoOfSignedTwoBounds : ∀ {x : ℝ} →
  (0ℝ -ℝ A2.twoℝ) ≤ℝ x → x ≤ℝ A2.twoℝ → absℝ x ≤ℝ A2.twoℝ
absLeTwoOfSignedTwoBounds {x} = absBound x A2.twoℝ twoNonnegative

twoMulTwoEqFour : A2.twoℝ *ℝ A2.twoℝ ≡ A2.fourℝ
twoMulTwoEqFour =
  let h = onePlusMulOnePlus 1ℝ 1ℝ
      h' = trans h (cong (λ t → 1ℝ +ℝ t +ℝ A2.twoℝ) (oneMul 1ℝ))
  in h'

signedDifferenceBounds : ∀ {x y : ℝ} →
  A2.RangeNegOneOne x → A2.RangeNegOneOne y →
  ((0ℝ -ℝ A2.twoℝ) ≤ℝ x -ℝ y) × (x -ℝ y ≤ℝ A2.twoℝ)
signedDifferenceBounds {x} {y} hx hy =
  let habs = A2.absSubLeTwo hx hy
      hlow0 = negℝ-order habs
      hbase = ≤ℝ-trans hlow0 (negAbsLeSelf (x -ℝ y))
      hlow = subst (λ t → t ≤ℝ x -ℝ y) (negEqSubZero A2.twoℝ) hbase
      hup = ≤ℝ-trans (leAbs (x -ℝ y)) habs
  in hlow , hup

signedProductBounds : ∀ {x y : ℝ} →
  (0ℝ -ℝ A2.twoℝ) ≤ℝ x → x ≤ℝ A2.twoℝ →
  (0ℝ -ℝ A2.twoℝ) ≤ℝ y → y ≤ℝ A2.twoℝ →
  ((0ℝ -ℝ A2.fourℝ) ≤ℝ x *ℝ y) × (x *ℝ y ≤ℝ A2.fourℝ)
signedProductBounds {x} {y} hxlow hxup hylow hyup =
  let hxabs = absLeTwoOfSignedTwoBounds hxlow hxup
      hyabs = absLeTwoOfSignedTwoBounds hylow hyup
      hprod0 =
        mulMonotoneNonnegative (absNonnegative x) hxabs
          (absNonnegative y) hyabs
      hprod0' =
        subst (λ t → t ≤ℝ A2.twoℝ *ℝ A2.twoℝ) (sym (absMul x y)) hprod0
      hprod =
        subst (λ t → absℝ (x *ℝ y) ≤ℝ t) twoMulTwoEqFour hprod0'
      hlow0 = negℝ-order hprod
      hbase = ≤ℝ-trans hlow0 (negAbsLeSelf (x *ℝ y))
      hlow = subst (λ t → t ≤ℝ x *ℝ y) (negEqSubZero A2.fourℝ) hbase
      hup = ≤ℝ-trans (leAbs (x *ℝ y)) hprod
  in hlow , hup

oneMinusProductEq : ∀ a q →
  1ℝ -ℝ ((1ℝ -ℝ a) *ℝ q) ≡ (1ℝ -ℝ q) +ℝ a *ℝ q
oneMinusProductEq a q =
  let hmul = subMulDistributes 1ℝ a q
      hmul' = trans hmul (cong (λ t → t -ℝ a *ℝ q) (oneMul q))
      hneg = negℝ-sub q (a *ℝ q)
      hdiffComm =
        trans (subEqAddNeg (a *ℝ q) q)
          (+-comm (a *ℝ q) (-ℝ q))
      hright =
        trans (subEqAddNeg 1ℝ (q -ℝ a *ℝ q))
          (trans (cong (λ t → 1ℝ +ℝ t) hneg)
            (trans (cong (λ t → 1ℝ +ℝ t) hdiffComm)
              (trans (sym (+-assoc 1ℝ (-ℝ q) (a *ℝ q)))
                (cong (λ t → t +ℝ a *ℝ q)
                  (sym (subEqAddNeg 1ℝ q))))))
  in trans (cong (λ t → 1ℝ -ℝ t) hmul') hright

oneMinusMulLeSum : ∀ {a q s : ℝ} →
  0ℝ ≤ℝ a → a ≤ℝ 1ℝ → 0ℝ ≤ℝ q → q ≤ℝ 1ℝ →
  1ℝ -ℝ q ≤ℝ s →
  1ℝ -ℝ ((1ℝ -ℝ a) *ℝ q) ≤ℝ a +ℝ s
oneMinusMulLeSum {a} {q} {s} ha0 ha1 hq0 hq1 hs =
  let haq = mulMonotoneNonnegative ha0 ≤ℝ-refl hq0 hq1
      haq' = subst (λ t → a *ℝ q ≤ℝ t) (mulOneʳ a) haq
      hsum = +-mono-≤ hs haq'
      heq = oneMinusProductEq a q
      htarget = subst (λ t → t ≤ℝ s +ℝ a) (sym heq) hsum
  in subst (λ t → 1ℝ -ℝ ((1ℝ -ℝ a) *ℝ q) ≤ℝ t) (+-comm s a) htarget


shiftAbsoluteBoundOfInterval :
  ∀ (shift χhMean goodNumer q lower upper : ℝ) →
  shift ≡ χhMean -ℝ q *ℝ goodNumer →
  lower *ℝ q ≤ℝ χhMean →
  χhMean ≤ℝ upper *ℝ q →
  lower ≤ℝ goodNumer →
  goodNumer ≤ℝ upper →
  0ℝ ≤ℝ q →
  absℝ shift ≤ℝ (upper -ℝ lower) *ℝ q
shiftAbsoluteBoundOfInterval
  shift χhMean goodNumer q lower upper hshift hlowMean hupMean
  hlowGood hupGood hq0 =
  let hlowerUpper = ≤ℝ-trans hlowGood hupGood
      hlowerQNonneg = subNonnegative hlowerUpper
      hrNonneg = mulNonnegative hlowerQNonneg hq0
      hlowerQ_le_qGood =
        subst (λ t → lower *ℝ q ≤ℝ t) (*-comm goodNumer q)
          (mulRightMonoNonneg hlowGood hq0)
      hqGood_le_upperQ =
        subst (λ t → t ≤ℝ upper *ℝ q) (*-comm goodNumer q)
          (mulRightMonoNonneg hupGood hq0)
      hupper =
        ≤ℝ-trans (subLeSub hupMean hlowerQ_le_qGood)
          (subst (λ t → upper *ℝ q -ℝ lower *ℝ q ≤ℝ t)
            (sym (subMulDistributes upper lower q)) ≤ℝ-refl)
      hlowerBase = subLeSub hlowMean hqGood_le_upperQ
      hlower =
        subst (λ t → t ≤ℝ χhMean -ℝ q *ℝ goodNumer)
          (sym (negℝ-sub (upper *ℝ q) (lower *ℝ q))) hlowerBase
      hshiftUpper = subst (λ t → t ≤ℝ (upper -ℝ lower) *ℝ q) (sym hshift) hupper
      hlower0 =
        subst (λ t → (-ℝ t) ≤ℝ χhMean -ℝ q *ℝ goodNumer)
          (sym (subMulDistributes upper lower q)) hlower
      hlower' =
        subst (λ t → t ≤ℝ χhMean -ℝ q *ℝ goodNumer)
          (negEqSubZero ((upper -ℝ lower) *ℝ q)) hlower0
      hshiftLower = subst (λ t → (0ℝ -ℝ (upper -ℝ lower) *ℝ q) ≤ℝ t) (sym hshift) hlower'
  in absBound shift ((upper -ℝ lower) *ℝ q) hrNonneg hshiftLower hshiftUpper
