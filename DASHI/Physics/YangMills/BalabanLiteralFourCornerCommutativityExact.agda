module DASHI.Physics.YangMills.BalabanLiteralFourCornerCommutativityExact where

-- Constructive commutativity of the actual rational four-corner product
-- in BalabanClayT4TypedRationalExpressionIntervalExact.
-- Equality is on rational lower and upper endpoints, not on arbitrary
-- ordering-proof fields of the dependent RationalInterval record.
-- No type-level postulates, no new interval operation or invented carrier.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _≤_; _*_)
import Data.Rational.Properties as ℚP
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong₂; trans; sym)

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed
import DASHI.Physics.YangMills.BalabanLiteralRationalEndpointSemiringExact as End

min2Greatest : ∀ {z x y} → z ≤ x → z ≤ y →
  z ≤ Typed.min2 x y
min2Greatest {z} {x} {y} zx zy with ℚP.≤-total x y
... | inj₁ _ = zx
... | inj₂ _ = zy

max2Least : ∀ {x y z} → x ≤ z → y ≤ z →
  Typed.max2 x y ≤ z
max2Least {x} {y} {z} xz yz with ℚP.≤-total x y
... | inj₁ _ = yz
... | inj₂ _ = xz

min4Greatest : ∀ {z a b c d} →
  z ≤ a → z ≤ b → z ≤ c → z ≤ d →
  z ≤ Typed.min4 a b c d
min4Greatest za zb zc zd =
  min2Greatest (min2Greatest za zb) (min2Greatest zc zd)

max4Least : ∀ {a b c d z} →
  a ≤ z → b ≤ z → c ≤ z → d ≤ z →
  Typed.max4 a b c d ≤ z
max4Least az bz cz dz =
  max2Least (max2Least az bz) (max2Least cz dz)

-- The four-corner hull is invariant under the transpose of the
-- 2×2 corner array, swapping its middle two entries.
min4MiddleSwap : ∀ a b c d →
  Typed.min4 a b c d ≡ Typed.min4 a c b d
min4MiddleSwap a b c d = ℚP.≤-antisym
  (min4Greatest
    (Typed.min4BelowFirst a b c d)
    (Typed.min4BelowThird a b c d)
    (Typed.min4BelowSecond a b c d)
    (Typed.min4BelowFourth a b c d))
  (min4Greatest
    (Typed.min4BelowFirst a c b d)
    (Typed.min4BelowThird a c b d)
    (Typed.min4BelowSecond a c b d)
    (Typed.min4BelowFourth a c b d))

max4MiddleSwap : ∀ a b c d →
  Typed.max4 a b c d ≡ Typed.max4 a c b d
max4MiddleSwap a b c d = ℚP.≤-antisym
  (max4Least
    (Typed.firstBelowMax4 a c b d)
    (Typed.thirdBelowMax4 a c b d)
    (Typed.secondBelowMax4 a c b d)
    (Typed.fourthBelowMax4 a c b d))
  (max4Least
    (Typed.firstBelowMax4 a b c d)
    (Typed.thirdBelowMax4 a b c d)
    (Typed.secondBelowMax4 a b c d)
    (Typed.fourthBelowMax4 a b c d))

-- Literal four-corner rational products for [a,b] * [c,d].
productLL productLU productUL productUU :
  Eval.RationalInterval → Eval.RationalInterval → ℚ
productLL x y = Eval.lower x * Eval.lower y
productLU x y = Eval.lower x * Eval.upper y
productUL x y = Eval.upper x * Eval.lower y
productUU x y = Eval.upper x * Eval.upper y

productLower : Eval.RationalInterval → Eval.RationalInterval → ℚ
productLower x y = Typed.min4
  (productLL x y) (productLU x y)
  (productUL x y) (productUU x y)

productUpper : Eval.RationalInterval → Eval.RationalInterval → ℚ
productUpper x y = Typed.max4
  (productLL x y) (productLU x y)
  (productUL x y) (productUU x y)

lowerIsOriginal : ∀ x y →
  Eval.lower (Typed.multiplyInterval x y) ≡ productLower x y
lowerIsOriginal x y = refl

upperIsOriginal : ∀ x y →
  Eval.upper (Typed.multiplyInterval x y) ≡ productUpper x y
upperIsOriginal x y = refl

productLowerCommutative : ∀ x y →
  productLower x y ≡ productLower y x
productLowerCommutative x y =
  trans
    (cong₂ Typed.min2
      (cong₂ Typed.min2
        (ℚP.*-comm (Eval.lower x) (Eval.lower y))
        (ℚP.*-comm (Eval.lower x) (Eval.upper y)))
      (cong₂ Typed.min2
        (ℚP.*-comm (Eval.upper x) (Eval.lower y))
        (ℚP.*-comm (Eval.upper x) (Eval.upper y))))
    (min4MiddleSwap
      (productLL y x) (productUL y x)
      (productLU y x) (productUU y x))

productUpperCommutative : ∀ x y →
  productUpper x y ≡ productUpper y x
productUpperCommutative x y =
  trans
    (cong₂ Typed.max2
      (cong₂ Typed.max2
        (ℚP.*-comm (Eval.lower x) (Eval.lower y))
        (ℚP.*-comm (Eval.lower x) (Eval.upper y)))
      (cong₂ Typed.max2
        (ℚP.*-comm (Eval.upper x) (Eval.lower y))
        (ℚP.*-comm (Eval.upper x) (Eval.upper y))))
    (max4MiddleSwap
      (productLL y x) (productUL y x)
      (productLU y x) (productUU y x))

typedFourCornerMultiplyEndpointCommutative :
  (x y : Eval.RationalInterval) →
  End.SameEndpoints
    (Typed.multiplyInterval x y)
    (Typed.multiplyInterval y x)
typedFourCornerMultiplyEndpointCommutative x y =
  End.sameEndpoints
    (productLowerCommutative x y)
    (productUpperCommutative x y)

-- Multiplication associativity requires eight-corner hull transport;
-- this module does NOT infer it from commutativity, nor falsely
-- upgrade endpoint equality to proof-containing record identity.
