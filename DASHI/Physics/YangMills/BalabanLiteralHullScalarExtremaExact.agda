module DASHI.Physics.YangMills.BalabanLiteralHullScalarExtremaExact where

-- Endpoint selection is stable under multiplication by an ARBITRARY
-- rational scalar. No sign assumption is necessary: this is an
-- order-theoretic statement about choosing one of the original corners.
-- These lemmas are not an assertion that multiplication is monotone.

open import Data.Rational.Base as ℚ using (ℚ; _≤_; _*_)
import Data.Rational.Properties as ℚP
open import Data.Sum.Base using (inj₁; inj₂)
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed

min2TimesLower : ∀ {bound a b} scalar →
  bound ≤ a * scalar → bound ≤ b * scalar →
  bound ≤ Typed.min2 a b * scalar
min2TimesLower {a = a} {b = b} scalar aBound bBound
  with ℚP.≤-total a b
... | inj₁ _ = aBound
... | inj₂ _ = bBound

max2TimesLower : ∀ {bound a b} scalar →
  bound ≤ a * scalar → bound ≤ b * scalar →
  bound ≤ Typed.max2 a b * scalar
max2TimesLower {a = a} {b = b} scalar aBound bBound
  with ℚP.≤-total a b
... | inj₁ _ = bBound
... | inj₂ _ = aBound

min2TimesUpper : ∀ {bound a b} scalar →
  a * scalar ≤ bound → b * scalar ≤ bound →
  Typed.min2 a b * scalar ≤ bound
min2TimesUpper {a = a} {b = b} scalar aBound bBound
  with ℚP.≤-total a b
... | inj₁ _ = aBound
... | inj₂ _ = bBound

max2TimesUpper : ∀ {bound a b} scalar →
  a * scalar ≤ bound → b * scalar ≤ bound →
  Typed.max2 a b * scalar ≤ bound
max2TimesUpper {a = a} {b = b} scalar aBound bBound
  with ℚP.≤-total a b
... | inj₁ _ = bBound
... | inj₂ _ = aBound

min4TimesLower : ∀ {bound a b c d} scalar →
  bound ≤ a * scalar → bound ≤ b * scalar →
  bound ≤ c * scalar → bound ≤ d * scalar →
  bound ≤ Typed.min4 a b c d * scalar
min4TimesLower scalar a b c d =
  min2TimesLower scalar
    (min2TimesLower scalar a b)
    (min2TimesLower scalar c d)

max4TimesLower : ∀ {bound a b c d} scalar →
  bound ≤ a * scalar → bound ≤ b * scalar →
  bound ≤ c * scalar → bound ≤ d * scalar →
  bound ≤ Typed.max4 a b c d * scalar
max4TimesLower scalar a b c d =
  max2TimesLower scalar
    (max2TimesLower scalar a b)
    (max2TimesLower scalar c d)

min4TimesUpper : ∀ {bound a b c d} scalar →
  a * scalar ≤ bound → b * scalar ≤ bound →
  c * scalar ≤ bound → d * scalar ≤ bound →
  Typed.min4 a b c d * scalar ≤ bound
min4TimesUpper scalar a b c d =
  min2TimesUpper scalar
    (min2TimesUpper scalar a b)
    (min2TimesUpper scalar c d)

max4TimesUpper : ∀ {bound a b c d} scalar →
  a * scalar ≤ bound → b * scalar ≤ bound →
  c * scalar ≤ bound → d * scalar ≤ bound →
  Typed.max4 a b c d * scalar ≤ bound
max4TimesUpper scalar a b c d =
  max2TimesUpper scalar
    (max2TimesUpper scalar a b)
    (max2TimesUpper scalar c d)

-- The corresponding left-scalar lemmas can be obtained via rational
-- multiplication commutativity; avoiding sign splits remains essential.
-- Pair these selection lemmas with multiplyIntervalSound to finish
-- both directions of the four nested-hull extremality comparisons.
