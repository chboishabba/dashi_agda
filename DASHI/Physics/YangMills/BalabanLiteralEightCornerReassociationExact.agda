module DASHI.Physics.YangMills.BalabanLiteralEightCornerReassociationExact where

-- Universal eight-corner rational reassociation. This proves the equality
-- of the two eight-corner hulls; it does NOT silently identify either
-- with the NESTED four-corner interval evaluation.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _≤_; _*_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed
import DASHI.Physics.YangMills.BalabanLiteralFourCornerCommutativityExact as Four
import DASHI.Physics.YangMills.BalabanLiteralEndpointEvaluatorCongruenceExact as Cong

min8 max8 : (a b c d e f g h : ℚ) → ℚ
min8 a b c d e f g h =
  Typed.min2 (Typed.min4 a b c d) (Typed.min4 e f g h)
max8 a b c d e f g h =
  Typed.max2 (Typed.max4 a b c d) (Typed.max4 e f g h)

min8Greatest : ∀ {z a b c d e f g h} →
  z ≤ a → z ≤ b → z ≤ c → z ≤ d →
  z ≤ e → z ≤ f → z ≤ g → z ≤ h →
  z ≤ min8 a b c d e f g h
min8Greatest za zb zc zd ze zf zg zh =
  Four.min2Greatest (Four.min4Greatest za zb zc zd)
                    (Four.min4Greatest ze zf zg zh)

max8Least : ∀ {a b c d e f g h z} →
  a ≤ z → b ≤ z → c ≤ z → d ≤ z →
  e ≤ z → f ≤ z → g ≤ z → h ≤ z →
  max8 a b c d e f g h ≤ z
max8Least az bz cz dz ez fz gz hz =
  Four.max2Least (Four.max4Least az bz cz dz)
                 (Four.max4Least ez fz gz hz)

min8Cong :
  ∀ {a b c d e f g h a′ b′ c′ d′ e′ f′ g′ h′} →
  a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ →
  e ≡ e′ → f ≡ f′ → g ≡ g′ → h ≡ h′ →
  min8 a b c d e f g h ≡ min8 a′ b′ c′ d′ e′ f′ g′ h′
min8Cong aa bb cc dd ee ff gg hh =
  cong₂ Typed.min2 (Cong.min4Cong aa bb cc dd)
                   (Cong.min4Cong ee ff gg hh)

max8Cong :
  ∀ {a b c d e f g h a′ b′ c′ d′ e′ f′ g′ h′} →
  a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ →
  e ≡ e′ → f ≡ f′ → g ≡ g′ → h ≡ h′ →
  max8 a b c d e f g h ≡ max8 a′ b′ c′ d′ e′ f′ g′ h′
max8Cong aa bb cc dd ee ff gg hh =
  cong₂ Typed.max2 (Cong.max4Cong aa bb cc dd)
                   (Cong.max4Cong ee ff gg hh)

-- A single boolean-free enumeration of the eight ACTUAL corner products.
-- The lower and upper extrema share the same exact rational corner list.
leftCorners rightCorners : (ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ) →
  Eval.RationalInterval → Eval.RationalInterval → Eval.RationalInterval → ℚ
leftCorners hull x y z = hull
  ((Eval.lower x * Eval.lower y) * Eval.lower z)
  ((Eval.lower x * Eval.lower y) * Eval.upper z)
  ((Eval.lower x * Eval.upper y) * Eval.lower z)
  ((Eval.lower x * Eval.upper y) * Eval.upper z)
  ((Eval.upper x * Eval.lower y) * Eval.lower z)
  ((Eval.upper x * Eval.lower y) * Eval.upper z)
  ((Eval.upper x * Eval.upper y) * Eval.lower z)
  ((Eval.upper x * Eval.upper y) * Eval.upper z)
rightCorners hull x y z = hull
  (Eval.lower x * (Eval.lower y * Eval.lower z))
  (Eval.lower x * (Eval.lower y * Eval.upper z))
  (Eval.lower x * (Eval.upper y * Eval.lower z))
  (Eval.lower x * (Eval.upper y * Eval.upper z))
  (Eval.upper x * (Eval.lower y * Eval.lower z))
  (Eval.upper x * (Eval.lower y * Eval.upper z))
  (Eval.upper x * (Eval.upper y * Eval.lower z))
  (Eval.upper x * (Eval.upper y * Eval.upper z))

eightCornerLowerReassociation : ∀ x y z →
  leftCorners min8 x y z ≡ rightCorners min8 x y z
eightCornerLowerReassociation x y z = min8Cong
  (ℚP.*-assoc (Eval.lower x) (Eval.lower y) (Eval.lower z))
  (ℚP.*-assoc (Eval.lower x) (Eval.lower y) (Eval.upper z))
  (ℚP.*-assoc (Eval.lower x) (Eval.upper y) (Eval.lower z))
  (ℚP.*-assoc (Eval.lower x) (Eval.upper y) (Eval.upper z))
  (ℚP.*-assoc (Eval.upper x) (Eval.lower y) (Eval.lower z))
  (ℚP.*-assoc (Eval.upper x) (Eval.lower y) (Eval.upper z))
  (ℚP.*-assoc (Eval.upper x) (Eval.upper y) (Eval.lower z))
  (ℚP.*-assoc (Eval.upper x) (Eval.upper y) (Eval.upper z))

eightCornerUpperReassociation : ∀ x y z →
  leftCorners max8 x y z ≡ rightCorners max8 x y z
eightCornerUpperReassociation x y z = max8Cong
  (ℚP.*-assoc (Eval.lower x) (Eval.lower y) (Eval.lower z))
  (ℚP.*-assoc (Eval.lower x) (Eval.lower y) (Eval.upper z))
  (ℚP.*-assoc (Eval.lower x) (Eval.upper y) (Eval.lower z))
  (ℚP.*-assoc (Eval.lower x) (Eval.upper y) (Eval.upper z))
  (ℚP.*-assoc (Eval.upper x) (Eval.lower y) (Eval.lower z))
  (ℚP.*-assoc (Eval.upper x) (Eval.lower y) (Eval.upper z))
  (ℚP.*-assoc (Eval.upper x) (Eval.upper y) (Eval.lower z))
  (ℚP.*-assoc (Eval.upper x) (Eval.upper y) (Eval.upper z))

-- Remaining four hull-extremality equalities:
-- lower (multiply (multiply x y) z) = leftCorners min8 x y z
-- lower (multiply x (multiply y z)) = rightCorners min8 x y z
-- and analogously for upper / max8.
