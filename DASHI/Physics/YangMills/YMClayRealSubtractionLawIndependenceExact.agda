module DASHI.Physics.YangMills.YMClayRealSubtractionLawIndependenceExact where

------------------------------------------------------------------------
-- P0.01 EXACT NEGATIVE CONTROL on the current RealAnalysisAxioms.
--
-- Those axioms list addition, multiplication, subtraction, etc. as
-- independent operations. The named subtraction interaction laws
-- listed below alone do NOT entail x - 0 = x, and therefore do not
-- entail the requested subtraction-as-additive-inverse theorem.
--
-- This explicitly inhabited model has ordinary Nat addition and
-- multiplication, but subtraction constantly zero. It satisfies
-- the currently named subtraction interaction fragment (subSelf,
-- subAddCancelMiddle, subAddDistributes, subMulDistributes, and
-- mulSubDistributes); nevertheless 1 - 0 = 0, not 1.
--
-- This is a NEGATIVE CONTROL for the specified scalar fragment,
-- NOT a full RealAnalysisAxioms model (which requires real/order/abs
-- laws). A coherent selected field backend, not a new physics
-- postulate, must supply the missing compatibility.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

data Empty : Set where

zeroSub : Nat → Nat → Nat
zeroSub a b = zero

zeroSubSelf : (a : Nat) → zeroSub a a ≡ zero
zeroSubSelf a = refl

zeroSubAddCancelMiddle :
  (a b c : Nat) →
  zeroSub a b + zeroSub b c ≡ zeroSub a c
zeroSubAddCancelMiddle a b c = refl

zeroSubAddDistributes :
  (a b c d : Nat) →
  zeroSub (a + b) (c + d)
    ≡ zeroSub a c + zeroSub b d
zeroSubAddDistributes a b c d = refl

zeroSubMulDistributes :
  (a b c : Nat) →
  (zeroSub a b * c)
    ≡ zeroSub (a * c) (b * c)
zeroSubMulDistributes a b c = refl

multiplyZeroRight : (a : Nat) → a * zero ≡ zero
multiplyZeroRight zero = refl
multiplyZeroRight (suc n) rewrite multiplyZeroRight n = refl

zeroMulSubDistributes :
  (a b c : Nat) →
  a * zeroSub b c ≡ zeroSub (a * b) (a * c)
zeroMulSubDistributes a b c = multiplyZeroRight a

-- This absurd proposition has no constructor. Consequently the
-- original P0.01 equality cannot be inferred merely from those
-- algebraic subtraction interaction laws.
notOneMinusZeroIsOne :
  zeroSub (suc zero) zero ≡ suc zero → Empty
notOneMinusZeroIsOne ()

oneMinusZeroIsZero :
  zeroSub (suc zero) zero ≡ zero
oneMinusZeroIsZero = refl
