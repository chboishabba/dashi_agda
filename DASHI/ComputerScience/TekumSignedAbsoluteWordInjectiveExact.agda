module DASHI.ComputerScience.TekumSignedAbsoluteWordInjectiveExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (suc)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.Nat.Properties using (suc-injective)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source

------------------------------------------------------------------------
-- SIGN + ABSOLUTE INTEGER VALUE IS A COMPLETE SOURCE-WORD KEY
------------------------------------------------------------------------

signAbsoluteIntegerInjective :
  (x y : ℤ) →
  Source.signOfInteger x ≡ Source.signOfInteger y →
  ℤ.∣ x ∣ ≡ ℤ.∣ y ∣ →
  x ≡ y
signAbsoluteIntegerInjective (+ 0) (+ 0) signEq magnitudeEq = refl
signAbsoluteIntegerInjective (+ 0) (+ (suc n)) () magnitudeEq
signAbsoluteIntegerInjective (+ 0) -[1+ n ] () magnitudeEq
signAbsoluteIntegerInjective (+ (suc m)) (+ 0) () magnitudeEq
signAbsoluteIntegerInjective (+ (suc m)) (+ (suc n)) signEq magnitudeEq =
  cong +_ magnitudeEq
signAbsoluteIntegerInjective (+ (suc m)) -[1+ n ] () magnitudeEq
signAbsoluteIntegerInjective -[1+ m ] (+ 0) () magnitudeEq
signAbsoluteIntegerInjective -[1+ m ] (+ (suc n)) () magnitudeEq
signAbsoluteIntegerInjective -[1+ m ] -[1+ n ] signEq magnitudeEq =
  cong (λ k → -[1+ k ]) (suc-injective magnitudeEq)

sameSignAbsoluteValueDeterminesSourceWord :
  ∀ {n} {left right : Vec Trit.Trit n} →
  Source.signOfWord left ≡ Source.signOfWord right →
  ℤ.∣ BT.toInteger (BT.eval left) ∣
  ≡ ℤ.∣ BT.toInteger (BT.eval right) ∣ →
  left ≡ right
sameSignAbsoluteValueDeterminesSourceWord {left = left} {right = right}
    signEq magnitudeEq =
  Positional.toIntegerInjective
    (signAbsoluteIntegerInjective
      (BT.toInteger (BT.eval left))
      (BT.toInteger (BT.eval right))
      signEq magnitudeEq)
