module DASHI.ComputerScience.TekumSpecialIntegerOrderExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base as ℤ using (+_; -_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Vec.Base as Vec using (Vec; []; _∷_; replicate)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional
import DASHI.ComputerScience.TekumFiniteSemanticsExact as Sem
import DASHI.ComputerScience.TekumParsedPayloadOrderExact as PayloadOrder
import DASHI.ComputerScience.TekumSpecialValuesExact as Special

------------------------------------------------------------------------
-- BOOLEAN SPECIAL CLASSIFICATION IS PROOF-RECOVERABLE
------------------------------------------------------------------------

allSameTrueWord :
  ∀ {n} {t : Trit.Trit} {word : Vec Trit.Trit n} →
  Special.allSame t word ≡ true →
  word ≡ replicate n t
allSameTrueWord {t = Trit.neg} {word = []} eq = refl
allSameTrueWord {t = Trit.neg} {word = Trit.neg ∷ xs} eq =
  cong (Trit.neg ∷_) (allSameTrueWord eq)
allSameTrueWord {t = Trit.neg} {word = Trit.zer ∷ xs} ()
allSameTrueWord {t = Trit.neg} {word = Trit.pos ∷ xs} ()
allSameTrueWord {t = Trit.zer} {word = []} eq = refl
allSameTrueWord {t = Trit.zer} {word = Trit.neg ∷ xs} ()
allSameTrueWord {t = Trit.zer} {word = Trit.zer ∷ xs} eq =
  cong (Trit.zer ∷_) (allSameTrueWord eq)
allSameTrueWord {t = Trit.zer} {word = Trit.pos ∷ xs} ()
allSameTrueWord {t = Trit.pos} {word = []} eq = refl
allSameTrueWord {t = Trit.pos} {word = Trit.neg ∷ xs} ()
allSameTrueWord {t = Trit.pos} {word = Trit.zer ∷ xs} ()
allSameTrueWord {t = Trit.pos} {word = Trit.pos ∷ xs} eq =
  cong (Trit.pos ∷_) (allSameTrueWord eq)

classifyNaRWord :
  ∀ {n} {word : Vec Trit.Trit n} →
  Special.classifySpecial word ≡ just Sem.naR →
  word ≡ replicate n Trit.neg
classifyNaRWord {word = word} classifyEq
  with Special.allSame Trit.neg word in negEq
... | true = allSameTrueWord negEq
... | false with Special.allSame Trit.zer word
...   | true with classifyEq
...     | ()
...   | false with Special.allSame Trit.pos word
...     | true with classifyEq
...       | ()
...     | false with classifyEq
...       | ()

classifyZeroWord :
  ∀ {n} {word : Vec Trit.Trit n} →
  Special.classifySpecial word ≡ just Sem.zeroValue →
  word ≡ replicate n Trit.zer
classifyZeroWord {word = word} classifyEq
  with Special.allSame Trit.neg word
... | true with classifyEq
...   | ()
... | false with Special.allSame Trit.zer word in zeroEq
...   | true = allSameTrueWord zeroEq
...   | false with Special.allSame Trit.pos word
...     | true with classifyEq
...       | ()
...     | false with classifyEq
...       | ()

classifyInfinityWord :
  ∀ {n} {word : Vec Trit.Trit n} →
  Special.classifySpecial word ≡ just Sem.infinity →
  word ≡ replicate n Trit.pos
classifyInfinityWord {word = word} classifyEq
  with Special.allSame Trit.neg word
... | true with classifyEq
...   | ()
... | false with Special.allSame Trit.zer word
...   | true with classifyEq
...     | ()
...   | false with Special.allSame Trit.pos word in posEq
...     | true = allSameTrueWord posEq
...     | false with classifyEq
...       | ()

------------------------------------------------------------------------
-- EXACT INTEGER CODES OF THE THREE RESERVED WORDS
------------------------------------------------------------------------

allNegativeNatCode :
  (n : Nat) → Positional.natCode (replicate n Trit.neg) ≡ 0
allNegativeNatCode zero = refl
allNegativeNatCode (suc n)
  rewrite allNegativeNatCode n = refl

allNegativeInteger :
  (n : Nat) →
  BT.toInteger (BT.eval (replicate n Trit.neg))
  ≡ ℤ.- (+ (Positional.center n))
allNegativeInteger n
  rewrite PayloadOrder.integerFromNatCode (replicate n Trit.neg)
        | allNegativeNatCode n = refl

allZeroInteger :
  (n : Nat) →
  BT.toInteger (BT.eval (replicate n Trit.zer)) ≡ + 0
allZeroInteger zero = refl
allZeroInteger (suc n)
  rewrite Positional.evalIntegerCons Trit.zer (replicate n Trit.zer)
        | allZeroInteger n = refl

invertAllNegative :
  (n : Nat) →
  BT.invertWord (replicate n Trit.neg) ≡ replicate n Trit.pos
invertAllNegative zero = refl
invertAllNegative (suc n)
  rewrite invertAllNegative n = refl

allPositiveInteger :
  (n : Nat) →
  BT.toInteger (BT.eval (replicate n Trit.pos))
  ≡ + (Positional.center n)
allPositiveInteger n =
  trans
    (cong (λ word → BT.toInteger (BT.eval word))
      (sym (invertAllNegative n)))
    (trans
      (BT.toIntegerInvertWord (replicate n Trit.neg))
      (trans
        (cong ℤ.-_ (allNegativeInteger n))
        (Data.Integer.Properties.neg-involutive (+ (Positional.center n)))))

classifiedNaRInteger :
  ∀ {n} {word : Vec Trit.Trit n} →
  Special.classifySpecial word ≡ just Sem.naR →
  BT.toInteger (BT.eval word) ≡ ℤ.- (+ (Positional.center n))
classifiedNaRInteger {n} {word} classifyEq =
  trans
    (cong (λ w → BT.toInteger (BT.eval w)) (classifyNaRWord classifyEq))
    (allNegativeInteger n)

classifiedZeroInteger :
  ∀ {n} {word : Vec Trit.Trit n} →
  Special.classifySpecial word ≡ just Sem.zeroValue →
  BT.toInteger (BT.eval word) ≡ + 0
classifiedZeroInteger {n} {word} classifyEq =
  trans
    (cong (λ w → BT.toInteger (BT.eval w)) (classifyZeroWord classifyEq))
    (allZeroInteger n)

classifiedInfinityInteger :
  ∀ {n} {word : Vec Trit.Trit n} →
  Special.classifySpecial word ≡ just Sem.infinity →
  BT.toInteger (BT.eval word) ≡ + (Positional.center n)
classifiedInfinityInteger {n} {word} classifyEq =
  trans
    (cong (λ w → BT.toInteger (BT.eval w)) (classifyInfinityWord classifyEq))
    (allPositiveInteger n)

sameNaRWord :
  ∀ {n} {left right : Vec Trit.Trit n} →
  Special.classifySpecial left ≡ just Sem.naR →
  Special.classifySpecial right ≡ just Sem.naR →
  left ≡ right
sameNaRWord leftEq rightEq =
  trans (classifyNaRWord leftEq) (sym (classifyNaRWord rightEq))

sameZeroWord :
  ∀ {n} {left right : Vec Trit.Trit n} →
  Special.classifySpecial left ≡ just Sem.zeroValue →
  Special.classifySpecial right ≡ just Sem.zeroValue →
  left ≡ right
sameZeroWord leftEq rightEq =
  trans (classifyZeroWord leftEq) (sym (classifyZeroWord rightEq))

sameInfinityWord :
  ∀ {n} {left right : Vec Trit.Trit n} →
  Special.classifySpecial left ≡ just Sem.infinity →
  Special.classifySpecial right ≡ just Sem.infinity →
  left ≡ right
sameInfinityWord leftEq rightEq =
  trans (classifyInfinityWord leftEq) (sym (classifyInfinityWord rightEq))
