module DASHI.Combinatorics.NGram where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; []; _∷_; map)

open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Metric.AgreementUltrametric as AUM

------------------------------------------------------------------------
-- Typed n-gram surface over the canonical DASHI ternary carrier.
--
-- This module only names fixed-width windows and finite n-grams of those
-- windows.  It is not an ITIR import layer and does not assign text semantics
-- to the ternary carrier.

two : Nat
two = suc (suc zero)

three : Nat
three = suc two

Window : Nat → Set
Window width = RTC.Carrier width

NGram : Nat → Nat → Set
NGram width arity = Vec (Window width) arity

Bigram : Nat → Set
Bigram width = NGram width two

Trigram : Nat → Set
Trigram width = NGram width three

mkBigram :
  ∀ {width : Nat} →
  Window width →
  Window width →
  Bigram width
mkBigram x y = x ∷ y ∷ []

mkTrigram :
  ∀ {width : Nat} →
  Window width →
  Window width →
  Window width →
  Trigram width
mkTrigram x y z = x ∷ y ∷ z ∷ []

firstWindow :
  ∀ {width arity : Nat} →
  NGram width (suc arity) →
  Window width
firstWindow (x ∷ _) = x

restWindows :
  ∀ {width arity : Nat} →
  NGram width (suc arity) →
  NGram width arity
restWindows (_ ∷ xs) = xs

bigramLeft :
  ∀ {width : Nat} →
  Bigram width →
  Window width
bigramLeft (x ∷ _ ∷ []) = x

bigramRight :
  ∀ {width : Nat} →
  Bigram width →
  Window width
bigramRight (_ ∷ y ∷ []) = y

trigramLeft :
  ∀ {width : Nat} →
  Trigram width →
  Window width
trigramLeft (x ∷ _ ∷ _ ∷ []) = x

trigramMiddle :
  ∀ {width : Nat} →
  Trigram width →
  Window width
trigramMiddle (_ ∷ y ∷ _ ∷ []) = y

trigramRight :
  ∀ {width : Nat} →
  Trigram width →
  Window width
trigramRight (_ ∷ _ ∷ z ∷ []) = z

invertWindows :
  ∀ {width arity : Nat} →
  NGram width arity →
  NGram width arity
invertWindows = map RTC.invVec

windowAgreementDepth :
  ∀ {width : Nat} →
  Window width →
  Window width →
  Nat
windowAgreementDepth = AUM.agreeDepth

windowDistance :
  ∀ {width : Nat} →
  Window width →
  Window width →
  Nat
windowDistance = AUM.dNat

bigramAdjacentDistance :
  ∀ {width : Nat} →
  Bigram width →
  Nat
bigramAdjacentDistance bg =
  windowDistance (bigramLeft bg) (bigramRight bg)

trigramAdjacentDistances :
  ∀ {width : Nat} →
  Trigram width →
  Nat × Nat
trigramAdjacentDistances tg =
  windowDistance (trigramLeft tg) (trigramMiddle tg)
  ,
  windowDistance (trigramMiddle tg) (trigramRight tg)
