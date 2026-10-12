module DASHI.Mathematics.Complexity.ConcreteTapeNonblankWriteBoundExact where

------------------------------------------------------------------------
-- NONBLANK CONTENT CAN INCREASE BY AT MOST ONE PER SYMBOL WRITE
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeSymbolWriteLocalityExact as Writes

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ rest) = suc (listLength rest)

nonblankBit :
  ∀ {Symbol : Set} →
  Local.FiniteEnumeration Symbol →
  Symbol → Symbol → Nat
nonblankBit enumeration blank symbol
    with Local.decideEqual enumeration symbol blank
... | true = zero
... | false = suc zero

nonblankCount :
  ∀ {Symbol : Set} →
  Local.FiniteEnumeration Symbol →
  Symbol → List Symbol → Nat
nonblankCount enumeration blank [] = zero
nonblankCount enumeration blank (symbol ∷ symbols) =
  nonblankBit enumeration blank symbol
  + nonblankCount enumeration blank symbols

blankBitZero :
  ∀ {Symbol : Set}
    (enumeration : Local.FiniteEnumeration Symbol)
    (blank : Symbol) →
  nonblankBit enumeration blank blank ≡ zero
blankBitZero enumeration blank
    rewrite Local.decideEqualRefl enumeration blank = refl

nonblankBitAtMostOne :
  ∀ {Symbol : Set}
    (enumeration : Local.FiniteEnumeration Symbol)
    (blank symbol : Symbol) →
  nonblankBit enumeration blank symbol ≤ suc zero
nonblankBitAtMostOne enumeration blank symbol
    with Local.decideEqual enumeration symbol blank
... | true = NatP.z≤n
... | false = NatP.≤-refl _

nonblankCountBelowLength :
  ∀ {Symbol : Set}
    (enumeration : Local.FiniteEnumeration Symbol)
    (blank : Symbol)
    (symbols : List Symbol) →
  nonblankCount enumeration blank symbols
  ≤ listLength symbols
nonblankCountBelowLength enumeration blank [] = NatP.≤-refl _
nonblankCountBelowLength enumeration blank (symbol ∷ symbols) =
  NatP.+-mono-≤
    (nonblankBitAtMostOne enumeration blank symbol)
    (nonblankCountBelowLength enumeration blank symbols)

atMostOneWriteNonblankBound :
  ∀ {Symbol : Set}
    (enumeration : Local.FiniteEnumeration Symbol)
    (blank : Symbol)
    {before after : List Symbol} →
  Writes.AtMostOneSymbolWrite before after →
  nonblankCount enumeration blank after
  ≤ suc (nonblankCount enumeration blank before)
atMostOneWriteNonblankBound enumeration blank Writes.noWrite =
  NatP.n≤1+n _
atMostOneWriteNonblankBound enumeration blank
    (Writes.writeHead {old = old} {new = new} {rest = rest}) =
  NatP.≤-trans
    (NatP.+-mono-≤
      (nonblankBitAtMostOne enumeration blank new)
      (NatP.≤-refl (nonblankCount enumeration blank rest)))
    onePlusRestBelowTarget
  where
    restBelowOldPlusRest :
      nonblankCount enumeration blank rest
      ≤
      nonblankBit enumeration blank old
        + nonblankCount enumeration blank rest
    restBelowOldPlusRest =
      NatP.m≤n+m
        (nonblankCount enumeration blank rest)
        (nonblankBit enumeration blank old)

    onePlusRestBelowTarget :
      suc zero + nonblankCount enumeration blank rest
      ≤
      suc
        (nonblankBit enumeration blank old
          + nonblankCount enumeration blank rest)
    onePlusRestBelowTarget =
      s≤s restBelowOldPlusRest
atMostOneWriteNonblankBound enumeration blank
    (Writes.keepHead {symbol = symbol} {before = before} {after = after} rewrite) =
  NatP.≤-trans
    (NatP.+-mono-≤
      (NatP.≤-refl (nonblankBit enumeration blank symbol))
      (atMostOneWriteNonblankBound enumeration blank rewrite))
    arithmetic
  where
    arithmetic :
      nonblankBit enumeration blank symbol
        + suc (nonblankCount enumeration blank before)
      ≤
      suc
        (nonblankBit enumeration blank symbol
          + nonblankCount enumeration blank before)
    arithmetic
      rewrite NatP.+-suc
        (nonblankBit enumeration blank symbol)
        (nonblankCount enumeration blank before) =
      NatP.≤-refl _

writesWithinNonblankBound :
  ∀ {Symbol : Set}
    (enumeration : Local.FiniteEnumeration Symbol)
    (blank : Symbol)
    {steps : Nat}
    {start finish : List Symbol} →
  Writes.SymbolWritesWithin steps start finish →
  nonblankCount enumeration blank finish
  ≤ nonblankCount enumeration blank start + steps
writesWithinNonblankBound enumeration blank Writes.writesDone =
  NatP.≤-refl _
writesWithinNonblankBound enumeration blank
    (Writes.writesStep {steps = steps} {start = start}
      {middle = middle} rewrite rest) =
  NatP.≤-trans
    (writesWithinNonblankBound enumeration blank rest)
    (NatP.≤-trans
      (NatP.+-mono-≤
        (atMostOneWriteNonblankBound enumeration blank rewrite)
        (NatP.≤-refl steps))
      arithmetic)
  where
    arithmetic :
      suc (nonblankCount enumeration blank start) + steps
      ≤ nonblankCount enumeration blank start + suc steps
    arithmetic
      rewrite NatP.+-suc (nonblankCount enumeration blank start) steps =
      NatP.≤-refl _

------------------------------------------------------------------------
-- RESOURCE CONSEQUENCE
--
-- This is the quantitative form of one-cell write locality: p prefix steps can
-- increase literal nonblank tape content by at most p, independent of how much
-- blank address space was preallocated.
------------------------------------------------------------------------
