module DASHI.Physics.Closure.MDLDescentShiftInstance where

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_)

open import DASHI.MDL.MDLDescentTradeoff as MDL using (MDLParts; TradeoffLemma; MDLDescent; OrderedMonoid)
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
open import DASHI.Physics.RealTernaryCarrier as RTC

private
  Parts : ∀ {m k : Nat} → MDL.MDLParts (RTC.Carrier (m + k)) MSI.NatOrderedMonoid
  Parts {m} {k} = MSI.MDLPartsShift {m} {k}

  Trade : ∀ {m k : Nat} → MDL.TradeoffLemma (Parts {m} {k})
  Trade {m} {k} = MSI.TradeoffShift {m} {k}

-- Concrete MDL descent for the shift stack, using the tradeoff lemma.
mdlyapShift :
  ∀ {m k : Nat} (x : RTC.Carrier (m + k)) →
  Data.Nat._≤_
    (MDL.MDLParts.MDL (Parts {m} {k})
      (MDL.MDLParts.T (Parts {m} {k}) x))
    (MDL.MDLParts.MDL (Parts {m} {k}) x)
mdlyapShift {m} {k} =
  MDL.MDLDescent (Parts {m} {k}) (Trade {m} {k})
