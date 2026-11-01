module DASHI.Physics.Closure.MDLFejerAxiomsShift where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat using (_≤_)

open import DASHI.MDL.MDLDescentTradeoff as MDL using (MDLParts; OrderedMonoid)
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
open import DASHI.Physics.RealTernaryCarrier as RTC

private
  Parts : ∀ {m k : Nat} → MDL.MDLParts (RTC.Carrier (m + k)) MSI.NatOrderedMonoid
  Parts {m} {k} = MSI.MDLPartsShift {m} {k}

  Trade : ∀ {m k : Nat} → MDL.TradeoffLemma (Parts {m} {k})
  Trade {m} {k} = MSI.TradeoffShift {m} {k}

-- Formalizes the empirical finding: MDL-style energy is Fejér/monotone
-- under the shift operator (closest-point geometry, not raw χ²).
record MDLFejerAxiomsShift : Set₁ where
  field
    mdlFejer :
      ∀ {m k : Nat} (x : RTC.Carrier (m + k)) →
      (MDL.MDLParts.MDL (Parts {m} {k})
        (MDL.MDLParts.T (Parts {m} {k}) x))
      ≤
      (MDL.MDLParts.MDL (Parts {m} {k}) x)

open MDLFejerAxiomsShift public

-- Concrete instance: derived from the tradeoff-based MDL descent proof.
mdlFejerShift : MDLFejerAxiomsShift
mdlFejerShift =
  record
    { mdlFejer = λ {m} {k} x →
        MDL.MDLDescent (Parts {m} {k}) (Trade {m} {k}) x
    }
