{-# OPTIONS --safe #-}
module DASHI.Interop.DaysAgoBoundaryExact where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Day ordinals are supplied by the caller. No calendar, timezone or
-- wall-clock timestamp semantics are asserted by this arithmetic model.
record DaysAgo : Set where
  constructor daysAgo
  field
    referenceDay : Nat
    elapsedDay : Nat
    offsetDays : Nat
    exactOffset : referenceDay ≡ elapsedDay + offsetDays

makeDaysAgo : (elapsed offset : Nat) → DaysAgo
makeDaysAgo elapsed offset =
  daysAgo (elapsed + offset) elapsed offset refl

makeDaysAgoReference : (elapsed offset : Nat) →
  DaysAgo.referenceDay (makeDaysAgo elapsed offset) ≡ elapsed + offset
makeDaysAgoReference elapsed offset = refl

makeDaysAgoOffset : (elapsed offset : Nat) →
  DaysAgo.offsetDays (makeDaysAgo elapsed offset) ≡ offset
makeDaysAgoOffset elapsed offset = refl

daysAgoEquation : (entry : DaysAgo) →
  DaysAgo.referenceDay entry ≡
  DaysAgo.elapsedDay entry + DaysAgo.offsetDays entry
daysAgoEquation = DaysAgo.exactOffset
