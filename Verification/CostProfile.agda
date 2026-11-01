module Verification.CostProfile where

open import Verification.Prelude

postulate Program : Set

-- Abstract cost model (time, memory, steps, gas...)
record Cost : Set where
  constructor cost
  field
    time  : Nat
    mem   : Nat
    io    : Nat

postulate profile : Program → Cost

-- Thresholds
record Budget : Set where
  constructor budget
  field
    maxTime : Nat
    maxMem  : Nat
    maxIO   : Nat

-- ≤ relation can be imported from stdlib; keep abstract here:


record CostWithin : Set where
  field
    P : Program
    B : Budget
    okTime : Cost.time (profile P) ≤ Budget.maxTime B
    okMem  : Cost.mem  (profile P) ≤ Budget.maxMem  B
    okIO   : Cost.io   (profile P) ≤ Budget.maxIO   B
