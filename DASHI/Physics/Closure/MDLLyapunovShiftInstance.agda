module DASHI.Physics.Closure.MDLLyapunovShiftInstance where

open import Agda.Builtin.Nat using (Nat; _+_)

open import MDL as OldMDL
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
open import DASHI.Physics.Closure.MDLDescentShiftInstance as MDSI
open import DASHI.MDL.MDLDescentTradeoff as MDL using (MDLParts)

-- Lyapunov instance for the shift stack, using the MDL tradeoff descent.
lyapunovShift : ∀ {m k : Nat} → OldMDL.Lyapunov {S = RTC.Carrier (m + k)} (MDLParts.T (MSI.MDLPartsShift {m} {k}))
lyapunovShift {m} {k} =
  let
    Parts = MSI.MDLPartsShift {m} {k}
  in
  record
    { L = MDLParts.MDL Parts
    ; descent = MDL.MDLDescent Parts (MSI.TradeoffShift {m} {k})
    }
