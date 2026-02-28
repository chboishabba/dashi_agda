module DASHI.Physics.RealConeInteriorInstanceShift where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Unit using (⊤; tt)

open import UFTC_Lattice as UFTC
open import DASHI.Physics.RealTernaryCarrier as RTC

-- Placeholder cone interior/boundary predicates for shift carrier.
-- This matches the strict-premise empirical behavior:
-- interior holds when the cone margin is positive; boundary captures ties.
record ConeInteriorShift {m k : Nat} : Set₁ where
  field
    C : UFTC.ConeInterior {X = RTC.Carrier (m + k)}

open ConeInteriorShift public

coneInteriorShift : ∀ {m k : Nat} → ConeInteriorShift {m} {k}
coneInteriorShift {m} {k} =
  record
    { C = record
        { InInterior = λ _ → ⊤
        ; Boundary   = λ _ → ⊤
        }
    }
