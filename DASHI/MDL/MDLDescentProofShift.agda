module DASHI.MDL.MDLDescentProofShift where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat using (_≤_; z≤n)
open import Data.Nat.Properties as NatP using (≤-refl; ≤-trans)

import DASHI.Energy.Core as EC
open import DASHI.MDL.MDLDescentProof as MDP
open import DASHI.MDL.MDLDescentTradeoff as MDT using (MDLParts)
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
open import DASHI.Physics.Closure.MDLDescentShiftInstance as MDSI
open import DASHI.Physics.RealTernaryCarrier as RTC

-- Preorder on Nat (for EnergySpace).
preorderNat : EC.Preorder Nat
preorderNat =
  record
    { _≤_ = _≤_
    ; refl = λ _ → ≤-refl
    ; trans = λ x≤y y≤z → ≤-trans x≤y y≤z
    }

energyNat : ∀ {m k : Nat} → EC.EnergySpace (RTC.Carrier (m + k)) Nat
energyNat {m} {k} =
  record
    { P = preorderNat
    ; energy = MDT.MDLParts.MDL (MSI.MDLPartsShift {m} {k})
    }

mdlNat : ∀ {m k : Nat} → MDP.MDL (RTC.Carrier (m + k)) Nat
mdlNat {m} {k} =
  record { mdl = MDT.MDLParts.MDL (MSI.MDLPartsShift {m} {k}) }

-- Concrete MDL descent proof using the shift tradeoff lemma.
descentShift :
  ∀ {m k : Nat} →
  MDP.Descent
    (energyNat {m} {k})
    (MDT.MDLParts.T (MSI.MDLPartsShift {m} {k}))
    (mdlNat {m} {k})
descentShift {m} {k} =
  record
    { descent = MDSI.mdlyapShift {m} {k}
    }
