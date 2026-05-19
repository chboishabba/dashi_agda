module DASHI.Physics.Closure.W9LyapunovAdapterReceipt where

-- Planck/W9: narrow Lyapunov adapter for the normalize-add carry pressure.
--
-- This receipt constructs the repo's current CancellationPressureLyapunovBridge
-- interface for the state-side pressure `carryDepth + carryBudget`.  It is not
-- a dim-15 pressure/Qcore compatibility witness and does not discharge
-- CancellationPressureCompatibility.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_+_; _≤_; z≤n)
open import Data.Nat.Properties as NatP using (≤-refl)
open import Data.Unit using (⊤)

import DASHI.Arithmetic.CancellationPressureCore as Core
import DASHI.Arithmetic.CancellationPressureLyapunovBridge as Bridge
import DASHI.Arithmetic.CancellationPressureMDL as CP-MDL
import DASHI.Arithmetic.NormalizeAdd as NA
import DASHI.Arithmetic.NormalizeAddState as NAS
import DASHI.MDL.MDLLyapunov as MDL

carryDepthBudgetPressure : NAS.NormalizeAddState → Nat
carryDepthBudgetPressure s =
  NAS.carryDepth s + NAS.carryBudget s

carryDepthBudgetPressure-step :
  ∀ s →
  carryDepthBudgetPressure (NA.normalizeAdd s)
    ≤
  carryDepthBudgetPressure s
carryDepthBudgetPressure-step _ = z≤n

carryDepthBudgetPressureCore : Core.CancellationPressureCore
carryDepthBudgetPressureCore =
  record
    { Carrier = NAS.NormalizeAddState
    ; step = NA.normalizeAdd
    ; cancellationPressure = carryDepthBudgetPressure
    ; pressure-step = carryDepthBudgetPressure-step
    }

carryDepthBudgetMDLFunctional :
  MDL.MDLFunctional NAS.NormalizeAddState
carryDepthBudgetMDLFunctional =
  record
    { model = λ _ → zero
    ; residual = carryDepthBudgetPressure
    ; mdl = carryDepthBudgetPressure
    ; mdl≡ = λ _ → refl
    }

carryDepthBudgetCancellationPressureMDL :
  CP-MDL.CancellationPressureMDL carryDepthBudgetPressureCore
carryDepthBudgetCancellationPressureMDL =
  record
    { mdlFunctional = carryDepthBudgetMDLFunctional
    ; cancellationPressure≈mdl = λ _ → refl
    ; residual≤pressure = λ _ → NatP.≤-refl
    }

carryDepthBudgetMDLLyapunov :
  MDL.MDLLyapunov
    NA.normalizeAdd
    carryDepthBudgetMDLFunctional
carryDepthBudgetMDLLyapunov =
  record
    { decreases = carryDepthBudgetPressure-step
    ; strictUnlessFixed = ⊤
    }

carryDepthBudgetLyapunovBridge :
  Bridge.CancellationPressureLyapunovBridge carryDepthBudgetPressureCore
carryDepthBudgetLyapunovBridge =
  record
    { mdlBridge = carryDepthBudgetCancellationPressureMDL
    ; lyapunov = carryDepthBudgetMDLLyapunov
    }

data W9LyapunovAdapterStatus : Set where
  carryDepthBudgetBridgeConstructedNonPromoting :
    W9LyapunovAdapterStatus

record W9LyapunovAdapterReceipt : Setω where
  field
    pressure :
      NAS.NormalizeAddState → Nat

    pressureIsCarryDepthPlusCarryBudget :
      pressure ≡ carryDepthBudgetPressure

    core :
      Core.CancellationPressureCore

    coreIsCarryDepthBudget :
      core ≡ carryDepthBudgetPressureCore

    mdlFunctional :
      MDL.MDLFunctional NAS.NormalizeAddState

    mdlBridge :
      CP-MDL.CancellationPressureMDL core

    lyapunovBridge :
      Bridge.CancellationPressureLyapunovBridge core

    descent :
      ∀ s →
      pressure (NA.normalizeAdd s)
        ≤
      pressure s

    status :
      W9LyapunovAdapterStatus

    nonPromotionBoundary :
      List String

canonicalW9LyapunovAdapterReceipt :
  W9LyapunovAdapterReceipt
canonicalW9LyapunovAdapterReceipt =
  record
    { pressure = carryDepthBudgetPressure
    ; pressureIsCarryDepthPlusCarryBudget = refl
    ; core = carryDepthBudgetPressureCore
    ; coreIsCarryDepthBudget = refl
    ; mdlFunctional = carryDepthBudgetMDLFunctional
    ; mdlBridge = carryDepthBudgetCancellationPressureMDL
    ; lyapunovBridge = carryDepthBudgetLyapunovBridge
    ; descent = carryDepthBudgetPressure-step
    ; status = carryDepthBudgetBridgeConstructedNonPromoting
    ; nonPromotionBoundary =
        "Constructs CancellationPressureLyapunovBridge only for NormalizeAddState"
        ∷ "Uses pressure = carryDepth + carryBudget and normalizeAdd zeroing of both fields"
        ∷ "Does not construct dim-15 CancellationPressureCompatibility"
        ∷ "Does not identify pair pressure with canonical Qcore"
        ∷ "Does not change W9Dim15ClosureStatus"
        ∷ []
    }
