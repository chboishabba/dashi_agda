module DASHI.Physics.Closure.CanonicalObservableSignatureReceiptInstance where

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat using (zero)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Nat using (z≤n)
open import Data.Product using (_,_)

import DASHI.Physics.Closure.Basin as Basin
import DASHI.Physics.Closure.DeltaToQuadraticBridgeTheorem as DQ
import DASHI.Physics.Closure.ExecutionContract as EC
import DASHI.Physics.Closure.ExecutionContractLaws as ECL
import DASHI.Physics.Closure.ObservableSignaturePressureTestInstance as OSPTI
import DASHI.Physics.Closure.Projection as Projection
import DASHI.Physics.Closure.ReceiptFromObservableSignature as RFOS

------------------------------------------------------------------------
-- Canonical execution receipt for the inhabited observable/signature path.
--
-- This is deliberately the smallest identity-step execution contract.  It
-- closes the receipt lane for the canonical promoted pressure point without
-- claiming a recovered dynamics, gauge/matter model, or nontrivial execution
-- transition.

canonicalExecutionProjection :
  Projection.Projection
    OSPTI.CanonicalShiftState
    OSPTI.CanonicalShiftState
    ⊤
    ⊤
canonicalExecutionProjection = record
  { π = λ x → x
  ; Δ = λ _ _ → tt
  ; projectΔ = λ _ → tt
  ; Δπ = λ _ _ → tt
  ; projected-delta-compatible = λ _ _ → refl
  }

canonicalExecutionBasin :
  Basin.Basin OSPTI.CanonicalShiftState
canonicalExecutionBasin = record
  { step = λ x → x
  ; StableShell = λ _ → ⊤
  ; InBasin = λ _ → ⊤
  ; basin-eventually-stable = λ _ _ → Basin.now tt
  ; basin-step = λ _ _ → tt
  }

canonicalExecutionContract :
  EC.ExecutionContract
canonicalExecutionContract = record
  { State = OSPTI.CanonicalShiftState
  ; Source = OSPTI.CanonicalShiftState
  ; ΔState = ⊤
  ; ΔSource = ⊤
  ; Eigen = ⊤
  ; projection = canonicalExecutionProjection
  ; sourceStep = λ x → x
  ; ArrowOK = λ _ _ → ⊤
  ; ConeOK = λ _ → ⊤
  ; mdl = λ _ → zero
  ; basin = canonicalExecutionBasin
  ; eigenOf = λ _ → tt
  ; eigenOverlap = λ _ _ → zero
  ; overlapFloor = zero
  }

canonicalExecutionReceipt :
  ECL.ExecutionContractReceipt
    canonicalExecutionContract
    OSPTI.canonicalShift
    OSPTI.canonicalShift
canonicalExecutionReceipt = record
  { arrowOK = tt
  ; coneOK = tt
  ; mdlOK = z≤n
  ; basinOK = tt , tt
  ; eigenOK = z≤n
  }

canonicalReceiptPair :
  DQ.DeltaPair
canonicalReceiptPair = zero , zero

canonicalPairSupportObservableSignatureReceipt :
  RFOS.PairSupportObservableSignatureExecutionReceipt
    canonicalExecutionContract
    OSPTI.canonicalShift
    OSPTI.canonicalShift
    OSPTI.canonicalObservableSignaturePressureTest
    OSPTI.canonicalShift
    canonicalReceiptPair
canonicalPairSupportObservableSignatureReceipt =
  RFOS.receiptFromObservableSignatureWithPairSupport
    canonicalExecutionReceipt
    OSPTI.canonicalPromotionReadyPoint
    canonicalReceiptPair
