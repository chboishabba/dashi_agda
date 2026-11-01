module DASHI.Physics.Closure.DefectCollapseShiftInstance where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat using (_≤_)

open import DASHI.Geometry.DefectCollapse as DC
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI

-- Defect = tail; energy = countNZ on tail; T = Tᵣ
defectCollapseShift :
  ∀ {m k : Nat} →
  DC.DefectCollapse (RTC.Carrier (m + k)) Nat
defectCollapseShift {m} {k} =
  record
    { D = λ x → x
    ; T = TCP.Tᵣ {m} {k}
    ; _≤_ = Data.Nat._≤_
    ; energy = λ x → MSI.countNZ (TCP.tailOf m k x)
    ; collapse = MSI.resid-drop-lemma {m} {k}
    }
