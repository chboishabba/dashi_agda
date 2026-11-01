module DASHI.Geometry.RealIsotropy.Instance.Shift where

-- Shim: use the tail-inversion isotropy instance (commutes with C/P/R).
open import Agda.Builtin.Nat using (Nat; _+_)
open import DASHI.Geometry.RealIsotropy.Core as RIS
open import DASHI.Metric.FineAgreementUltrametric as FAM
open import DASHI.Physics.RealOperatorStackShift as ROSS
open import DASHI.Geometry.RealIsotropy.Instance.ShiftTailInv as TailInv

realIsotropyInstanceShift :
  ∀ {m k : Nat} →
  RIS.RealIsotropy (FAM.ultrametricVec {n = m + k})
    (λ x → ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} x)))
realIsotropyInstanceShift {m} {k} =
  TailInv.realIsotropyInstanceTailInv {m} {k}
