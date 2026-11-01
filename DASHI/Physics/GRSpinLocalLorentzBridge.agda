module DASHI.Physics.GRSpinLocalLorentzBridge where

-- GR-facing thin wrapper: packages a GR adapter boundary together with the
-- closure-side Spin->LocalLorentz bridge witness. No GR semantics asserted.

open import Agda.Primitive using (Setω)

open import DASHI.Physics.GR using (GRAdapter)
open import DASHI.Physics.Closure.SpinLocalLorentzBridgeTheorem as SLLB
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI

record GRSpinLocalLorentzAdapter : Setω where
  field
    gr : GRAdapter
    spinLocalLorentz : SLLB.SpinLocalLorentzBridge MCCSI.minimumCredibleClosureShift

open GRSpinLocalLorentzAdapter public

canonicalGRSpinLocalLorentzAdapter : GRAdapter -> GRSpinLocalLorentzAdapter
canonicalGRSpinLocalLorentzAdapter A =
  record
    { gr = A
    ; spinLocalLorentz = SLLB.canonicalSpinLocalLorentzBridge
    }
