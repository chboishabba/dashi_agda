module DASHI.Physics.LorentzBridge where

-- Lorentz-like adapter boundary: symmetry data only, no semantics.
--
-- This adapter also exposes the theorem-critical Signature31 seam so that
-- downstream "physics-facing" wrappers can consume the canonical signature
-- without importing the prototype-only module `DASHI.Physics.Signature31`.

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Bridge using (BridgeSurface)

open import DASHI.Geometry.ConeTimeIsotropy as CTI using (Signature)
open import DASHI.Geometry.SignatureUniqueness31 as SU using (Signature31Theorem)
open import DASHI.Physics.Signature31Canonical as S31C

record LorentzAdapter : Set₁ where
  field
    bridge : BridgeSurface

    -- Canonical signature seam (theorem-critical).
    signature31Tag : CTI.Signature
    signature31Theorem : SU.Signature31Theorem


open LorentzAdapter public

-- A more Lorentz-shaped package (still semantics-free): keep the stable base
-- adapter, and add the canonical closure-side bridge witness explicitly.
open import DASHI.Physics.Closure.SpinLocalLorentzBridgeTheorem as SLLB
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI

record LorentzAdapterPlus : Setω where
  field
    base : LorentzAdapter
    spinLocalLorentz : SLLB.SpinLocalLorentzBridge MCCSI.minimumCredibleClosureShift

open LorentzAdapterPlus public

-- Canonical Lorentz adapter surface for the current repo theorem snapshot.
-- Keeps the bridge boundary stable while routing signature claims through the
-- theorem-critical seam.
canonicalLorentzAdapter : BridgeSurface -> LorentzAdapter
canonicalLorentzAdapter b =
  record
    { bridge = b
    ; signature31Tag = S31C.signature31
    ; signature31Theorem = S31C.signature31-theorem
    }

canonicalLorentzAdapterPlus : BridgeSurface -> LorentzAdapterPlus
canonicalLorentzAdapterPlus b =
  record
    { base = canonicalLorentzAdapter b
    ; spinLocalLorentz = SLLB.canonicalSpinLocalLorentzBridge
    }
