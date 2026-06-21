module DASHI.Physics.Closure.SSPPrimeLane369FieldPhaseBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Core.SuperSSP369Field using
  ( SuperSSP369Field
  ; rootField
  ; depth3Field
  ; focusPrimeLane
  ; focusBodySurface
  ; focusResidueSurface
  )
open import DASHI.Foundations.SSPBase369Bridge using
  ( SSPBase369BridgeReceipt
  ; mkSSPBase369BridgeReceipt
  ; surfaceTriTruth
  ; surfaceHexTruth
  ; surfaceNonaryTruth
  )
open import DASHI.Foundations.FifteenSSPSurface using
  ( FifteenSSPSurface
  ; canonicalZeroFifteenSSPSurface
  ; canonicalExampleFifteenSSPSurface
  ; canonicalNegativeFifteenSSPSurface
  )
open import DASHI.Physics.Closure.SSPPrimeLane369PhaseBridge using
  ( SSPPrimeLane369PhaseBridge
  ; primeIdentity
  ; primeLane369PhaseBridge
  )
open import MonsterOntos using (SSP; p3; p7)

------------------------------------------------------------------------
-- Field-level 3/6/9 phase bridge.
--
-- The record keeps the focused field explicit and exposes:
--   * a typed phase bridge for the focused prime lane,
--   * Base369 readouts for the focused body and residue surfaces,
--   * exact equalities tying the receipts back to the source field.

surfaceBridgeReceipt : FifteenSSPSurface → SSPBase369BridgeReceipt
surfaceBridgeReceipt s =
  mkSSPBase369BridgeReceipt
    s
    (surfaceTriTruth s)
    (surfaceHexTruth s)
    (surfaceNonaryTruth s)
    refl
    refl
    refl

record SSPPrimeLane369FieldPhaseBridge (d : Nat) : Set where
  constructor mkSSPPrimeLane369FieldPhaseBridge
  field
    sourceField : SuperSSP369Field d
    focusedPrimePhaseBridge : SSPPrimeLane369PhaseBridge
    bodySurfaceBridge : SSPBase369BridgeReceipt
    residueSurfaceBridge : SSPBase369BridgeReceipt
    focusedPrimeBridgeMatches :
      primeIdentity focusedPrimePhaseBridge ≡ focusPrimeLane sourceField
    bodySurfaceBridgeMatches :
      SSPBase369BridgeReceipt.sourceSurface bodySurfaceBridge
      ≡ focusBodySurface sourceField
    residueSurfaceBridgeMatches :
      SSPBase369BridgeReceipt.sourceSurface residueSurfaceBridge
      ≡ focusResidueSurface sourceField
    bodySurfaceBridgeIsCanonical :
      bodySurfaceBridge ≡ surfaceBridgeReceipt (focusBodySurface sourceField)
    residueSurfaceBridgeIsCanonical :
      residueSurfaceBridge
      ≡ surfaceBridgeReceipt (focusResidueSurface sourceField)

open SSPPrimeLane369FieldPhaseBridge public

fieldPhaseBridge :
  ∀ {d : Nat} →
  SuperSSP369Field d →
  SSPPrimeLane369FieldPhaseBridge d
fieldPhaseBridge source = record
  { sourceField = source
  ; focusedPrimePhaseBridge = primeLane369PhaseBridge (focusPrimeLane source)
  ; bodySurfaceBridge = surfaceBridgeReceipt (focusBodySurface source)
  ; residueSurfaceBridge = surfaceBridgeReceipt (focusResidueSurface source)
  ; focusedPrimeBridgeMatches = refl
  ; bodySurfaceBridgeMatches = refl
  ; residueSurfaceBridgeMatches = refl
  ; bodySurfaceBridgeIsCanonical = refl
  ; residueSurfaceBridgeIsCanonical = refl
  }

canonicalRootFieldPhaseBridge :
  SSPPrimeLane369FieldPhaseBridge zero
canonicalRootFieldPhaseBridge = fieldPhaseBridge rootField

canonicalDepth3FieldPhaseBridge :
  SSPPrimeLane369FieldPhaseBridge (suc (suc (suc zero)))
canonicalDepth3FieldPhaseBridge = fieldPhaseBridge depth3Field

canonicalRootFieldFocusedPrimeIsP3 :
  primeIdentity (focusedPrimePhaseBridge canonicalRootFieldPhaseBridge) ≡ p3
canonicalRootFieldFocusedPrimeIsP3 = refl

canonicalDepth3FieldFocusedPrimeIsP7 :
  primeIdentity (focusedPrimePhaseBridge canonicalDepth3FieldPhaseBridge) ≡ p7
canonicalDepth3FieldFocusedPrimeIsP7 = refl

canonicalRootFieldBodySurfaceIsCanonicalZero :
  SSPBase369BridgeReceipt.sourceSurface
    (bodySurfaceBridge canonicalRootFieldPhaseBridge)
  ≡ canonicalZeroFifteenSSPSurface
canonicalRootFieldBodySurfaceIsCanonicalZero = refl

canonicalRootFieldResidueSurfaceIsCanonicalExample :
  SSPBase369BridgeReceipt.sourceSurface
    (residueSurfaceBridge canonicalRootFieldPhaseBridge)
  ≡ canonicalExampleFifteenSSPSurface
canonicalRootFieldResidueSurfaceIsCanonicalExample = refl

canonicalDepth3FieldBodySurfaceIsCanonicalExample :
  SSPBase369BridgeReceipt.sourceSurface
    (bodySurfaceBridge canonicalDepth3FieldPhaseBridge)
  ≡ canonicalExampleFifteenSSPSurface
canonicalDepth3FieldBodySurfaceIsCanonicalExample = refl

canonicalDepth3FieldResidueSurfaceIsCanonicalNegative :
  SSPBase369BridgeReceipt.sourceSurface
    (residueSurfaceBridge canonicalDepth3FieldPhaseBridge)
  ≡ canonicalNegativeFifteenSSPSurface
canonicalDepth3FieldResidueSurfaceIsCanonicalNegative = refl

canonicalRootFieldBodyReceiptIsCanonical :
  bodySurfaceBridge canonicalRootFieldPhaseBridge
  ≡ surfaceBridgeReceipt (focusBodySurface rootField)
canonicalRootFieldBodyReceiptIsCanonical = refl

canonicalRootFieldResidueReceiptIsCanonical :
  residueSurfaceBridge canonicalRootFieldPhaseBridge
  ≡ surfaceBridgeReceipt (focusResidueSurface rootField)
canonicalRootFieldResidueReceiptIsCanonical = refl

canonicalDepth3FieldBodyReceiptIsCanonical :
  bodySurfaceBridge canonicalDepth3FieldPhaseBridge
  ≡ surfaceBridgeReceipt (focusBodySurface depth3Field)
canonicalDepth3FieldBodyReceiptIsCanonical = refl

canonicalDepth3FieldResidueReceiptIsCanonical :
  residueSurfaceBridge canonicalDepth3FieldPhaseBridge
  ≡ surfaceBridgeReceipt (focusResidueSurface depth3Field)
canonicalDepth3FieldResidueReceiptIsCanonical = refl

canonicalRootFieldBodyReceipt :
  SSPBase369BridgeReceipt
canonicalRootFieldBodyReceipt = bodySurfaceBridge canonicalRootFieldPhaseBridge

canonicalRootFieldResidueReceipt :
  SSPBase369BridgeReceipt
canonicalRootFieldResidueReceipt = residueSurfaceBridge canonicalRootFieldPhaseBridge

canonicalDepth3FieldBodyReceipt :
  SSPBase369BridgeReceipt
canonicalDepth3FieldBodyReceipt = bodySurfaceBridge canonicalDepth3FieldPhaseBridge

canonicalDepth3FieldResidueReceipt :
  SSPBase369BridgeReceipt
canonicalDepth3FieldResidueReceipt = residueSurfaceBridge canonicalDepth3FieldPhaseBridge
