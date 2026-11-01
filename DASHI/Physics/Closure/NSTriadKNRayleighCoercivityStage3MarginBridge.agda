module DASHI.Physics.Closure.NSTriadKNRayleighCoercivityStage3MarginBridge where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat using (_≤_; _<_)

import DASHI.Physics.Closure.NSAmplitudeWeightedNegativeFrameBoundary as NegativeFrame
import DASHI.Physics.Closure.NSTriadKNCrossShellRayleighMechanismReceipt as RayleighMechanism
import DASHI.Physics.Closure.NSTriadKNGramCoercivityTargetReceipt as GramReceipt
import DASHI.Physics.Closure.NSTriadKNGramRayleighMarginAuditReceipt as RayleighAudit
import DASHI.Physics.Closure.NSTriadKNGramRayleighBaseFormBridge as GramRayleighBridge
import DASHI.Physics.Closure.NSTriadKNShellScaleHeadroom as ScaleHeadroom

------------------------------------------------------------------------
-- The coercive/margin parent should depend on the actual negative-frame and
-- Rayleigh lanes, not float as a free theorem package.

record NegativeFrameRayleighMarginTarget
    (Carrier : Set)
    (shellIndex : Nat)
    (strongNormSquared : Carrier → Nat)
    (baseQuadraticForm : Carrier → Nat)
    (stage3ErrorConstant : Nat)
    : Setω where
  constructor mkNegativeFrameRayleighMarginTarget
  field
    gramReceipt :
      GramReceipt.NSTriadKNGramCoercivityTargetReceipt

    rayleighAuditReceipt :
      RayleighAudit.NSTriadKNGramRayleighMarginAuditReceipt

    rayleighMechanismReceipt :
      RayleighMechanism.NSTriadKNCrossShellRayleighMechanismReceipt

    negativeFrameBoundary :
      NegativeFrame.NSAmplitudeWeightedNegativeFrameBoundary

    gramReceiptRecorded :
      GramReceipt.failClosed gramReceipt ≡ true

    rayleighAuditRecorded :
      RayleighAudit.failClosed rayleighAuditReceipt ≡ true

    rayleighMechanismRecorded :
      RayleighMechanism.failClosed rayleighMechanismReceipt ≡ true

    negativeFrameRecorded :
      NegativeFrame.failClosed negativeFrameBoundary ≡ true

    baseGapConstant : Nat
    baseGapPositive : Set
    compatibilityScale : ScaleHeadroom.CompatibilityScale shellIndex

    rayleighBaseCoercive :
      (x : Carrier) →
      baseGapConstant * strongNormSquared x
        ≤
        ScaleHeadroom.CompatibilityScale.scaleSq compatibilityScale
          * baseQuadraticForm x

    stage3ErrorBelowBaseGap :
      stage3ErrorConstant < baseGapConstant

open NegativeFrameRayleighMarginTarget public

record NegativeFrameRayleighMarginCore
    (Carrier : Set)
    (shellIndex : Nat)
    (strongNormSquared : Carrier → Nat)
    (baseQuadraticForm : Carrier → Nat)
    (stage3ErrorConstant : Nat)
    : Setω where
  constructor mkNegativeFrameRayleighMarginCore
  field
    baseGapConstant : Nat
    baseGapPositive : Set
    compatibilityScale : ScaleHeadroom.CompatibilityScale shellIndex

    rayleighBaseCoercive :
      (x : Carrier) →
      baseGapConstant * strongNormSquared x
        ≤
        ScaleHeadroom.CompatibilityScale.scaleSq compatibilityScale
          * baseQuadraticForm x

    stage3ErrorBelowBaseGap :
      stage3ErrorConstant < baseGapConstant

open NegativeFrameRayleighMarginCore public

toNegativeFrameRayleighMarginTarget :
  {Carrier : Set} →
  {shellIndex : Nat} →
  {strongNormSquared : Carrier → Nat} →
  {baseQuadraticForm : Carrier → Nat} →
  {stage3ErrorConstant : Nat} →
  NegativeFrameRayleighMarginCore
    Carrier
    shellIndex
    strongNormSquared
    baseQuadraticForm
    stage3ErrorConstant →
  NegativeFrameRayleighMarginTarget
    Carrier
    shellIndex
    strongNormSquared
    baseQuadraticForm
    stage3ErrorConstant
toNegativeFrameRayleighMarginTarget core =
  mkNegativeFrameRayleighMarginTarget
    GramReceipt.canonicalNSTriadKNGramCoercivityTargetReceipt
    RayleighAudit.canonicalNSTriadKNGramRayleighMarginAuditReceipt
    RayleighMechanism.canonicalNSTriadKNCrossShellRayleighMechanismReceipt
    NegativeFrame.canonicalNSAmplitudeWeightedNegativeFrameBoundary
    refl
    refl
    refl
    refl
    (NegativeFrameRayleighMarginCore.baseGapConstant core)
    (NegativeFrameRayleighMarginCore.baseGapPositive core)
    (NegativeFrameRayleighMarginCore.compatibilityScale core)
    (NegativeFrameRayleighMarginCore.rayleighBaseCoercive core)
    (NegativeFrameRayleighMarginCore.stage3ErrorBelowBaseGap core)

toRayleighCoercivityBeatsStage3Error :
  {Carrier : Set} →
  {shellIndex : Nat} →
  {strongNormSquared : Carrier → Nat} →
  {baseQuadraticForm : Carrier → Nat} →
  {stage3ErrorConstant : Nat} →
  NegativeFrameRayleighMarginTarget
    Carrier
    shellIndex
    strongNormSquared
    baseQuadraticForm
    stage3ErrorConstant →
  GramRayleighBridge.RayleighCoercivityBeatsStage3Error
    Carrier
    shellIndex
    strongNormSquared
    baseQuadraticForm
    stage3ErrorConstant
toRayleighCoercivityBeatsStage3Error target =
  GramRayleighBridge.mkRayleighCoercivityBeatsStage3Error
    (NegativeFrameRayleighMarginTarget.rayleighAuditReceipt target)
    (NegativeFrameRayleighMarginTarget.rayleighMechanismReceipt target)
    (NegativeFrameRayleighMarginTarget.rayleighAuditRecorded target)
    (NegativeFrameRayleighMarginTarget.rayleighMechanismRecorded target)
    (NegativeFrameRayleighMarginTarget.baseGapConstant target)
    (NegativeFrameRayleighMarginTarget.baseGapPositive target)
    (NegativeFrameRayleighMarginTarget.compatibilityScale target)
    (NegativeFrameRayleighMarginTarget.rayleighBaseCoercive target)
    (NegativeFrameRayleighMarginTarget.stage3ErrorBelowBaseGap target)
