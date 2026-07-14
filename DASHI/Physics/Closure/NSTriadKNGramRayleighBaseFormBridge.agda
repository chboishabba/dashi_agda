module DASHI.Physics.Closure.NSTriadKNGramRayleighBaseFormBridge where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat using (_≤_; _<_)

import DASHI.Physics.Closure.NSTriadKNGramCoercivityTargetReceipt as GramReceipt
import DASHI.Physics.Closure.NSTriadKNGramRayleighMarginAuditReceipt as RayleighAudit
import DASHI.Physics.Closure.NSTriadKNCrossShellRayleighMechanismReceipt as RayleighMechanism
import DASHI.Physics.Closure.NSTriadKNGramRayleighBaseForm as GramBaseForm
import DASHI.Physics.Closure.NSTriadKNShellScaleHeadroom as ScaleHeadroom

------------------------------------------------------------------------
-- The last hard Blocker 2 parent should not remain a single opaque postulate.
-- Split it into:
--   1. exact base-form identification for the live Gram object;
--   2. Rayleigh coercivity on that same form, with strict margin over the
--      Stage 3 error constant.

record ExactGramBaseFormIdentification
    (Carrier : Set)
    : Setω where
  constructor mkExactGramBaseFormIdentification
  field
    gramReceipt :
      GramReceipt.NSTriadKNGramCoercivityTargetReceipt

    gramReceiptRecorded :
      GramReceipt.failClosed gramReceipt ≡ true

    baseQuadraticForm :
      Carrier → Nat

open ExactGramBaseFormIdentification public

record RayleighCoercivityBeatsStage3Error
    (Carrier : Set)
    (shellIndex : Nat)
    (strongNormSquared : Carrier → Nat)
    (baseQuadraticForm : Carrier → Nat)
    (stage3ErrorConstant : Nat)
    : Setω where
  constructor mkRayleighCoercivityBeatsStage3Error
  field
    rayleighAuditReceipt :
      RayleighAudit.NSTriadKNGramRayleighMarginAuditReceipt

    rayleighMechanismReceipt :
      RayleighMechanism.NSTriadKNCrossShellRayleighMechanismReceipt

    rayleighAuditRecorded :
      RayleighAudit.failClosed rayleighAuditReceipt ≡ true

    rayleighMechanismRecorded :
      RayleighMechanism.failClosed rayleighMechanismReceipt ≡ true

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

open RayleighCoercivityBeatsStage3Error public

toGramRayleighBaseFormTarget :
  {Carrier : Set} →
  {shellIndex : Nat} →
  {strongNormSquared : Carrier → Nat} →
  {stage3ErrorConstant : Nat} →
  (identification : ExactGramBaseFormIdentification Carrier) →
  RayleighCoercivityBeatsStage3Error
    Carrier
    shellIndex
    strongNormSquared
    (ExactGramBaseFormIdentification.baseQuadraticForm identification)
    stage3ErrorConstant →
  GramBaseForm.GramRayleighBaseFormTarget
    Carrier
    shellIndex
    strongNormSquared
    stage3ErrorConstant
toGramRayleighBaseFormTarget
  {Carrier} {shellIndex} {strongNormSquared} {stage3ErrorConstant}
  identification coercivity =
  GramBaseForm.mkGramRayleighBaseFormTarget
    (ExactGramBaseFormIdentification.gramReceipt identification)
    (RayleighCoercivityBeatsStage3Error.rayleighAuditReceipt coercivity)
    (ExactGramBaseFormIdentification.gramReceiptRecorded identification)
    (RayleighCoercivityBeatsStage3Error.rayleighAuditRecorded coercivity)
    (ExactGramBaseFormIdentification.baseQuadraticForm identification)
    (RayleighCoercivityBeatsStage3Error.baseGapConstant coercivity)
    (RayleighCoercivityBeatsStage3Error.baseGapPositive coercivity)
    (RayleighCoercivityBeatsStage3Error.compatibilityScale coercivity)
    (RayleighCoercivityBeatsStage3Error.rayleighBaseCoercive coercivity)
    (RayleighCoercivityBeatsStage3Error.stage3ErrorBelowBaseGap coercivity)
