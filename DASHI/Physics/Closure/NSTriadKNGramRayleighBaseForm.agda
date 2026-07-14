module DASHI.Physics.Closure.NSTriadKNGramRayleighBaseForm where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat using (_≤_; _<_)

import DASHI.Physics.Closure.NSTriadKNGramCoercivityTargetReceipt as GramReceipt
import DASHI.Physics.Closure.NSTriadKNGramRayleighMarginAuditReceipt as RayleighReceipt
import DASHI.Physics.Closure.NSTriadKNShellScaleHeadroom as ScaleHeadroom

------------------------------------------------------------------------
-- Shared Gram-Rayleigh parent for the NS base-gap lane.
--
-- This packages the actual base quadratic form together with the Rayleigh-side
-- coercive lower bound that should feed Blocker 2C.  It keeps the two live
-- analytic sources visible:
--   * the amplitude-weighted Gram coercivity target;
--   * the Rayleigh-margin audit identifying the dangerous margin mechanism.

record GramRayleighBaseFormTarget
    (Carrier : Set)
    (shellIndex : Nat)
    (strongNormSquared : Carrier → Nat)
    (stage3ErrorConstant : Nat)
    : Setω where
  constructor mkGramRayleighBaseFormTarget
  field
    gramReceipt :
      GramReceipt.NSTriadKNGramCoercivityTargetReceipt

    rayleighReceipt :
      RayleighReceipt.NSTriadKNGramRayleighMarginAuditReceipt

    gramReceiptRecorded :
      GramReceipt.failClosed gramReceipt ≡ true

    rayleighReceiptRecorded :
      RayleighReceipt.failClosed rayleighReceipt ≡ true

    baseQuadraticForm :
      Carrier → Nat

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

open GramRayleighBaseFormTarget public
