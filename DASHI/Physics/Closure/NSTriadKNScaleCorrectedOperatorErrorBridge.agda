module DASHI.Physics.Closure.NSTriadKNScaleCorrectedOperatorErrorBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat using (_≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; *-identityʳ)
open import Relation.Nullary using (¬_)

import DASHI.Physics.Closure.NSTriadKNQGapTransfer as QGap
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
import DASHI.Physics.Closure.NSTriadKNShellScaleHeadroom as ScaleHeadroom
import DASHI.Physics.Closure.NSTriadKNScaledOperatorErrorAudit as Audit

------------------------------------------------------------------------
-- Scale-corrected unit-shell operator-error bridge.
--
-- The raw weak-to-strong composition is an N^-2 statement at shell N = 1.
-- It must not be re-used by substituting scaleSq = 4 for N: doing that changes
-- N * (N * qError) into 4 * (4 * qError), i.e. sixteen copies of qError.
--
-- The canonical q-gap target instead asks for one explicit compatibility-scale
-- multiplier:
--
--   scaleSq * qError <= C_err * strongNormSquared.
--
-- At the current model witness qError = strongNormSquared = residueEnergy and
-- scaleSq = 4, so the exact corrected constant is C_err = 4.
------------------------------------------------------------------------

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

four : Nat
four = suc three

Carrier : Set
Carrier = ResidueNorm.ResidueEnergyCarrier one

residueEnergy : Carrier → Nat
residueEnergy = ResidueNorm.residueEnergy

canonicalCompatibilityScale : ScaleHeadroom.CompatibilityScale one
canonicalCompatibilityScale =
  ScaleHeadroom.mkCompatibilityScale four (s≤s (s≤s z≤n))

canonicalScaleSqIsFour :
  ScaleHeadroom.CompatibilityScale.scaleSq canonicalCompatibilityScale ≡ four
canonicalScaleSqIsFour = refl

canonicalScaledOperatorErrorTarget : Set
canonicalScaledOperatorErrorTarget =
  QGap.scaledOperatorErrorBridgeTarget
    canonicalCompatibilityScale
    residueEnergy
    residueEnergy
    four

canonicalScaledOperatorErrorProof : canonicalScaledOperatorErrorTarget
canonicalScaledOperatorErrorProof x = ≤-refl

canonicalScaledOperatorErrorBridge :
  QGap.ScaledOperatorErrorBridge one Carrier
canonicalScaledOperatorErrorBridge =
  QGap.mkScaledOperatorErrorBridge
    canonicalCompatibilityScale
    residueEnergy
    residueEnergy
    four
    canonicalScaledOperatorErrorProof

canonicalScaledOperatorErrorBridgeClosed : Bool
canonicalScaledOperatorErrorBridgeClosed = true

canonicalScaledOperatorErrorBridgeClosedIsTrue :
  canonicalScaledOperatorErrorBridgeClosed ≡ true
canonicalScaledOperatorErrorBridgeClosedIsTrue = refl

------------------------------------------------------------------------
-- Exact lower bound on the corrected error constant at unit energy.
------------------------------------------------------------------------

scaledErrorConstantAtUnitForcesFourOrMore :
  (C : Nat) →
  four * one ≤ C * one →
  four ≤ C
scaledErrorConstantAtUnitForcesFourOrMore C proof
  rewrite *-identityʳ four
        | *-identityʳ C = proof

canonicalCorrectedErrorConstantIsSharp :
  four * one ≤ four * one
canonicalCorrectedErrorConstantIsSharp = ≤-refl

------------------------------------------------------------------------
-- No-go for the requested strict compatibility closure on the current model.
--
-- The same unit-energy state forces the base constant A <= 4 and the corrected
-- error constant C_err >= 4. Hence C_err < A is impossible.  The scale adapter
-- is now constructive, but it cannot honestly turn compatibilityRouteClosed on.
------------------------------------------------------------------------

canonicalCurrentModelHasNoStrictGap :
  (A C : Nat) →
  A * one ≤ four * one →
  four * one ≤ C * one →
  ¬ (C < A)
canonicalCurrentModelHasNoStrictGap =
  Audit.canonicalUnitScaleHasNoStrictMargin

canonicalCompatibilityRouteClosed : Bool
canonicalCompatibilityRouteClosed = false

canonicalCompatibilityRouteClosedIsFalse :
  canonicalCompatibilityRouteClosed ≡ false
canonicalCompatibilityRouteClosedIsFalse = refl

------------------------------------------------------------------------
-- The next honest theorem cannot be more scale bookkeeping.  It must provide
-- strict analytic slack, for example a Stage-3 estimate with C_err < 4 or a
-- positive defect separating qBase from qError on every non-zero state.
------------------------------------------------------------------------

canonicalSharperScaledOperatorErrorTarget : Set
canonicalSharperScaledOperatorErrorTarget =
  QGap.sharperScaledOperatorErrorBridgeTarget
    canonicalCompatibilityScale
    residueEnergy
    residueEnergy
    three

canonicalSharperScaledOperatorErrorClosed : Bool
canonicalSharperScaledOperatorErrorClosed = false

canonicalSharperScaledOperatorErrorClosedIsFalse :
  canonicalSharperScaledOperatorErrorClosed ≡ false
canonicalSharperScaledOperatorErrorClosedIsFalse = refl
