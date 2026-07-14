module DASHI.Physics.Closure.NSTriadKNScaledOperatorErrorAudit where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat using (_≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (*-identityʳ; ≤-trans)
open import Relation.Nullary using (¬_)

import DASHI.Physics.Closure.NSTriadKNQGapTransfer as QGap
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
import DASHI.Physics.Closure.NSTriadKNShellScaleHeadroom as ScaleHeadroom
import DASHI.Physics.Closure.NSTriadKNProfileCrossProductAnalyticAudit as CrossAudit
import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition as ProfileKernel

data PrimaryStage3SaturationSource : Set where
  unitShellQuadraticWitness : PrimaryStage3SaturationSource
  canonicalProfileKernelPlaceholder : PrimaryStage3SaturationSource

primaryStage3SaturationSource : PrimaryStage3SaturationSource
primaryStage3SaturationSource = canonicalProfileKernelPlaceholder

canonicalProfileKernelIsConstantInIndices :
  (N i j : Nat) → ProfileKernel.canonicalNSKernel N i j ≡ N
canonicalProfileKernelIsConstantInIndices N i j = refl

canonicalUnitShellProfileKernelValue :
  (i j : Nat) → ProfileKernel.canonicalNSKernel (suc zero) i j ≡ suc zero
canonicalUnitShellProfileKernelValue i j = refl

------------------------------------------------------------------------
-- Constant ledger for the canonical unit-shell scaled-error attempt.
--
-- The existing Stage-3 witness controls qError by one copy of the unit-shell
-- energy.  Successor scaling contributes four copies.  The base form can
-- therefore provide at most A = 4, while the scaled error needs C = 4.
-- This is an arithmetic no-margin result, not a promotion receipt.

record ScaledOperatorErrorLedger : Set where
  constructor mkScaledOperatorErrorLedger
  field
    scaleSq : Nat
    rawErrorConstant : Nat
    scaledErrorConstant : Nat
    maximalBaseConstant : Nat

    scaleSqIsFour : scaleSq ≡ suc (suc (suc (suc zero)))
    rawErrorConstantIsOne : rawErrorConstant ≡ suc zero
    scaledErrorConstantIsFour :
      scaledErrorConstant ≡ suc (suc (suc (suc zero)))
    maximalBaseConstantIsFour :
      maximalBaseConstant ≡ suc (suc (suc (suc zero)))

    strictMarginClosed : Bool
    strictMarginClosedIsFalse : strictMarginClosed ≡ false

open ScaledOperatorErrorLedger public

canonicalScaledOperatorErrorLedger : ScaledOperatorErrorLedger
canonicalScaledOperatorErrorLedger =
  mkScaledOperatorErrorLedger
    (suc (suc (suc (suc zero))))
    (suc zero)
    (suc (suc (suc (suc zero))))
    (suc (suc (suc (suc zero))))
    refl
    refl
    refl
    refl
    false
    refl

canonicalScaledOperatorErrorMarginClosed : Bool
canonicalScaledOperatorErrorMarginClosed =
  strictMarginClosed canonicalScaledOperatorErrorLedger

canonicalScaledOperatorErrorMarginClosedIsFalse :
  canonicalScaledOperatorErrorMarginClosed ≡ false
canonicalScaledOperatorErrorMarginClosedIsFalse =
  strictMarginClosedIsFalse canonicalScaledOperatorErrorLedger

------------------------------------------------------------------------
-- Generic unit-energy obstruction.

notLessOfLe :
  (A C : Nat) → A ≤ C → ¬ (C < A)
notLessOfLe zero C _ ()
notLessOfLe (suc A) zero ()
notLessOfLe (suc A) (suc C) (s≤s A≤C) (s≤s C<A) =
  notLessOfLe A C A≤C C<A

scaledErrorConstantAtUnitForcesFourOrMore :
  (C : Nat) →
  suc (suc (suc (suc zero))) * suc zero
    ≤ C * suc zero →
  suc (suc (suc (suc zero))) ≤ C
scaledErrorConstantAtUnitForcesFourOrMore C proof
  rewrite *-identityʳ (suc (suc (suc (suc zero))))
        | *-identityʳ C = proof

baseConstantAtUnitIsAtMostFour :
  (A : Nat) →
  A * suc zero
    ≤ suc (suc (suc (suc zero))) * suc zero →
  A ≤ suc (suc (suc (suc zero)))
baseConstantAtUnitIsAtMostFour A proof
  rewrite *-identityʳ A
        | *-identityʳ (suc (suc (suc (suc zero)))) = proof

canonicalUnitScaleHasNoStrictMargin :
  (A C : Nat) →
  A * suc zero
    ≤ suc (suc (suc (suc zero))) * suc zero →
  suc (suc (suc (suc zero))) * suc zero
    ≤ C * suc zero →
  ¬ (C < A)
canonicalUnitScaleHasNoStrictMargin A C baseBound errorBound C<A =
  notLessOfLe
    A
    C
    (≤-trans
      (baseConstantAtUnitIsAtMostFour A baseBound)
      (scaledErrorConstantAtUnitForcesFourOrMore C errorBound))
    C<A

------------------------------------------------------------------------
-- The next analytic target: sharpen the actual Stage-3 error below four.

canonicalSharperScaledOperatorErrorBridgeTarget : Set
canonicalSharperScaledOperatorErrorBridgeTarget =
  QGap.sharperScaledOperatorErrorBridgeTarget
    {N = suc zero}
    {Carrier = ResidueNorm.ResidueEnergyCarrier (suc zero)}
    (ScaleHeadroom.mkCompatibilityScale
      (suc (suc (suc (suc zero))))
      (s≤s (s≤s z≤n)))
    (λ x → ResidueNorm.residueEnergy x)
    (λ x → ResidueNorm.residueEnergy x)
    (suc (suc (suc zero)))

canonicalSharperScaledOperatorErrorBridgeClosed : Bool
canonicalSharperScaledOperatorErrorBridgeClosed = false

canonicalSharperScaledOperatorErrorBridgeClosedIsFalse :
  canonicalSharperScaledOperatorErrorBridgeClosed ≡ false
canonicalSharperScaledOperatorErrorBridgeClosedIsFalse = refl

------------------------------------------------------------------------
-- Equality-source audit and strict-defect target.

record Stage3ErrorSourceAudit : Set where
  constructor mkStage3ErrorSourceAudit
  field
    primarySource : PrimaryStage3SaturationSource
    unitShellQuadraticWitnessSaturates : Bool
    unitShellQuadraticWitnessSaturatesIsTrue :
      unitShellQuadraticWitnessSaturates ≡ true
    weakStrongNormModelSaturates : Bool
    weakStrongNormModelSaturatesIsTrue :
      weakStrongNormModelSaturates ≡ true
    crossProductStrictDefectAvailable : Bool
    crossProductStrictDefectAvailableIsFalse :
      crossProductStrictDefectAvailable ≡ false

stage3StrictDefectAvailableFromCrossAudit :
  CrossAudit.ProfileCrossProductAnalyticAudit → Bool
stage3StrictDefectAvailableFromCrossAudit audit =
  CrossAudit.analyticMatrixClosed audit

canonicalStage3ErrorSourceAudit : Stage3ErrorSourceAudit
canonicalStage3ErrorSourceAudit =
  mkStage3ErrorSourceAudit
    canonicalProfileKernelPlaceholder
    true refl
    true refl
    (stage3StrictDefectAvailableFromCrossAudit
      CrossAudit.canonicalProfileCrossProductAnalyticAudit)
    CrossAudit.canonicalProfileCrossProductAnalyticClosedIsFalse

canonicalStage3StrictKernelDefectTarget : Set
canonicalStage3StrictKernelDefectTarget =
  QGap.stage3StrictKernelDefectTarget
    {N = suc zero}
    {Carrier = ResidueNorm.ResidueEnergyCarrier (suc zero)}
    (ScaleHeadroom.mkCompatibilityScale
      (suc (suc (suc (suc zero))))
      (s≤s (s≤s z≤n)))
    (λ x → ResidueNorm.residueEnergy x)
    (λ x → ResidueNorm.residueEnergy x)
    (λ x → ResidueNorm.residueEnergy x)
    (suc zero)

canonicalStage3StrictKernelDefectClosed : Bool
canonicalStage3StrictKernelDefectClosed = false

canonicalStage3StrictKernelDefectClosedIsFalse :
  canonicalStage3StrictKernelDefectClosed ≡ false
canonicalStage3StrictKernelDefectClosedIsFalse = refl
