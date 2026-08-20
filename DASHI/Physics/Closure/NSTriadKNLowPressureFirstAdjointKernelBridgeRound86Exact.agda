module DASHI.Physics.Closure.NSTriadKNLowPressureFirstAdjointKernelBridgeRound86Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Ronald Coifman; Yves Meyer.
-- Title: "Au dela des operateurs pseudo-differentiels".
-- Asterisque 57 (1978).
-- Classical Coifman--Meyer multiplier provenance; no DOI is attached here.
--
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- ROUND86 / EXACT C4b REDUCTION
--
-- The repository already proves the three unit-weight output/partial-adjoint
-- Schur conditions and the positive factorized shell-kernel estimate
--
--   sum_{j<=J,d<=D} (1/4)^j (1/32)^d <= 128/93.
--
-- Coifman--Meyer explains why an order-zero bilinear multiplier should be
-- controlled once the symbol derivatives are uniform, but the literal DASHI
-- route is sharper: Grafakos--Torres/Bony machinery is already formalized at
-- the shell level.  Therefore the only missing C4b analytic producer is the
-- pointwise physical power comparison
--
--   |literal low-pressure first-adjoint coefficient(j,d)|^2
--      <= (1/4)^j (1/32)^d.
--
-- This module proves that THAT ONE inequality, if established on the literal
-- coefficient, immediately yields a cutoff-uniform first-adjoint mass bound.
-- No additional summability theorem is required.  Note the exact rectangle
-- constant is 128/93 (approximately 1.376), not 93/128.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Majorant
import DASHI.Physics.Closure.NSTriadKNOutputRelocationUnitWeightShellSchur as ShellSchur
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

record LiteralLowPressureFirstAdjointKernelBridge : Set where
  constructor low-pressure-kernel-bridge
  field
    coefficientSquared : Nat → Nat → ℚ
    coefficientSquaredNonnegative :
      ∀ lowShell gap → 0ℚ ≤ coefficientSquared lowShell gap
    coefficientDominatedByCanonicalKernel :
      ∀ lowShell gap →
        coefficientSquared lowShell gap
        ≤ Majorant.canonicalKernel lowShell gap

open LiteralLowPressureFirstAdjointKernelBridge public

coefficientRowSum :
  LiteralLowPressureFirstAdjointKernelBridge → Nat → Nat → ℚ
coefficientRowSum bridge lowShell gapCutoff =
  Majorant.sumTo (coefficientSquared bridge lowShell) gapCutoff

coefficientRectangleSum :
  LiteralLowPressureFirstAdjointKernelBridge → Nat → Nat → ℚ
coefficientRectangleSum bridge lowCutoff gapCutoff =
  Majorant.sumTo
    (λ lowShell → coefficientRowSum bridge lowShell gapCutoff)
    lowCutoff

coefficientRowDominatedByCanonical :
  ∀ bridge lowShell gapCutoff →
  coefficientRowSum bridge lowShell gapCutoff
  ≤ Majorant.rowSum Majorant.canonicalKernel lowShell gapCutoff
coefficientRowDominatedByCanonical bridge lowShell gapCutoff =
  Majorant.sumToMonotone
    (coefficientSquared bridge lowShell)
    (Majorant.canonicalKernel lowShell)
    gapCutoff
    (coefficientDominatedByCanonicalKernel bridge lowShell)

coefficientRectangleDominatedByCanonical :
  ∀ bridge lowCutoff gapCutoff →
  coefficientRectangleSum bridge lowCutoff gapCutoff
  ≤ Majorant.rectangleSum Majorant.canonicalKernel lowCutoff gapCutoff
coefficientRectangleDominatedByCanonical bridge lowCutoff gapCutoff =
  Majorant.sumToMonotone
    (λ lowShell → coefficientRowSum bridge lowShell gapCutoff)
    (λ lowShell →
      Majorant.rowSum Majorant.canonicalKernel lowShell gapCutoff)
    lowCutoff
    (λ lowShell →
      coefficientRowDominatedByCanonical bridge lowShell gapCutoff)

literalLowPressureFirstAdjointCutoffUniformBound :
  ∀ bridge lowCutoff gapCutoff →
  coefficientRectangleSum bridge lowCutoff gapCutoff
  ≤ Geo.oneTwentyEightNinetyThirds
literalLowPressureFirstAdjointCutoffUniformBound bridge lowCutoff gapCutoff =
  ℚP.≤-trans
    (coefficientRectangleDominatedByCanonical bridge lowCutoff gapCutoff)
    (Majorant.canonicalKernelCutoffUniformBound lowCutoff gapCutoff)

firstAdjointShellSchurAlreadyClosed : ∀ lowCutoff gapCutoff →
  ShellSchur.orientationCutoffSum
    ShellSchur.firstAdjointCondition lowCutoff gapCutoff
  ≤ Geo.oneTwentyEightNinetyThirds
firstAdjointShellSchurAlreadyClosed =
  ShellSchur.firstAdjointUnitWeightShellSchurBound

round86LowPressureFirstAdjointSummabilityNeedsNoNewTheorem : Bool
round86LowPressureFirstAdjointSummabilityNeedsNoNewTheorem = true

round86LiteralLowPressureCoefficientPowerComparisonConstructed : Bool
round86LiteralLowPressureCoefficientPowerComparisonConstructed = false

round86C4bReducedToLiteralCoefficientKernelDomination : Bool
round86C4bReducedToLiteralCoefficientKernelDomination = true

round86LowPressureFirstAdjointSummabilityNeedsNoNewTheoremIsTrue :
  round86LowPressureFirstAdjointSummabilityNeedsNoNewTheorem ≡ true
round86LowPressureFirstAdjointSummabilityNeedsNoNewTheoremIsTrue = refl

round86C4bReducedToLiteralCoefficientKernelDominationIsTrue :
  round86C4bReducedToLiteralCoefficientKernelDomination ≡ true
round86C4bReducedToLiteralCoefficientKernelDominationIsTrue = refl
