module DASHI.Physics.Closure.NSTriadKNHHGoodParabolicPeriodizedOwnerRound42Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 42 repairs the false pointwise `W <= E0 X D` shortcut by using the
-- actual parabolic shell window:
--
--   lambda_q^2 * |I_q| <= c,
--
-- so the kinetic-to-vorticity lambda_q^2 loss is cancelled after time
-- localization.  The companion amplitude module proves
--
--   localizedMass <= c E0 X D.
--
-- This file closes the finite owner algebra by identifying that localized
-- mass with the *same* `weightedLocalMass` consumed by the periodized annular
-- strain-kernel Cauchy theorem.  Once this one equality and the already typed
-- parabolic recovery are supplied, the existing Round-41 Young constructor
-- returns the literal HH-good owner with effective quadratic factor `c E0`.
--
-- The Round-41 Young input also requires nonnegativity of the physical
-- critical and dissipation resources.  Those are kept as explicit fields;
-- they are not inferred circularly from the quartic inequality.
--
-- Thus the remaining physical HH-good seam is exactly:
--
--   (1) periodized annular strain-kernel/sample identification;
--   (2) actual terminal-window cells with total mass <= c lambda_q^-2;
--   (3) kinetic-to-vorticity lambda_q^2 bound on the selected amplitude leg;
--   (4) quartic envelope <= X D;
--   (5) same-object equality between the localized time mass and the shell
--       `weightedLocalMass` after PV/residual/shell/threshold ordering.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHGoodFiniteKernelCauchyRound40Exact as Good
import DASHI.Physics.Closure.NSTriadKNHHGoodPeriodizedKernelUniformRound40Exact as Periodized
import DASHI.Physics.Closure.NSTriadKNHHGoodSquaredYoungOwnerRound41Exact as Young
import DASHI.Physics.Closure.NSTriadKNHHGoodParabolicAmplitudeAllocationRound42Exact as Parabolic

record PeriodizedParabolicHHGoodInput
    {st : Level}
    {TorusPoint : Set st}
    (environment : Owner.TaxEnvironment)
    (kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint)
    (shell : Nat)
    (parameter : Threshold.PositiveThreshold)
    (samples : List (Good.HHGoodKernelSample parameter)) : Set (lsuc st) where
  field
    kernelIdentification :
      Periodized.PhysicalStrainShellKernelMassIdentification
        kernelTheorem shell parameter samples

    dataEnergy windowConstant quarticEnvelope : ℚ

    parabolicCriticalRecovery :
      Parabolic.ParabolicHHGoodCriticalRecovery
        environment shell dataEnergy windowConstant quarticEnvelope

    weightedLocalMassIsLocalizedParabolicMass :
      Good.weightedLocalMass samples
      ≡ Parabolic.localizedAmplitudeQuarticMass
          (Parabolic.cells
            (Parabolic.recovery parabolicCriticalRecovery))

    criticalNonnegative : 0ℚ ≤ Owner.integralCritical environment
    dissipationNonnegative : 0ℚ ≤ Owner.dissipation environment
    viscositySplit : Threshold.PositiveThreshold

open PeriodizedParabolicHHGoodInput public

effectiveParabolicDataFactor :
  ∀ {st : Level} {TorusPoint : Set st}
    {environment : Owner.TaxEnvironment}
    {kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell : Nat}
    {parameter : Threshold.PositiveThreshold}
    {samples : List (Good.HHGoodKernelSample parameter)} →
  PeriodizedParabolicHHGoodInput
    environment kernelTheorem shell parameter samples → ℚ
effectiveParabolicDataFactor input =
  windowConstant input * dataEnergy input

effectiveParabolicDataFactorNonnegative :
  ∀ {st : Level} {TorusPoint : Set st}
    {environment : Owner.TaxEnvironment}
    {kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell : Nat}
    {parameter : Threshold.PositiveThreshold}
    {samples : List (Good.HHGoodKernelSample parameter)}
    (input : PeriodizedParabolicHHGoodInput
      environment kernelTheorem shell parameter samples) →
  0ℚ ≤ effectiveParabolicDataFactor input
effectiveParabolicDataFactorNonnegative input =
  let
    recovery = Parabolic.recovery (parabolicCriticalRecovery input)
    windowNN = Parabolic.windowConstantNonnegative recovery
    energyNN = Parabolic.dataEnergyNonnegative recovery
    instance
      windowNNI = nonNegative windowNN
      energyNNI = nonNegative energyNN
      productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
        (windowConstant input) (dataEnergy input)
  in
  ℚP.nonNegative⁻¹ (effectiveParabolicDataFactor input)

weightedLocalMassBelowParabolicCriticalDissipation :
  ∀ {st : Level} {TorusPoint : Set st}
    {environment : Owner.TaxEnvironment}
    {kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell : Nat}
    {parameter : Threshold.PositiveThreshold}
    {samples : List (Good.HHGoodKernelSample parameter)}
    (input : PeriodizedParabolicHHGoodInput
      environment kernelTheorem shell parameter samples) →
  Good.weightedLocalMass samples
  ≤ effectiveParabolicDataFactor input
      * Owner.integralCritical environment
      * Owner.dissipation environment
weightedLocalMassBelowParabolicCriticalDissipation input =
  let
    physical =
      Parabolic.localizedHHGoodMassBelowParabolicKineticCriticalDissipation
        (parabolicCriticalRecovery input)
  in
  subst
    (λ lower →
      lower
      ≤ effectiveParabolicDataFactor input
          * Owner.integralCritical _
          * Owner.dissipation _)
    (sym (weightedLocalMassIsLocalizedParabolicMass input))
    physical

periodizedHHGoodOwnerFromParabolicKineticRecovery :
  ∀ {st : Level} {TorusPoint : Set st}
    {environment : Owner.TaxEnvironment}
    {kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell : Nat}
    {parameter : Threshold.PositiveThreshold}
    {samples : List (Good.HHGoodKernelSample parameter)} →
  PeriodizedParabolicHHGoodInput
    environment kernelTheorem shell parameter samples →
  Owner.AdmissibleOwnerEstimate environment
periodizedHHGoodOwnerFromParabolicKineticRecovery input =
  Young.periodizedHHGoodOwnerFromDataEnergyFactorization record
    { identification = kernelIdentification input
    ; dataEnergyFactor = effectiveParabolicDataFactor input
    ; dataEnergyFactorNonnegative =
        effectiveParabolicDataFactorNonnegative input
    ; viscositySplit = viscositySplit input
    ; criticalNonnegative = criticalNonnegative input
    ; dissipationNonnegative = dissipationNonnegative input
    ; localMassBelowDataCriticalDissipation =
        weightedLocalMassBelowParabolicCriticalDissipation input
    }

hhGoodParabolicPeriodizedOwnerReductionClosed : Bool
hhGoodParabolicPeriodizedOwnerReductionClosed = true

physicalHHGoodOwnerNowReducedToParabolicSameObjectInput : Bool
physicalHHGoodOwnerNowReducedToParabolicSameObjectInput = true

hhGoodParabolicPeriodizedOwnerReductionClosedIsTrue :
  hhGoodParabolicPeriodizedOwnerReductionClosed ≡ true
hhGoodParabolicPeriodizedOwnerReductionClosedIsTrue = refl
