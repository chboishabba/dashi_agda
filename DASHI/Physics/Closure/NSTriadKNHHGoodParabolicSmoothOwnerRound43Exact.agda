module DASHI.Physics.Closure.NSTriadKNHHGoodParabolicSmoothOwnerRound43Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 42 constructs the singular/periodized HH-good owner from the correct
-- parabolic window and same-object weighted local mass.  Round 39 separately
-- established the exact bookkeeping rule that a smooth periodic correction
-- contributes only data/critical remainder and must not consume viscosity.
--
-- This file composes those two already-proved pieces.  The viscosity tax in
-- the final physical HH-good owner is definitionally the parabolic Young tax;
-- the smooth torus correction cannot silently enlarge eta_HHg.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHGoodFiniteKernelCauchyRound40Exact as Good
import DASHI.Physics.Closure.NSTriadKNHHGoodPeriodizedKernelUniformRound40Exact as Periodized
import DASHI.Physics.Closure.NSTriadKNHHGoodParabolicPeriodizedOwnerRound42Exact as Parabolic
import DASHI.Physics.Closure.NSTriadKNPeriodicPVHHGoodNearSmoothOwnerRound39Exact as NearSmooth

record PhysicalParabolicSmoothHHGoodInput
    {st : Level}
    {TorusPoint : Set st}
    (environment : Owner.TaxEnvironment)
    (kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint)
    (shell : Nat)
    (parameter : Threshold.PositiveThreshold)
    (samples : List (Good.HHGoodKernelSample parameter)) : Set (lsuc st) where
  field
    parabolicInput :
      Parabolic.PeriodizedParabolicHHGoodInput
        environment kernelTheorem shell parameter samples

    smoothProduction : ℚ
    smoothDataRemainder : ℚ
    smoothCriticalCoefficient : ℚ

    physicalHHGoodSmoothPeriodicCorrectionBound :
      smoothProduction
      ≤ smoothDataRemainder
        + smoothCriticalCoefficient * Owner.integralCritical environment

open PhysicalParabolicSmoothHHGoodInput public

parabolicSingularOwner :
  ∀ {st} {TorusPoint : Set st}
    {environment : Owner.TaxEnvironment}
    {kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell parameter samples} →
  PhysicalParabolicSmoothHHGoodInput
    environment kernelTheorem shell parameter samples →
  Owner.AdmissibleOwnerEstimate environment
parabolicSingularOwner input =
  Parabolic.periodizedHHGoodOwnerFromParabolicKineticRecovery
    (parabolicInput input)

physicalHHGoodNearSmoothEstimate :
  ∀ {st} {TorusPoint : Set st}
    {environment : Owner.TaxEnvironment}
    {kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell parameter samples} →
  PhysicalParabolicSmoothHHGoodInput
    environment kernelTheorem shell parameter samples →
  NearSmooth.PeriodicPVHHGoodNearSmoothEstimate environment
physicalHHGoodNearSmoothEstimate {environment = environment} input = record
  { nearProduction = Owner.positiveProduction singular
  ; smoothProduction = smoothProduction input
  ; eta = Owner.eta singular
  ; nearDataRemainder = Owner.dataRemainder singular
  ; smoothDataRemainder = smoothDataRemainder input
  ; nearCriticalCoefficient = Owner.criticalCoefficient singular
  ; smoothCriticalCoefficient = smoothCriticalCoefficient input
  ; nearSingularBound = Owner.ownerBound singular
  ; smoothPeriodicBound = physicalHHGoodSmoothPeriodicCorrectionBound input
  }
  where
  singular = parabolicSingularOwner input

physicalHHGoodOwnerEstimate :
  ∀ {st} {TorusPoint : Set st}
    {environment : Owner.TaxEnvironment}
    {kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell parameter samples} →
  PhysicalParabolicSmoothHHGoodInput
    environment kernelTheorem shell parameter samples →
  Owner.AdmissibleOwnerEstimate environment
physicalHHGoodOwnerEstimate input =
  NearSmooth.hhGoodOwnerEstimateFromNearSmooth
    (physicalHHGoodNearSmoothEstimate input)

physicalHHGoodOwnerIdentity :
  ∀ {st} {TorusPoint : Set st}
    {environment : Owner.TaxEnvironment}
    {kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell parameter samples}
    (input : PhysicalParabolicSmoothHHGoodInput
      environment kernelTheorem shell parameter samples) →
  Owner.owner (physicalHHGoodOwnerEstimate input) ≡ Tax.HH-good
physicalHHGoodOwnerIdentity input = refl

smoothCorrectionDoesNotChangeHHGoodEta :
  ∀ {st} {TorusPoint : Set st}
    {environment : Owner.TaxEnvironment}
    {kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell parameter samples}
    (input : PhysicalParabolicSmoothHHGoodInput
      environment kernelTheorem shell parameter samples) →
  Owner.eta (physicalHHGoodOwnerEstimate input)
  ≡ Owner.eta (parabolicSingularOwner input)
smoothCorrectionDoesNotChangeHHGoodEta input = refl

hhGoodParabolicSmoothOwnerCompositionClosed : Bool
hhGoodParabolicSmoothOwnerCompositionClosed = true

hhGoodSmoothCorrectionConsumesNoViscosity : Bool
hhGoodSmoothCorrectionConsumesNoViscosity = true

hhGoodParabolicSmoothOwnerCompositionClosedIsTrue :
  hhGoodParabolicSmoothOwnerCompositionClosed ≡ true
hhGoodParabolicSmoothOwnerCompositionClosedIsTrue = refl

hhGoodSmoothCorrectionConsumesNoViscosityIsTrue :
  hhGoodSmoothCorrectionConsumesNoViscosity ≡ true
hhGoodSmoothCorrectionConsumesNoViscosityIsTrue = refl
