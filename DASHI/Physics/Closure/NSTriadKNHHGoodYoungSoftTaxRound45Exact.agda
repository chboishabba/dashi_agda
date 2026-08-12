module DASHI.Physics.Closure.NSTriadKNHHGoodYoungSoftTaxRound45Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
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
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- The existing HH-good parabolic owner stores the Young viscosity split as an
-- input field.  That can obscure an important distinction: once the physical
-- annular/parabolic producer exists, the split itself is not a hard viscosity
-- floor.  The same physical data may be paired with *any* PositiveThreshold
-- epsilon, yielding
--
--   P_HHg <= epsilon D + B(epsilon) X + A.
--
-- This file factors the split out of the physical producer.  A
-- `PhysicalHHGoodProducerWithoutSplit` owns every physical datum used by the
-- Round-42 parabolic lane and the Round-43 smooth correction, but no epsilon.
-- For every supplied positive rational split it reconstructs the exact existing
-- inputs and proves the final HH-good owner's eta is definitionally that split.
--
-- Thus HH-good is proved Young-soft *conditional only on the genuine physical
-- producer*.  This does not construct the still-open annular kernel or local
-- mass theorem and does not claim eta=0; it proves there is no positive floor
-- introduced by Young algebra itself.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHGoodFiniteKernelCauchyRound40Exact as Good
import DASHI.Physics.Closure.NSTriadKNHHGoodPeriodizedKernelUniformRound40Exact as Periodized
import DASHI.Physics.Closure.NSTriadKNHHGoodParabolicAmplitudeAllocationRound42Exact as Allocation
import DASHI.Physics.Closure.NSTriadKNHHGoodParabolicPeriodizedOwnerRound42Exact as Parabolic
import DASHI.Physics.Closure.NSTriadKNHHGoodParabolicSmoothOwnerRound43Exact as Smooth

record PhysicalHHGoodProducerWithoutSplit
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
      Allocation.ParabolicHHGoodCriticalRecovery
        environment shell dataEnergy windowConstant quarticEnvelope

    weightedLocalMassIsLocalizedParabolicMass :
      Good.weightedLocalMass samples
      ≡ Allocation.localizedAmplitudeQuarticMass
          (Allocation.cells
            (Allocation.recovery parabolicCriticalRecovery))

    criticalNonnegative : 0ℚ ≤ Owner.integralCritical environment
    dissipationNonnegative : 0ℚ ≤ Owner.dissipation environment

    smoothProduction : ℚ
    smoothDataRemainder : ℚ
    smoothCriticalCoefficient : ℚ

    physicalHHGoodSmoothPeriodicCorrectionBound :
      smoothProduction
      ≤ smoothDataRemainder
        + smoothCriticalCoefficient * Owner.integralCritical environment

open PhysicalHHGoodProducerWithoutSplit public

parabolicInputAtSplit :
  ∀ {st} {TorusPoint : Set st}
    {environment : Owner.TaxEnvironment}
    {kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell parameter samples} →
  PhysicalHHGoodProducerWithoutSplit
    environment kernelTheorem shell parameter samples →
  Threshold.PositiveThreshold →
  Parabolic.PeriodizedParabolicHHGoodInput
    environment kernelTheorem shell parameter samples
parabolicInputAtSplit producer split = record
  { kernelIdentification = kernelIdentification producer
  ; dataEnergy = dataEnergy producer
  ; windowConstant = windowConstant producer
  ; quarticEnvelope = quarticEnvelope producer
  ; parabolicCriticalRecovery = parabolicCriticalRecovery producer
  ; weightedLocalMassIsLocalizedParabolicMass =
      weightedLocalMassIsLocalizedParabolicMass producer
  ; criticalNonnegative = criticalNonnegative producer
  ; dissipationNonnegative = dissipationNonnegative producer
  ; viscositySplit = split
  }

fullHHGoodInputAtSplit :
  ∀ {st} {TorusPoint : Set st}
    {environment : Owner.TaxEnvironment}
    {kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell parameter samples} →
  (producer : PhysicalHHGoodProducerWithoutSplit
    environment kernelTheorem shell parameter samples) →
  (split : Threshold.PositiveThreshold) →
  Smooth.PhysicalParabolicSmoothHHGoodInput
    environment kernelTheorem shell parameter samples
fullHHGoodInputAtSplit producer split = record
  { parabolicInput = parabolicInputAtSplit producer split
  ; smoothProduction = smoothProduction producer
  ; smoothDataRemainder = smoothDataRemainder producer
  ; smoothCriticalCoefficient = smoothCriticalCoefficient producer
  ; physicalHHGoodSmoothPeriodicCorrectionBound =
      physicalHHGoodSmoothPeriodicCorrectionBound producer
  }

physicalHHGoodOwnerAtSplit :
  ∀ {st} {TorusPoint : Set st}
    {environment : Owner.TaxEnvironment}
    {kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell parameter samples} →
  (producer : PhysicalHHGoodProducerWithoutSplit
    environment kernelTheorem shell parameter samples) →
  (split : Threshold.PositiveThreshold) →
  Owner.AdmissibleOwnerEstimate environment
physicalHHGoodOwnerAtSplit producer split =
  Smooth.physicalHHGoodOwnerEstimate
    (fullHHGoodInputAtSplit producer split)

physicalHHGoodOwnerAtSplitIdentity :
  ∀ {st} {TorusPoint : Set st}
    {environment : Owner.TaxEnvironment}
    {kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell parameter samples}
    (producer : PhysicalHHGoodProducerWithoutSplit
      environment kernelTheorem shell parameter samples)
    (split : Threshold.PositiveThreshold) →
  Owner.owner (physicalHHGoodOwnerAtSplit producer split) ≡ Tax.HH-good
physicalHHGoodOwnerAtSplitIdentity producer split = refl

physicalHHGoodEtaAtSplitExact :
  ∀ {st} {TorusPoint : Set st}
    {environment : Owner.TaxEnvironment}
    {kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell parameter samples}
    (producer : PhysicalHHGoodProducerWithoutSplit
      environment kernelTheorem shell parameter samples)
    (split : Threshold.PositiveThreshold) →
  Owner.eta (physicalHHGoodOwnerAtSplit producer split)
  ≡ Threshold.threshold split
physicalHHGoodEtaAtSplitExact producer split =
  trans
    (Smooth.smoothCorrectionDoesNotChangeHHGoodEta
      (fullHHGoodInputAtSplit producer split))
    refl

record YoungSoftOwnerFamily
    (environment : Owner.TaxEnvironment)
    (selectedOwner : Tax.TaxOwner) : Set₁ where
  field
    estimateAtSplit :
      Threshold.PositiveThreshold → Owner.AdmissibleOwnerEstimate environment
    ownerAtSplit : ∀ split →
      Owner.owner (estimateAtSplit split) ≡ selectedOwner
    etaAtSplit : ∀ split →
      Owner.eta (estimateAtSplit split) ≡ Threshold.threshold split

open YoungSoftOwnerFamily public

physicalHHGoodYoungSoftFamily :
  ∀ {st} {TorusPoint : Set st}
    {environment : Owner.TaxEnvironment}
    {kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell parameter samples} →
  PhysicalHHGoodProducerWithoutSplit
    environment kernelTheorem shell parameter samples →
  YoungSoftOwnerFamily environment Tax.HH-good
physicalHHGoodYoungSoftFamily producer = record
  { estimateAtSplit = physicalHHGoodOwnerAtSplit producer
  ; ownerAtSplit = physicalHHGoodOwnerAtSplitIdentity producer
  ; etaAtSplit = physicalHHGoodEtaAtSplitExact producer
  }

hhGoodYoungTaxHasNoAlgebraicPositiveFloor : Bool
hhGoodYoungTaxHasNoAlgebraicPositiveFloor = true

hhGoodYoungTaxHasNoAlgebraicPositiveFloorIsTrue :
  hhGoodYoungTaxHasNoAlgebraicPositiveFloor ≡ true
hhGoodYoungTaxHasNoAlgebraicPositiveFloorIsTrue = refl
