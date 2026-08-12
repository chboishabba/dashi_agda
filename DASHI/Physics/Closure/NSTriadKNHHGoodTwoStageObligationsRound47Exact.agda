module DASHI.Physics.Closure.NSTriadKNHHGoodTwoStageObligationsRound47Exact where

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
-- Round 46 proved that HH-good's critical coefficient does not consume
-- residual viscosity.  Round 47 splits the remaining physical programme into
-- two logically distinct obligations:
--
--   Stage A: construct the finite cutoff-uniform annular/parabolic producer.
--            This already gives a Young-soft HH-good owner family.
--
--   Stage B: prove that the resulting finite coefficient is compatible with
--            the later explicit-majorant / fixed-shift recursion.
--
-- Stage B is intentionally NOT a prerequisite for Young-soft classification.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNHHGoodFiniteKernelCauchyRound40Exact as Good
import DASHI.Physics.Closure.NSTriadKNHHGoodPeriodizedKernelUniformRound40Exact as Periodized
import DASHI.Physics.Closure.NSTriadKNHHGoodYoungSoftTaxRound45Exact as Soft

record HHGoodFiniteProducerStage
    {st : Level}
    {TorusPoint : Set st}
    (environment : Owner.TaxEnvironment)
    (kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint)
    (shell : Nat)
    (parameter : Threshold.PositiveThreshold)
    (samples : List (Good.HHGoodKernelSample parameter)) : Set (lsuc st) where
  field
    producer :
      Soft.PhysicalHHGoodProducerWithoutSplit
        environment kernelTheorem shell parameter samples

open HHGoodFiniteProducerStage public

hhGoodYoungSoftFromFiniteProducerStage :
  ∀ {st} {TorusPoint : Set st}
    {environment : Owner.TaxEnvironment}
    {kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell parameter samples} →
  HHGoodFiniteProducerStage environment kernelTheorem shell parameter samples →
  Soft.YoungSoftOwnerFamily environment Tax.HH-good
hhGoodYoungSoftFromFiniteProducerStage stage =
  Soft.physicalHHGoodYoungSoftFamily (producer stage)

-- The downstream coefficient requirement is intentionally abstract here because
-- the actual block-decay bridge owns the explicit majorant and recursion types.
-- The record only states that a separately produced finite coefficient has been
-- checked against that later consumer.
record HHGoodDownstreamRecursionCompatibility
    (finiteCoefficient : ℚ) : Set₁ where
  field
    RecursionCompatibility : Set
    finiteCoefficientCompatible : RecursionCompatibility

open HHGoodDownstreamRecursionCompatibility public

record HHGoodTwoStageClosure
    {st : Level}
    {TorusPoint : Set st}
    {environment : Owner.TaxEnvironment}
    {kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell : Nat}
    {parameter : Threshold.PositiveThreshold}
    {samples : List (Good.HHGoodKernelSample parameter)} : Set (lsuc st) where
  field
    finiteStage :
      HHGoodFiniteProducerStage environment kernelTheorem shell parameter samples
    finiteCoefficient : ℚ
    downstreamStage : HHGoodDownstreamRecursionCompatibility finiteCoefficient

open HHGoodTwoStageClosure public

hhGoodReserveStageNeedsOnlyFiniteProducer : Bool
hhGoodReserveStageNeedsOnlyFiniteProducer = true

hhGoodDownstreamCompatibilityRemainsSeparate : Bool
hhGoodDownstreamCompatibilityRemainsSeparate = true

hhGoodReserveStageNeedsOnlyFiniteProducerIsTrue :
  hhGoodReserveStageNeedsOnlyFiniteProducer ≡ true
hhGoodReserveStageNeedsOnlyFiniteProducerIsTrue = refl
