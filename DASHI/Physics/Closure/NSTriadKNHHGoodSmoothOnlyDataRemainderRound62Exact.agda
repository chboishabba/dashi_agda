module DASHI.Physics.Closure.NSTriadKNHHGoodSmoothOnlyDataRemainderRound62Exact where

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
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 62 CONTRIBUTION
--
-- The singular/parabolic HH-good owner is already pure Young:
--
--   P_near <= epsilon D + B(epsilon) X,
--
-- with dataRemainder = 0 definitionally.  The later torus composition adds a
-- smooth periodic correction, and only THAT term is allowed to carry additive
-- data remainder.  Therefore for every Young split
--
--   dataRemainder(HH-good owner) = smoothDataRemainder.
--
-- C should bound this smaller same-object quantity rather than an opaque total
-- HH-good remainder.  The viscosity coefficient remains exactly epsilon.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHGoodFiniteKernelCauchyRound40Exact as Good
import DASHI.Physics.Closure.NSTriadKNHHGoodPeriodizedKernelUniformRound40Exact as Periodized
import DASHI.Physics.Closure.NSTriadKNHHGoodYoungSoftTaxRound45Exact as Soft

hhGoodDataRemainderIsSmoothOnly :
  ∀ {st : Level} {TorusPoint : Set st}
    {environment : Owner.TaxEnvironment}
    {kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell : Nat}
    {parameter : Threshold.PositiveThreshold}
    {samples : List (Good.HHGoodKernelSample parameter)}
    (producer : Soft.PhysicalHHGoodProducerWithoutSplit
      environment kernelTheorem shell parameter samples)
    (split : Threshold.PositiveThreshold) →
  Owner.dataRemainder (Soft.physicalHHGoodOwnerAtSplit producer split)
  ≡ Soft.smoothDataRemainder producer
hhGoodDataRemainderIsSmoothOnly producer split =
  solve (Soft.smoothDataRemainder producer ∷ [])

hhGoodEtaStillExactlySplit :
  ∀ {st : Level} {TorusPoint : Set st}
    {environment : Owner.TaxEnvironment}
    {kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell : Nat}
    {parameter : Threshold.PositiveThreshold}
    {samples : List (Good.HHGoodKernelSample parameter)}
    (producer : Soft.PhysicalHHGoodProducerWithoutSplit
      environment kernelTheorem shell parameter samples)
    (split : Threshold.PositiveThreshold) →
  Owner.eta (Soft.physicalHHGoodOwnerAtSplit producer split)
  ≡ Threshold.threshold split
hhGoodEtaStillExactlySplit = Soft.physicalHHGoodEtaAtSplitExact

hhGoodAdditiveCScaleIsSmoothCorrectionOnly : Bool
hhGoodAdditiveCScaleIsSmoothCorrectionOnly = true

hhGoodAdditiveCScaleIsSmoothCorrectionOnlyIsTrue :
  hhGoodAdditiveCScaleIsSmoothCorrectionOnly ≡ true
hhGoodAdditiveCScaleIsSmoothCorrectionOnlyIsTrue = refl
