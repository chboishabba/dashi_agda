module DASHI.Physics.Closure.NSTriadKNPartialHardFloorNoGoRound45Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Gyula Farkas.
-- Title: "Theorie der einfachen Ungleichungen".
-- Journal fuer die reine und angewandte Mathematik 124 (1902), 1--27.
-- DOI: no DOI assigned to the historical article.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- The full nine-dimensional Farkas certificate is unnecessary when already
-- proved unavoidable floors consume the whole residual budget.  After Round
-- 45, boundary costs zero and HH-good's Young split is nonnegative but has no
-- algebraic positive floor.  Therefore lower floors for HH-bad, Com and kernel
-- alone can refute the current architecture.
--
-- If
--
--   floor_HHb + floor_Com + floor_kernel + 4/64 >= 1
--
-- and each floor is below its actual owner eta, then every positive HH-good
-- split only increases the total.  Hence the strict reserve is impossible.
-- This is a genuine partial no-go theorem: it can fire before all producers or
-- all numerical choices have been completed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Negation using (¬_)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNLuoFiniteCriticalFourClassClosureExact as Critical
import DASHI.Physics.Closure.NSTriadKNHardSoftReserveRound45Exact as HardSoft

fourBonyTax : ℚ
fourBonyTax =
  Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth

record PartialHardFloorCertificate
    {environment : Owner.TaxEnvironment}
    (core : HardSoft.HardSoftOwnerCore environment) : Set where
  field
    hhBadFloor comFloor kernelFloor : ℚ

    hhBadFloorBelowActual :
      hhBadFloor
      ≤ HardSoft.Sharp.two * HardSoft.hhBadProfileCeiling core

    comFloorBelowActual :
      comFloor ≤ Owner.eta (HardSoft.comEstimate core)

    kernelFloorBelowActual :
      kernelFloor ≤ Owner.eta (HardSoft.kernelEstimate core)

    floorsConsumeResidualReserve :
      1ℚ ≤ hhBadFloor + comFloor + kernelFloor + fourBonyTax

open PartialHardFloorCertificate public

actualHardBaseDominatesFloors :
  ∀ {environment}
    {core : HardSoft.HardSoftOwnerCore environment} →
  PartialHardFloorCertificate core →
  hhBadFloor _ + comFloor _ + kernelFloor _ + fourBonyTax
  ≤ HardSoft.Sharp.two * HardSoft.hhBadProfileCeiling core
    + Owner.eta (HardSoft.comEstimate core)
    + Owner.eta (HardSoft.kernelEstimate core)
    + fourBonyTax
actualHardBaseDominatesFloors certificate =
  let
    first = ℚP.+-mono-≤
      (hhBadFloorBelowActual certificate)
      (comFloorBelowActual certificate)
    second = ℚP.+-mono-≤
      first
      (kernelFloorBelowActual certificate)
    third = ℚP.+-mono-≤ second ℚP.≤-refl
  in
  subst
    (λ lower →
      lower
      ≤ HardSoft.Sharp.two
          * HardSoft.hhBadProfileCeiling _
        + Owner.eta (HardSoft.comEstimate _)
        + Owner.eta (HardSoft.kernelEstimate _)
        + fourBonyTax)
    (solve
      ( hhBadFloor certificate
      ∷ comFloor certificate
      ∷ kernelFloor certificate
      ∷ fourBonyTax
      ∷ []))
    (subst
      (λ upper →
        (hhBadFloor certificate + comFloor certificate + kernelFloor certificate)
          + fourBonyTax
        ≤ upper)
      (solve
        ( HardSoft.Sharp.two * HardSoft.hhBadProfileCeiling _
        ∷ Owner.eta (HardSoft.comEstimate _)
        ∷ Owner.eta (HardSoft.kernelEstimate _)
        ∷ fourBonyTax
        ∷ []))
      third)

partialFloorsForceTotalAtLeastOne :
  ∀ {environment}
    (core : HardSoft.HardSoftOwnerCore environment)
    (split : Threshold.PositiveThreshold) →
  PartialHardFloorCertificate core →
  1ℚ ≤ HardSoft.hardSoftEtaTotal core split
partialFloorsForceTotalAtLeastOne core split certificate =
  let
    floorToBase = actualHardBaseDominatesFloors certificate

    withEpsilon :
      0ℚ
        + (hhBadFloor certificate + comFloor certificate
          + kernelFloor certificate + fourBonyTax)
      ≤ Threshold.threshold split
        + (HardSoft.Sharp.two * HardSoft.hhBadProfileCeiling core
          + Owner.eta (HardSoft.comEstimate core)
          + Owner.eta (HardSoft.kernelEstimate core)
          + fourBonyTax)
    withEpsilon = ℚP.+-mono-≤
      (Threshold.thresholdNonnegative split)
      floorToBase

    normalized :
      hhBadFloor certificate + comFloor certificate
        + kernelFloor certificate + fourBonyTax
      ≤ HardSoft.hardSoftEtaTotal core split
    normalized =
      subst
        (λ lower → lower ≤ HardSoft.hardSoftEtaTotal core split)
        (solve
          ( hhBadFloor certificate
          ∷ comFloor certificate
          ∷ kernelFloor certificate
          ∷ fourBonyTax
          ∷ []))
        (subst
          (λ upper →
            0ℚ + (hhBadFloor certificate + comFloor certificate
              + kernelFloor certificate + fourBonyTax)
            ≤ upper)
          (solve
            ( Threshold.threshold split
            ∷ HardSoft.Sharp.two * HardSoft.hhBadProfileCeiling core
            ∷ Owner.eta (HardSoft.comEstimate core)
            ∷ Owner.eta (HardSoft.kernelEstimate core)
            ∷ Critical.oneSixtyFourth
            ∷ []))
          withEpsilon)
  in
  ℚP.≤-trans (floorsConsumeResidualReserve certificate) normalized

partialHardFloorNoGo :
  ∀ {environment}
    (core : HardSoft.HardSoftOwnerCore environment)
    (split : Threshold.PositiveThreshold)
    (certificate : PartialHardFloorCertificate core) →
  ¬ HardSoft.HardSoftStrictReserveAtSplit core split
partialHardFloorNoGo core split certificate reserve =
  let
    lower : 1ℚ ≤ HardSoft.hardSoftEtaTotal core split
    lower = partialFloorsForceTotalAtLeastOne core split certificate

    strict : HardSoft.hardSoftEtaTotal core split < 1ℚ
    strict = HardSoft.reducedTotalStrict reserve

    impossible : 1ℚ < 1ℚ
    impossible = ℚP.≤-<-trans lower strict
  in
  ℚP.<-irrefl refl impossible

partialHardFloorNoGoClosed : Bool
partialHardFloorNoGoClosed = true

partialHardFloorNoGoClosedIsTrue :
  partialHardFloorNoGoClosed ≡ true
partialHardFloorNoGoClosedIsTrue = refl
