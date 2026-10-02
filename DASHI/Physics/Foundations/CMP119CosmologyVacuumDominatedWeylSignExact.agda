{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyVacuumDominatedWeylSignExact where

------------------------------------------------------------------------
-- VACUUM-DOMINATED SIGN COMPILER FOR THE FINITE EUCLIDEAN WEYL RESPONSE.
--
-- Existing exact facts:
--
--   N_nonW = N_E + N_R + N_B + N_V,
--   N_V    = c_V * Z,
--   Q_E    = - N_nonW.
--
-- Therefore the remaining sign problem can be separated into two genuinely
-- physical/source obligations:
--
--   (1) c_V > 0 for the selected vacuum Weyl coefficient;
--   (2) N_E + N_R + N_B >= 0 (or any stronger lower bound).
--
-- Together with Z > 0 these imply Q_E < 0.
--
-- This file DOES NOT assert either source sign.  It is only the exact compiler
-- from those signs to the cosmologically relevant finite Weyl-response sign.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyPartitionWeylTraceExact as Weyl
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSectorDecompositionExact as Sector
import DASHI.Physics.Foundations.CMP119CosmologyVacuumSectorFactorizationExact as Vacuum
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

erbNumerator :
  ∀ {Configuration} →
  Physical.PhysicalFiniteYMMeasure Configuration ℚ →
  Source.CompleteFiniteMetricVariation Configuration →
  ℚ
erbNumerator measure d =
  (Sector.regularNumerator measure d
    + Sector.rOperationNumerator measure d)
  + Sector.boundaryNumerator measure d

vacuumNumeratorPositive :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (d : Source.CompleteFiniteMetricVariation Configuration)
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (scaleLaw : Vacuum.RationalHaarScaleLaw measure)
    (constant : Vacuum.VacuumTraceConstant d) →
  0ℚ < Vacuum.coefficient constant →
  0ℚ < Sector.vacuumNumerator measure d
vacuumNumeratorPositive measure d partition scaleLaw constant coefficientPositive =
  let
    zPositive :
      0ℚ < Physical.haarIntegral measure (Physical.density measure)
    zPositive =
      subst
        (λ value → 0ℚ < value)
        (Partition.partitionIsDensityIntegral partition)
        (Partition.partitionPositive partition)

    scaledPositive :
      Vacuum.coefficient constant * 0ℚ
      <
      Vacuum.coefficient constant
        * Physical.haarIntegral measure (Physical.density measure)
    scaledPositive =
      ℚP.*-monoˡ-<-pos
        (Vacuum.coefficient constant)
        zPositive

    productPositive :
      0ℚ
      <
      Vacuum.coefficient constant
        * Physical.haarIntegral measure (Physical.density measure)
    productPositive =
      subst
        (λ left →
          left <
          Vacuum.coefficient constant
            * Physical.haarIntegral measure (Physical.density measure))
        (Ring.solve-∀ (Vacuum.coefficient constant))
        scaledPositive
  in
  subst
    (λ value → 0ℚ < value)
    (sym (Vacuum.vacuumNumeratorFactors measure d scaleLaw constant))
    productPositive

erbNonnegativeAndVacuumPositiveGivePositiveFourSectorBalance :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (d : Source.CompleteFiniteMetricVariation Configuration) →
  0ℚ ≤ erbNumerator measure d →
  0ℚ < Sector.vacuumNumerator measure d →
  0ℚ <
    ((Sector.regularNumerator measure d
      + Sector.rOperationNumerator measure d)
      + (Sector.boundaryNumerator measure d
        + Sector.vacuumNumerator measure d))
erbNonnegativeAndVacuumPositiveGivePositiveFourSectorBalance
    measure d erbNonnegative vacuumPositive =
  let
    vacuumBelowTotal :
      Sector.vacuumNumerator measure d
      ≤
      ((Sector.regularNumerator measure d
        + Sector.rOperationNumerator measure d)
        + (Sector.boundaryNumerator measure d
          + Sector.vacuumNumerator measure d))
    vacuumBelowTotal =
      subst
        (λ left →
          left
          ≤
          ((Sector.regularNumerator measure d
            + Sector.rOperationNumerator measure d)
            + (Sector.boundaryNumerator measure d
              + Sector.vacuumNumerator measure d)))
        (Ring.solve-∀ (Sector.vacuumNumerator measure d))
        (subst
          (λ right →
            0ℚ + Sector.vacuumNumerator measure d ≤ right)
          (Ring.solve-∀
            (Sector.regularNumerator measure d)
            (Sector.rOperationNumerator measure d)
            (Sector.boundaryNumerator measure d)
            (Sector.vacuumNumerator measure d))
          (ℚP.+-mono-≤ erbNonnegative ℚP.≤-refl))
  in
  ℚP.<-≤-trans vacuumPositive vacuumBelowTotal

vacuumDominatedSourceForcesNegativeFiniteWeylResponse :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (d : Source.CompleteFiniteMetricVariation Configuration)
    (laws : Sign.RationalWeylSignIntegrationLaws measure)
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (scaleLaw : Vacuum.RationalHaarScaleLaw measure)
    (constant : Vacuum.VacuumTraceConstant d)
    (referenceFixed :
      ∀ h x → Source.referenceMeasureLogVariation d h x ≡ 0ℚ) →
  0ℚ < Vacuum.coefficient constant →
  0ℚ ≤ erbNumerator measure d →
  Weyl.fourDiagonalPartitionDerivativeSum measure d < 0ℚ
vacuumDominatedSourceForcesNegativeFiniteWeylResponse
    measure d laws partition scaleLaw constant referenceFixed
    coefficientPositive erbNonnegative =
  Sector.positiveFourSectorBalanceForcesNegativeWeylResponse
    measure d laws referenceFixed
    (erbNonnegativeAndVacuumPositiveGivePositiveFourSectorBalance
      measure d erbNonnegative
      (vacuumNumeratorPositive
        measure d partition scaleLaw constant coefficientPositive))

vacuumCoefficientSignIsStillPhysicalInput : Bool
vacuumCoefficientSignIsStillPhysicalInput = true

erbBalanceSignIsStillPhysicalInput : Bool
erbBalanceSignIsStillPhysicalInput = true

negativeFiniteWeylResponseNowFollowsFromTwoSourceSignObligations : Bool
negativeFiniteWeylResponseNowFollowsFromTwoSourceSignObligations = true
