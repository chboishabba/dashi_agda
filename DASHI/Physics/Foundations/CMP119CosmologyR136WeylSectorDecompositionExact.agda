{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR136WeylSectorDecompositionExact where

------------------------------------------------------------------------
-- EXACT FOUR-SECTOR DECOMPOSITION OF THE NON-WILSON WEYL SIGN NUMERATOR.
--
-- The classical Wilson diagonal trace has already cancelled.
-- The remaining complete-action Weyl source is carried by:
--
--   regular + R-operation + boundary + vacuum.
--
-- This file decomposes the weighted numerator used by the strict-sign max-cut:
--
--   N_nonWilson
--     = N_regular + N_R + N_boundary + N_vacuum.
--
-- Hence the strict sign problem can be attacked sectorwise without changing
-- the selected finite measure or stress source.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureIntegrationLawsExact as Integral
import DASHI.Physics.Foundations.CMP119CosmologyPartitionWeylTraceExact as Weyl
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

regularDiagonalTrace :
  ∀ {Configuration} →
  Source.CompleteFiniteMetricVariation Configuration →
  Configuration → ℚ
regularDiagonalTrace d x =
  (Source.regularVariation d K.component00 x
    + Source.regularVariation d K.component11 x)
  +
  (Source.regularVariation d K.component22 x
    + Source.regularVariation d K.component33 x)

rOperationDiagonalTrace :
  ∀ {Configuration} →
  Source.CompleteFiniteMetricVariation Configuration →
  Configuration → ℚ
rOperationDiagonalTrace d x =
  (Source.rOperationVariation d K.component00 x
    + Source.rOperationVariation d K.component11 x)
  +
  (Source.rOperationVariation d K.component22 x
    + Source.rOperationVariation d K.component33 x)

boundaryDiagonalTrace :
  ∀ {Configuration} →
  Source.CompleteFiniteMetricVariation Configuration →
  Configuration → ℚ
boundaryDiagonalTrace d x =
  (Source.boundaryVariation d K.component00 x
    + Source.boundaryVariation d K.component11 x)
  +
  (Source.boundaryVariation d K.component22 x
    + Source.boundaryVariation d K.component33 x)

vacuumDiagonalTrace :
  ∀ {Configuration} →
  Source.CompleteFiniteMetricVariation Configuration →
  Configuration → ℚ
vacuumDiagonalTrace d x =
  (Source.vacuumVariation d K.component00 x
    + Source.vacuumVariation d K.component11 x)
  +
  (Source.vacuumVariation d K.component22 x
    + Source.vacuumVariation d K.component33 x)

nonWilsonTraceSplitsFourWays :
  ∀ {Configuration}
    (d : Source.CompleteFiniteMetricVariation Configuration)
    x →
  Weyl.nonWilsonDiagonalTrace d x
  ≡
  ((regularDiagonalTrace d x + rOperationDiagonalTrace d x)
    + (boundaryDiagonalTrace d x + vacuumDiagonalTrace d x))
nonWilsonTraceSplitsFourWays d x =
  Ring.solve-∀
    (Source.regularVariation d K.component00 x)
    (Source.regularVariation d K.component11 x)
    (Source.regularVariation d K.component22 x)
    (Source.regularVariation d K.component33 x)
    (Source.rOperationVariation d K.component00 x)
    (Source.rOperationVariation d K.component11 x)
    (Source.rOperationVariation d K.component22 x)
    (Source.rOperationVariation d K.component33 x)
    (Source.boundaryVariation d K.component00 x)
    (Source.boundaryVariation d K.component11 x)
    (Source.boundaryVariation d K.component22 x)
    (Source.boundaryVariation d K.component33 x)
    (Source.vacuumVariation d K.component00 x)
    (Source.vacuumVariation d K.component11 x)
    (Source.vacuumVariation d K.component22 x)
    (Source.vacuumVariation d K.component33 x)

weightedSectorNumerator :
  ∀ {Configuration} →
  Physical.PhysicalFiniteYMMeasure Configuration ℚ →
  (Configuration → ℚ) →
  ℚ
weightedSectorNumerator measure trace =
  Physical.haarIntegral measure
    (λ x → Physical.density measure x * trace x)

regularNumerator :
  ∀ {Configuration} →
  Physical.PhysicalFiniteYMMeasure Configuration ℚ →
  Source.CompleteFiniteMetricVariation Configuration → ℚ
regularNumerator measure d =
  weightedSectorNumerator measure (regularDiagonalTrace d)

rOperationNumerator :
  ∀ {Configuration} →
  Physical.PhysicalFiniteYMMeasure Configuration ℚ →
  Source.CompleteFiniteMetricVariation Configuration → ℚ
rOperationNumerator measure d =
  weightedSectorNumerator measure (rOperationDiagonalTrace d)

boundaryNumerator :
  ∀ {Configuration} →
  Physical.PhysicalFiniteYMMeasure Configuration ℚ →
  Source.CompleteFiniteMetricVariation Configuration → ℚ
boundaryNumerator measure d =
  weightedSectorNumerator measure (boundaryDiagonalTrace d)

vacuumNumerator :
  ∀ {Configuration} →
  Physical.PhysicalFiniteYMMeasure Configuration ℚ →
  Source.CompleteFiniteMetricVariation Configuration → ℚ
vacuumNumerator measure d =
  weightedSectorNumerator measure (vacuumDiagonalTrace d)

weightedNonWilsonNumeratorSplitsFourWays :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (d : Source.CompleteFiniteMetricVariation Configuration)
    (laws : Integral.RationalFiniteMeasureIntegrationLaws measure) →
  Sign.weightedNonWilsonWeylNumerator measure d
  ≡
  ((regularNumerator measure d + rOperationNumerator measure d)
    + (boundaryNumerator measure d + vacuumNumerator measure d))
weightedNonWilsonNumeratorSplitsFourWays measure d laws =
  let
    fr = λ x → Physical.density measure x * regularDiagonalTrace d x
    fR = λ x → Physical.density measure x * rOperationDiagonalTrace d x
    fb = λ x → Physical.density measure x * boundaryDiagonalTrace d x
    fv = λ x → Physical.density measure x * vacuumDiagonalTrace d x
  in
  trans
    (Integral.haarIntegralCongruent laws _ _
      (λ x →
        trans
          (cong
            (λ trace → Physical.density measure x * trace)
            (nonWilsonTraceSplitsFourWays d x))
          (Ring.solve-∀
            (Physical.density measure x)
            (regularDiagonalTrace d x)
            (rOperationDiagonalTrace d x)
            (boundaryDiagonalTrace d x)
            (vacuumDiagonalTrace d x))))
    (Integral.haarIntegralFourAdd laws fr fR fb fv)

strictSignTargetIsPositiveFourSectorBalance : Bool
strictSignTargetIsPositiveFourSectorBalance = true

wilsonSectorAbsentFromBalance : Bool
wilsonSectorAbsentFromBalance = true


positiveFourSectorBalanceForcesNegativeWeylResponse :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (d : Source.CompleteFiniteMetricVariation Configuration)
    (laws : Sign.RationalWeylSignIntegrationLaws measure)
    (referenceFixed :
      ∀ h x → Source.referenceMeasureLogVariation d h x ≡ 0ℚ) →
  0ℚ <
    ((regularNumerator measure d + rOperationNumerator measure d)
      + (boundaryNumerator measure d + vacuumNumerator measure d)) →
  Weyl.fourDiagonalPartitionDerivativeSum measure d < 0ℚ
positiveFourSectorBalanceForcesNegativeWeylResponse
    measure d laws referenceFixed balancePositive =
  Sign.positiveWeightedNonWilsonNumeratorForcesNegativeWeylResponse
    measure d laws referenceFixed
    (subst
      (λ value → 0ℚ < value)
      (sym
        (weightedNonWilsonNumeratorSplitsFourWays
          measure d (Sign.base laws)))
      balancePositive)

strictSignNowSectorwise : Bool
strictSignNowSectorwise = true
