{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyUnnormalizedSourceTailMarginExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; Positive; positive; _+_; _*_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (cong; subst; subst₂; sym; trans)

import DASHI.Physics.Foundations.CMP119CosmologyEq223FiniteEffectiveActionUpperExact as Finite
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.Foundations.CMP119CosmologyVacuumSectorFactorizationExact as Vacuum
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureOrderExact as Order
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quot
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw

------------------------------------------------------------------------
-- SOURCE-NATIVE QUANTITATIVE B2 RECUT
--
-- Cosmology consumes the normalized margin
--
--   D_Gamma,k + Tail_109(k) < 0.
--
-- But the literal finite source naturally produces an unnormalized numerator N
-- and partition function Z>0 with
--
--   D_Gamma,k = N / Z.
--
-- Therefore the exact source-facing sufficient condition is
--
--   N + Tail_109(k) * Z < 0.
--
-- Multiplication by the positive reciprocal of Z proves this is equivalent in
-- the required direction.  This is strictly sharper than asking Eq.(2.23) to
-- provide a separately calibrated normalized vacuum threshold.
------------------------------------------------------------------------

module _
    {Density Background Fluctuation
     Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumTerm
     Configuration : Set}
    {source :
      Raw.CMP119SourceNativeRawState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumTerm}
    {scale : Nat}
    (realization :
      Eq223.Eq223SourceMetricVariationRealization
        source Configuration scale)
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (orderLaws : Order.RationalPositiveFiniteMeasureOrderLaws measure)
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (scaleLaw : Vacuum.RationalHaarScaleLaw measure)
    (signLaws : Sign.RationalWeylSignIntegrationLaws measure)
    (referenceFixed :
      ∀ h x →
      Source.referenceMeasureLogVariation
        (Eq223.sourceCompleteFiniteMetricVariation realization) h x
      ≡ 0ℚ)
  where

  module F =
    Finite realization measure orderLaws partition scaleLaw signLaws referenceFixed

  sourceNumeratorTailMarginForcesFiniteTailMargin :
    ∀ tail →
    F.nonWilsonNumerator + tail * F.z < 0ℚ →
    F.finiteEffectiveActionWeyl + tail < 0ℚ
  sourceNumeratorTailMarginForcesFiniteTailMargin tail sourceMargin =
    let
      zPositive = Partition.partitionPositive partition
      reciprocal = Quot.positiveReciprocal F.z zPositive

      instance
        reciprocalPositive : Positive reciprocal
        reciprocalPositive =
          positive (Quot.positiveReciprocalPositive F.z zPositive)

      scaled :
        (F.nonWilsonNumerator + tail * F.z) * reciprocal
        < 0ℚ * reciprocal
      scaled =
        ℚP.*-monoʳ-<-pos reciprocal sourceMargin

      leftExact :
        (F.nonWilsonNumerator + tail * F.z) * reciprocal
        ≡
        Quot.dividePositive F.nonWilsonNumerator F.z zPositive + tail
      leftExact =
        trans
          (Ring.solve-∀ F.nonWilsonNumerator tail F.z reciprocal)
          (trans
            (cong
              (λ zr → F.nonWilsonNumerator * reciprocal + tail * zr)
              (Quot.positiveReciprocalRightInverse F.z zPositive))
            (Ring.solve-∀ F.nonWilsonNumerator tail reciprocal))

      rightExact : 0ℚ * reciprocal ≡ 0ℚ
      rightExact = Ring.solve-∀ reciprocal

      normalizedMargin :
        Quot.dividePositive F.nonWilsonNumerator F.z zPositive + tail < 0ℚ
      normalizedMargin =
        subst₂ _<_ leftExact rightExact scaled
    in
    subst
      (λ finite → finite + tail < 0ℚ)
      (sym F.finiteEffectiveActionWeylIsNormalizedNonWilsonNumerator)
      normalizedMargin

sourceNumeratorMarginIsSufficientForPreferredB2 : Bool
sourceNumeratorMarginIsSufficientForPreferredB2 = true

sourceNumeratorMarginUsesSameUnitsAsFiniteSource : Bool
sourceNumeratorMarginUsesSameUnitsAsFiniteSource = true
