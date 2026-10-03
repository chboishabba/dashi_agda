{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPartitionDerivativeTailMarginExact where

------------------------------------------------------------------------
-- PREFERRED B2: ONE-POINT PARTITION RESPONSE BEATS THE R109 TAIL.
--
-- Under fixed product Haar the existing finite source theorem proves
--
--   D_Weyl Z = - N_nonWilson.
--
-- Therefore the source-native terminal inequality
--
--   N_nonWilson + tail * Z < 0
--
-- follows exactly from the physically more transparent one-point statement
--
--   tail * Z < D_Weyl Z.
--
-- This is the correct response order for cosmology.  It does not consume the
-- connected derivative of a normalized insertion used in the antigravity
-- ordered-Haar trace lane.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _<_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (subst; subst₂)

import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyPartitionWeylTraceExact as Weyl
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

partitionDerivativeBeatsTailForcesSourceNumeratorMargin :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (d : Source.CompleteFiniteMetricVariation Configuration)
    (laws : Sign.RationalWeylSignIntegrationLaws measure)
    (referenceFixed :
      ∀ h x → Source.referenceMeasureLogVariation d h x ≡ 0ℚ)
    (tail : ℚ) →
  tail * Physical.partitionFunction measure
    < Weyl.fourDiagonalPartitionDerivativeSum measure d →
  Sign.weightedNonWilsonWeylNumerator measure d
    + tail * Physical.partitionFunction measure
    < 0ℚ
partitionDerivativeBeatsTailForcesSourceNumeratorMargin
    measure d laws referenceFixed tail tailBelowPartition =
  let
    numerator = Sign.weightedNonWilsonWeylNumerator measure d
    tailDebt = tail * Physical.partitionFunction measure

    tailBelowNegativeNumerator : tailDebt < - numerator
    tailBelowNegativeNumerator =
      subst
        (λ right → tailDebt < right)
        (Sign.fixedHaarResponseIsNegativeWeightedNonWilsonNumerator
          measure d laws referenceFixed)
        tailBelowPartition

    shifted : tailDebt + numerator < (- numerator) + numerator
    shifted =
      ℚP.+-mono-<-≤ tailBelowNegativeNumerator ℚP.≤-refl
  in
  subst₂ _<_
    (Ring.solve-∀ numerator tailDebt)
    (Ring.solve-∀ numerator)
    shifted

partitionDerivativeTailDominanceIsSufficientForB2 : Bool
partitionDerivativeTailDominanceIsSufficientForB2 = true

connectedNormalizedTraceIsNotRequiredForB2 : Bool
connectedNormalizedTraceIsNotRequiredForB2 = true

sourceFacingB2IsOnePointPartitionResponse : Bool
sourceFacingB2IsOnePointPartitionResponse = true
