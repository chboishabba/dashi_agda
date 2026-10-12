{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityStaticPairToDifferentialMetricResponseExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; _-_)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Physics.Foundations.CMP119AntigravityVacuumNormalizationGravityFirewallExact as Static
import DASHI.Physics.Foundations.CMP119AntigravityDifferentialMetricResponseFirewallExact as Differential

------------------------------------------------------------------------
-- TWO STATIC SAME-STATE PROMOTIONS -> DIFFERENTIAL SAME-STATE PROMOTION
--
-- If the OFF and ON states have each already paid the physical static weld
-- from their source normalization coordinate to the renormalized gravitational
-- metric response, and both are declared under one common cosmological
-- renormalization convention, then no second source-difference identification
-- theorem is required.  Delta-Lambda is obtained by equality transport.
------------------------------------------------------------------------

record CommonRenormalizedVacuumPair : Set₁ where
  field
    sourceOff : ℚ
    sourceOn : ℚ

    off : Static.VacuumNormalizationToGravityReceipt sourceOff
    on : Static.VacuumNormalizationToGravityReceipt sourceOn

    CommonRenormalizationConvention : Set
    commonRenormalizationConvention : CommonRenormalizationConvention

open CommonRenormalizedVacuumPair public

staticPairToDifferentialMetricResponse :
  CommonRenormalizedVacuumPair →
  Differential.DifferentialMetricResponseReceipt
staticPairToDifferentialMetricResponse pair = record
  { Differential.DifferentialMetricResponseReceipt.normalizationOff = sourceOff pair
  ; Differential.DifferentialMetricResponseReceipt.normalizationOn = sourceOn pair
  ; Differential.DifferentialMetricResponseReceipt.physicalLambdaOff =
      Static.renormalizedGravitationalAmplitude (off pair)
  ; Differential.DifferentialMetricResponseReceipt.physicalLambdaOn =
      Static.renormalizedGravitationalAmplitude (on pair)
  ; Differential.DifferentialMetricResponseReceipt.OffMetricResponseSameStateReceipt =
      Static.SameStateMetricVolumeReceipt (off pair)
  ; Differential.DifferentialMetricResponseReceipt.offMetricResponseSameStateReceipt =
      Static.sameStateMetricVolumeReceipt (off pair)
  ; Differential.DifferentialMetricResponseReceipt.OnMetricResponseSameStateReceipt =
      Static.SameStateMetricVolumeReceipt (on pair)
  ; Differential.DifferentialMetricResponseReceipt.onMetricResponseSameStateReceipt =
      Static.sameStateMetricVolumeReceipt (on pair)
  ; Differential.DifferentialMetricResponseReceipt.CommonCosmologicalRenormalizationConditionReceipt =
      CommonRenormalizationConvention pair
  ; Differential.DifferentialMetricResponseReceipt.commonCosmologicalRenormalizationConditionReceipt =
      commonRenormalizationConvention pair
  ; Differential.DifferentialMetricResponseReceipt.normalizationDifferenceMatchesMetricResponseDifference =
      cong₂ _-_
        (Static.sourceNormalizationSameObjectAsRenormalizedAmplitude (on pair))
        (Static.sourceNormalizationSameObjectAsRenormalizedAmplitude (off pair))
  }

normalizationDifferenceMatchesMetricResponseDifference :
  (pair : CommonRenormalizedVacuumPair) →
  sourceOn pair - sourceOff pair
  ≡
  Static.renormalizedGravitationalAmplitude (on pair)
  - Static.renormalizedGravitationalAmplitude (off pair)
normalizationDifferenceMatchesMetricResponseDifference pair =
  Differential.normalizationDifferenceMatchesMetricResponseDifference
    (staticPairToDifferentialMetricResponse pair)

independentDifferentialSameObjectTheoremRequiredAfterTwoStaticReceipts : Bool
independentDifferentialSameObjectTheoremRequiredAfterTwoStaticReceipts = false

commonRenormalizationConventionRequired : Bool
commonRenormalizationConventionRequired = true

staticPairToDifferentialCompilerOwned : Bool
staticPairToDifferentialCompilerOwned = true
