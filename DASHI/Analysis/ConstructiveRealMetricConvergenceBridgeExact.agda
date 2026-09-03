module DASHI.Analysis.ConstructiveRealMetricConvergenceBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConstructiveRealSpine as CRS
import DASHI.Analysis.MarxConstructiveRealTopology as CRT
import DASHI.Analysis.MetricConvergenceKernelBidiExact as Metric

------------------------------------------------------------------------
-- CONSTRUCTIVE-REAL -> GENERIC METRIC CONVERGENCE BRIDGE
--
-- The repo already owns a proof-producing constructive-real spine with
-- sequences, a Cauchy predicate, convergence and a Cauchy-limit constructor.
-- This owner prevents the Casimir lane from inventing a second notion of
-- complete scalar analysis.  It translates the generic epsilon/tail theorem
-- shape onto the existing Real R carrier and its absolute-value metric.
------------------------------------------------------------------------

record ConstructiveRealMetricFamily
    (R : CRS.ConstructedOrderedCompleteReal)
    (A : CRT.ConstructedRealAbsoluteValueLaws R) : Set₁ where
  field
    Parameter : Set
    Index : Set

    _≼_ : Index → Index → Set

    family : Parameter → Index → CRS.Real R
    candidate : Parameter → CRS.Real R

    directedIndexSemantics : Set
    reading : String

open ConstructiveRealMetricFamily public

closeWithin :
  (R : CRS.ConstructedOrderedCompleteReal) →
  CRS.Real R → CRS.Real R → CRS.Real R → Set
closeWithin R x y ε =
  CRS._<_ R (CRT.distance R x y) ε

positiveEpsilon :
  (R : CRS.ConstructedOrderedCompleteReal) →
  CRS.Real R → Set
positiveEpsilon R ε = CRS._<_ R (CRS.zero R) ε

asMetricLimitProblem :
  (R : CRS.ConstructedOrderedCompleteReal) →
  (A : CRT.ConstructedRealAbsoluteValueLaws R) →
  ConstructiveRealMetricFamily R A →
  Metric.ParameterisedMetricLimitProblem
asMetricLimitProblem R A F = record
  { Parameter = Parameter F
  ; Index = Index F
  ; Value = CRS.Real R
  ; Epsilon = CRS.Real R
  ; _≼_ = _≼_ F
  ; Positive = positiveEpsilon R
  ; Close = closeWithin R
  ; family = family F
  ; candidate = candidate F
  ; reading = "Existing ConstructedOrderedCompleteReal with abs-induced metric."
  }

------------------------------------------------------------------------
-- Reverse obligations.  The real carrier supplies scalar/order/completeness
-- architecture; an application still owes the actual tail estimate and any
-- bridge from its regulator index into the sequence notion used by R.
------------------------------------------------------------------------

record ConstructiveRealMetricObligations
    (R : CRS.ConstructedOrderedCompleteReal)
    (A : CRT.ConstructedRealAbsoluteValueLaws R)
    (F : ConstructiveRealMetricFamily R A) : Set₁ where
  field
    cutoffOrderDirected : directedIndexSemantics F
    positiveEpsilonMatchesApplication : Set
    applicationDistanceIsConstructiveRealDistance : Set
    regulatorTailEstimate : Set
    candidateSameObject : Set
    regulatorToConstructiveSequenceBridge : Set
    reading : String

open ConstructiveRealMetricObligations public

------------------------------------------------------------------------
-- Sequential specialization.  This is the point at which the existing
-- cauchyLimit constructor can genuinely discharge completeness, provided the
-- application proves that its regulator family is represented by Sequence R
-- and that generic tail-Cauchy agrees with IsCauchy R.
------------------------------------------------------------------------

record ConstructiveRealSequentialFamily
    (R : CRS.ConstructedOrderedCompleteReal) : Set₁ where
  field
    Parameter : Set
    sequence : Parameter → CRS.Sequence R
    candidate : Parameter → CRS.Real R
    reading : String

open ConstructiveRealSequentialFamily public

record GenericToConstructiveCauchyWeld
    (R : CRS.ConstructedOrderedCompleteReal) : Set₁ where
  field
    genericTailCauchyCarrier : Set
    constructiveSequence : CRS.Sequence R
    genericTailCauchy : genericTailCauchyCarrier
    genericTailCauchyImpliesConstructiveIsCauchy :
      genericTailCauchyCarrier → CRS.IsCauchy R constructiveSequence
    reading : String

open GenericToConstructiveCauchyWeld public

constructiveCauchyHasLimit :
  (R : CRS.ConstructedOrderedCompleteReal) →
  (W : GenericToConstructiveCauchyWeld R) →
  Σ (CRS.Real R)
    (λ x → CRS.ConvergesTo R (constructiveSequence W) x)
constructiveCauchyHasLimit R W =
  CRS.cauchyLimit R
    (constructiveSequence W)
    (genericTailCauchyImpliesConstructiveIsCauchy W (genericTailCauchy W))

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ConstructiveRealCarrierAutomaticallySuppliesTailEstimate : Set where

data GenericMetricCauchyAutomaticallyEqualsConstructiveIsCauchy : Set where

constructiveRealDoesNotAutoSupplyTailEstimate :
  ConstructiveRealCarrierAutomaticallySuppliesTailEstimate → ⊥
constructiveRealDoesNotAutoSupplyTailEstimate ()

genericCauchyNeedsSameObjectWeld :
  GenericMetricCauchyAutomaticallyEqualsConstructiveIsCauchy → ⊥
genericCauchyNeedsSameObjectWeld ()

record ConstructiveRealMetricBridgeStatus : Set where
  field
    existingConstructiveRealSpineReused : Bool
    absMetricBridgeOwned : Bool
    cauchyLimitConstructorReused : Bool
    casimirTailEstimateProduced : Bool

    existingConstructiveRealSpineReusedIsTrue :
      existingConstructiveRealSpineReused ≡ true
    absMetricBridgeOwnedIsTrue : absMetricBridgeOwned ≡ true
    cauchyLimitConstructorReusedIsTrue : cauchyLimitConstructorReused ≡ true
    casimirTailEstimateProducedIsFalse : casimirTailEstimateProduced ≡ false

open ConstructiveRealMetricBridgeStatus public

canonicalConstructiveRealMetricBridgeStatus : ConstructiveRealMetricBridgeStatus
canonicalConstructiveRealMetricBridgeStatus = record
  { existingConstructiveRealSpineReused = true
  ; absMetricBridgeOwned = true
  ; cauchyLimitConstructorReused = true
  ; casimirTailEstimateProduced = false
  ; existingConstructiveRealSpineReusedIsTrue = refl
  ; absMetricBridgeOwnedIsTrue = refl
  ; cauchyLimitConstructorReusedIsTrue = refl
  ; casimirTailEstimateProducedIsFalse = refl
  }
