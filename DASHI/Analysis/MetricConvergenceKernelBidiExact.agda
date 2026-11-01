module DASHI.Analysis.MetricConvergenceKernelBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GENERIC METRIC / EPSILON CONVERGENCE KERNEL, BIDI
--
-- Constructive theorem shape for parameterised regulator limits.  No concrete
-- real numbers, norm, metric completeness, or asymptotic estimate is assumed.
------------------------------------------------------------------------

record ParameterisedMetricLimitProblem : Set₁ where
  field
    Parameter : Set
    Index : Set
    Value : Set
    Epsilon : Set

    _≼_ : Index → Index → Set
    Positive : Epsilon → Set
    Close : Value → Value → Epsilon → Set

    family : Parameter → Index → Value
    candidate : Parameter → Value

    reading : String

open ParameterisedMetricLimitProblem public

record PointwiseMetricConvergence
    (P : ParameterisedMetricLimitProblem) : Set₁ where
  field
    threshold : Parameter P → Epsilon P → Index P

    tailClose :
      (p : Parameter P) →
      (ε : Epsilon P) →
      Positive P ε →
      (i : Index P) →
      _≼_ P (threshold p ε) i →
      Close P (family P p i) (candidate P p) ε

    convergenceReading : String

open PointwiseMetricConvergence public

record UniformMetricConvergence
    (P : ParameterisedMetricLimitProblem) : Set₁ where
  field
    threshold : Epsilon P → Index P

    uniformTailClose :
      (ε : Epsilon P) →
      Positive P ε →
      (p : Parameter P) →
      (i : Index P) →
      _≼_ P (threshold ε) i →
      Close P (family P p i) (candidate P p) ε

    convergenceReading : String

open UniformMetricConvergence public

record MetricCauchyReceipt
    (P : ParameterisedMetricLimitProblem) : Set₁ where
  field
    cauchyThreshold : Parameter P → Epsilon P → Index P

    tailCauchy :
      (p : Parameter P) →
      (ε : Epsilon P) →
      Positive P ε →
      (i j : Index P) →
      _≼_ P (cauchyThreshold p ε) i →
      _≼_ P (cauchyThreshold p ε) j →
      Close P (family P p i) (family P p j) ε

    cauchyReading : String

open MetricCauchyReceipt public

------------------------------------------------------------------------
-- Completeness is a separate payment.  A Cauchy receipt cannot manufacture a
-- candidate limit without a completeness/closure theorem for the value space.
------------------------------------------------------------------------

record CompletenessBridge
    (P : ParameterisedMetricLimitProblem)
    (cauchy : MetricCauchyReceipt P) : Set₁ where
  field
    ValueCompleteForFamily : Set
    valueCompleteForFamily : ValueCompleteForFamily
    candidateIsCauchyLimit : PointwiseMetricConvergence P
    bridgeReading : String

open CompletenessBridge public

------------------------------------------------------------------------
-- Reverse consumer obligations.
------------------------------------------------------------------------

record MetricLimitObligations
    (P : ParameterisedMetricLimitProblem) : Set₁ where
  field
    directedIndexSemantics : Set
    positiveEpsilonSemantics : Set
    closeRelationIsMetricLikeEnough : Set
    candidateSameObject : Set
    tailEstimate : Set
    parameterDependenceControlled : Set
    completenessIfUsingCauchyRoute : Set
    obligationReading : String

open MetricLimitObligations public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CauchyAutomaticallyImpliesConvergent : Set where

data PointwiseAutomaticallyImpliesUniform : Set where

data SymbolicCandidateAutomaticallyIsLimit : Set where

cauchyDoesNotAutoSupplyLimit :
  CauchyAutomaticallyImpliesConvergent → ⊥
cauchyDoesNotAutoSupplyLimit ()

pointwiseDoesNotAutoSupplyUniform :
  PointwiseAutomaticallyImpliesUniform → ⊥
pointwiseDoesNotAutoSupplyUniform ()

symbolicCandidateDoesNotAutoSupplyLimit :
  SymbolicCandidateAutomaticallyIsLimit → ⊥
symbolicCandidateDoesNotAutoSupplyLimit ()

record MetricConvergenceKernelStatus : Set where
  field
    pointwiseMetricLimitShapeOwned : Bool
    uniformMetricLimitShapeOwned : Bool
    cauchyShapeOwned : Bool
    completenessBridgeShapeOwned : Bool
    concreteRealMetricOwned : Bool
    concreteCompletenessTheoremOwned : Bool

    pointwiseMetricLimitShapeOwnedIsTrue : pointwiseMetricLimitShapeOwned ≡ true
    uniformMetricLimitShapeOwnedIsTrue : uniformMetricLimitShapeOwned ≡ true
    cauchyShapeOwnedIsTrue : cauchyShapeOwned ≡ true
    completenessBridgeShapeOwnedIsTrue : completenessBridgeShapeOwned ≡ true
    concreteRealMetricOwnedIsFalse : concreteRealMetricOwned ≡ false
    concreteCompletenessTheoremOwnedIsFalse : concreteCompletenessTheoremOwned ≡ false

open MetricConvergenceKernelStatus public

canonicalMetricConvergenceKernelStatus : MetricConvergenceKernelStatus
canonicalMetricConvergenceKernelStatus = record
  { pointwiseMetricLimitShapeOwned = true
  ; uniformMetricLimitShapeOwned = true
  ; cauchyShapeOwned = true
  ; completenessBridgeShapeOwned = true
  ; concreteRealMetricOwned = false
  ; concreteCompletenessTheoremOwned = false
  ; pointwiseMetricLimitShapeOwnedIsTrue = refl
  ; uniformMetricLimitShapeOwnedIsTrue = refl
  ; cauchyShapeOwnedIsTrue = refl
  ; completenessBridgeShapeOwnedIsTrue = refl
  ; concreteRealMetricOwnedIsFalse = refl
  ; concreteCompletenessTheoremOwnedIsFalse = refl
  }
