module DASHI.Core.CoarseUnitFineFibreCapacityExact where

------------------------------------------------------------------------
-- COARSE UNIT / FINE FIBRE CAPACITY
--
-- A single coarse observation can sit over an arbitrarily large finite fibre.
-- This module does NOT claim automatic semantic or physical amplification.
--
-- The load-bearing statement is conditional:
--
--   one coarse class
--   + k fine representatives that remain future-distinct
--   + a dynamically sufficient residual
--   => the residual must distinguish those k representatives.
--
-- Thus "one added coarse coordinate exposes a large fine fibre" is a carrier
-- statement; consumer/future relevance still requires a separation witness.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Fin.Base using (Fin)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.GeneralResidualFibreCardinalityExact as Cardinality
import DASHI.Core.ResidualFibreLowerBoundExact as Lower
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.JCoarseFineEvaluationFibreExact as JEval
import DASHI.Moonshine.Base369MonsterTwoComponentCompletionBidiExact as MonsterPlusOne

------------------------------------------------------------------------
-- 1. Canonical one-coarse-unit / k-fine-state carrier.
------------------------------------------------------------------------

CoarseUnitFineState : Nat -> Set
CoarseUnitFineState k = ⊤ × Fin k

coarseUnitProject :
  {k : Nat} ->
  CoarseUnitFineState k ->
  ⊤
coarseUnitProject state = tt

fineIndex :
  {k : Nat} ->
  CoarseUnitFineState k ->
  Fin k
fineIndex = proj₂

sameCoarseUnit :
  {k : Nat} ->
  (left right : CoarseUnitFineState k) ->
  coarseUnitProject left ≡ coarseUnitProject right
sameCoarseUnit left right = refl

fineIndexSeparatesState :
  {k : Nat} ->
  (left right : CoarseUnitFineState k) ->
  fineIndex left ≡ fineIndex right ->
  left ≡ right
fineIndexSeparatesState (tt , left) (tt , right) same
  rewrite same = refl

coarseUnitConsumerIsLeastFineObserver :
  {k : Nat} ->
  Descent.LeastSufficientConsumerObserver
    (fineIndex {k})
coarseUnitConsumerIsLeastFineObserver =
  Descent.canonicalConsumerObserverIsLeast fineIndex

------------------------------------------------------------------------
-- 2. The whole Fin k fibre can be represented over one coarse unit.
------------------------------------------------------------------------

equalityFutureFibre :
  (k : Nat) ->
  Cardinality.FiniteFutureDistinctFibre
    k
    (_≡_ {A = CoarseUnitFineState k})
    coarseUnitProject
equalityFutureFibre k =
  Cardinality.finiteFutureDistinctFibre
    (λ index -> tt , index)
    tt
    (λ index -> refl)
    (λ sameState -> cong proj₂ sameState)

futureSafeResidualMustInjectOnFineFibre :
  {k : Nat} ->
  {Residual : Set} ->
  {residual : CoarseUnitFineState k -> Residual} ->
  (safe :
    Lower.DynamicallySufficientPair
      (CoarseUnitFineState k)
      ⊤
      Residual
      (_≡_)
      coarseUnitProject
      residual) ->
  Cardinality.Injective
    (λ index -> residual (tt , index))
futureSafeResidualMustInjectOnFineFibre {k} safe =
  Cardinality.residualInjectionFromFutureDistinctFibre
    safe
    (equalityFutureFibre k)

futureSafeBitResidualNeedsAtLeastFineCapacity :
  {k bits : Nat} ->
  {residual :
    CoarseUnitFineState k ->
    Cardinality.BitWords bits} ->
  (safe :
    Lower.DynamicallySufficientPair
      (CoarseUnitFineState k)
      ⊤
      (Cardinality.BitWords bits)
      (_≡_)
      coarseUnitProject
      residual) ->
  k ≤ Cardinality.pow2 bits
futureSafeBitResidualNeedsAtLeastFineCapacity {k} safe =
  Cardinality.futureSafetyForBitWordsImpliesCapacityBound
    safe
    (equalityFutureFibre k)

------------------------------------------------------------------------
-- 3. J/369 instance: one completion channel carries a 3^9 fine-frequency
--    coordinate in the elementary harmonic carrier.
--
-- IMPORTANT: JCoarseFineEvaluationFibreExact explicitly blocks the stronger
-- claim that a fixed-value assignment fibre has cardinality 3^9.  We reuse the
-- elementary completion-sector dimension and evaluation-codomain dimension,
-- not that prohibited cardinality claim.
------------------------------------------------------------------------

jFineCoordinateCount : Nat
jFineCoordinateCount = Harmonic.fineFrequencyDimension

jFineCoordinateCountIs19683 :
  jFineCoordinateCount ≡ 19683
jFineCoordinateCountIs19683 = refl

jCompletionElementarySectorHas19683Coordinates :
  Harmonic.completionHarmonicDimension ≡ 19683
jCompletionElementarySectorHas19683Coordinates =
  Harmonic.completionHarmonicDimensionIsThreePowerNine

coarseJUnitContributionAgreesWithFineCoordinateCount :
  MonsterPlusOne.unitContribution MonsterPlusOne.coarseJCompletionUnit
  ≡ jFineCoordinateCount
coarseJUnitContributionAgreesWithFineCoordinateCount = refl

fixedJValueFibreCardinalityNotPromoted :
  JEval.fixedValueAssignmentFibreHasCardinalityThreePowerNine
    JEval.canonicalJCoarseFineEvaluationBoundary
  ≡ false
fixedJValueFibreCardinalityNotPromoted = refl

------------------------------------------------------------------------
-- 4. Interpretation boundary.
------------------------------------------------------------------------

record CoarseUnitFineFibreCapacityBoundary : Set where
  constructor coarse-unit-fine-fibre-capacity-boundary
  field
    oneCoarseUnitCanIndexFiniteFineFibre : Bool
    futureDistinctFineStatesForceResidualInjection : Bool
    bitResidualCapacityBoundReused : Bool
    jCompletionFineCoordinateCountReused : Bool
    fixedJValueFibreClaimedToHave19683Assignments : Bool
    fixedJValueFibreClaimedToHave19683AssignmentsIsFalse :
      fixedJValueFibreClaimedToHave19683Assignments ≡ false
    oneExtraCoarseCoordinateAutomaticallyImprovesEveryConsumer : Bool
    oneExtraCoarseCoordinateAutomaticallyImprovesEveryConsumerIsFalse :
      oneExtraCoarseCoordinateAutomaticallyImprovesEveryConsumer ≡ false
    fineFibreSizeAloneCreatesPhysicalMechanism : Bool
    fineFibreSizeAloneCreatesPhysicalMechanismIsFalse :
      fineFibreSizeAloneCreatesPhysicalMechanism ≡ false

canonicalCoarseUnitFineFibreCapacityBoundary :
  CoarseUnitFineFibreCapacityBoundary
canonicalCoarseUnitFineFibreCapacityBoundary =
  coarse-unit-fine-fibre-capacity-boundary
    true true true true
    false refl
    false refl
    false refl
