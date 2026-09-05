module DASHI.Physics.QuantumVacuum.ParallelPlatePolarBishopTrigReuseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.BishopConcreteTrigonometricDerivativeBidiExact as Trig
import DASHI.Physics.QuantumVacuum.ParallelPlatePolarJacobianBidiExact as Polar

------------------------------------------------------------------------
-- ROUND11 BISHOP TRIG -> CASIMIR POLAR DERIVATIVE ENTRIES
--
-- The upstream trig compiler now owns:
--   * concrete signed-term identification,
--   * finite power differentiation,
--   * inverse-factorial coefficient cancellation,
--   * sine/cosine finite-term differentiation,
--   * convergence of the differentiated term series to cosine / -sine.
--
-- The Casimir polar consumer therefore owes only:
--   1. the derivative/series interchange theorem on that literal Bishop series;
--   2. ordinary constant/product-rule semantics identifying derivatives of
--        x(r,theta) = r cos(theta), y(r,theta) = r sin(theta)
--      with the four polar Jacobian entries.
------------------------------------------------------------------------

record PolarBishopTrigConsumer : Set₁ where
  field
    trigProblem : Trig.ConcreteBishopTrigDerivativeProblem

    polarConstantProductRuleSemantics : Set

    buildTrigReceipt :
      Trig.derivativeSeriesInterchange trigProblem →
      Trig.ConcreteBishopTrigDerivativeReceipt trigProblem

    buildPolarDerivativeReceipt :
      Trig.ConcreteBishopTrigDerivativeReceipt trigProblem →
      polarConstantProductRuleSemantics →
      Polar.ConstructedPolarDerivativeReceipt

    reading : String

open PolarBishopTrigConsumer public

record PolarBishopTrigClosure
    (C : PolarBishopTrigConsumer) : Set₁ where
  field
    derivativeSeriesInterchangeClosed :
      Trig.derivativeSeriesInterchange (trigProblem C)
    polarConstantProductRuleClosed : polarConstantProductRuleSemantics C

open PolarBishopTrigClosure public

compileTrigReceipt :
  ∀ {C} →
  PolarBishopTrigClosure C →
  Trig.ConcreteBishopTrigDerivativeReceipt (trigProblem C)
compileTrigReceipt {C} closure =
  buildTrigReceipt C (derivativeSeriesInterchangeClosed closure)

compilePolarDerivativeReceipt :
  ∀ {C} →
  (closure : PolarBishopTrigClosure C) →
  Polar.ConstructedPolarDerivativeReceipt
compilePolarDerivativeReceipt {C} closure =
  buildPolarDerivativeReceipt C
    (compileTrigReceipt closure)
    (polarConstantProductRuleClosed closure)

record ReversePolarBishopTrigObligations : Set where
  field
    round11BishopSeriesSelected : Set
    derivativeSeriesInterchange : Set
    polarConstantProductRuleSemantics : Set

open ReversePolarBishopTrigObligations public

data FiniteTrigAlgebraAutomaticallySuppliesPolarProductRule : Set where

data PolarProductRuleAutomaticallySuppliesSeriesInterchange : Set where

noFiniteToPolarRuleLeak :
  FiniteTrigAlgebraAutomaticallySuppliesPolarProductRule → ⊥
noFiniteToPolarRuleLeak ()

noPolarRuleToInterchangeLeak :
  PolarProductRuleAutomaticallySuppliesSeriesInterchange → ⊥
noPolarRuleToInterchangeLeak ()

record Status : Set where
  field
    finiteTrigTermDerivativeOwned : Bool
    derivedTrigSeriesConvergenceOwned : Bool
    polarConsumerCompilerOwned : Bool
    derivativeSeriesInterchangeClosed : Bool
    polarConstantProductRuleClosed : Bool

    finiteTrigTermDerivativeOwnedIsTrue : finiteTrigTermDerivativeOwned ≡ true
    derivedTrigSeriesConvergenceOwnedIsTrue : derivedTrigSeriesConvergenceOwned ≡ true
    polarConsumerCompilerOwnedIsTrue : polarConsumerCompilerOwned ≡ true
    derivativeSeriesInterchangeClosedIsFalse : derivativeSeriesInterchangeClosed ≡ false
    polarConstantProductRuleClosedIsFalse : polarConstantProductRuleClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { finiteTrigTermDerivativeOwned = true
  ; derivedTrigSeriesConvergenceOwned = true
  ; polarConsumerCompilerOwned = true
  ; derivativeSeriesInterchangeClosed = false
  ; polarConstantProductRuleClosed = false
  ; finiteTrigTermDerivativeOwnedIsTrue = refl
  ; derivedTrigSeriesConvergenceOwnedIsTrue = refl
  ; polarConsumerCompilerOwnedIsTrue = refl
  ; derivativeSeriesInterchangeClosedIsFalse = refl
  ; polarConstantProductRuleClosedIsFalse = refl
  }
