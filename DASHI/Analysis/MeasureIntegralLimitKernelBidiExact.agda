module DASHI.Analysis.MeasureIntegralLimitKernelBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GENERIC MEASURE / INTEGRAL / PARAMETERISED-LIMIT KERNEL, BIDI
--
-- This owner is theorem-shape infrastructure.  It does not provide a concrete
-- Lebesgue theory, dominated-convergence theorem, Fubini theorem, or physical
-- integral.  Applications must supply their own carriers and receipts.
--
-- The design cross-pollinates several repo patterns without importing any
-- application conclusion:
--   * Moonshine: regularisation parameter and domain-local convergence;
--   * Riemann: transform/interchange hypotheses kept distinct from output;
--   * Yang--Mills: cutoff-removal obligations exposed explicitly;
--   * Casimir: subtraction-before-limit and parameterised continuum passage.
------------------------------------------------------------------------

record MeasureIntegralProblem : Set₁ where
  field
    Parameter : Set
    Regulator : Set
    Point : Set
    Scalar : Set
    Integrand : Set
    Measure : Set

    measure : Measure
    regulatedIntegrand : Parameter → Regulator → Point → Integrand
    limitIntegrand : Parameter → Point → Integrand

    integrate : Measure → (Point → Integrand) → Scalar

    regulatedIntegral : Parameter → Regulator → Scalar
    limitIntegral : Parameter → Scalar

    regulatedIntegralLaw :
      (p : Parameter) → (r : Regulator) →
      regulatedIntegral p r ≡
      integrate measure (regulatedIntegrand p r)

    limitIntegralLaw :
      (p : Parameter) →
      limitIntegral p ≡ integrate measure (limitIntegrand p)

    reading : String

open MeasureIntegralProblem public

------------------------------------------------------------------------
-- Local analytic receipts.  These are deliberately independent: proving one
-- does not manufacture the others.
------------------------------------------------------------------------

record MeasurabilityIntegrabilityReceipt
    (P : MeasureIntegralProblem) : Set₁ where
  field
    Measurable : Integrand P → Set
    Integrable : (Point P → Integrand P) → Set

    regulatedMeasurable :
      (p : Parameter P) → (r : Regulator P) →
      (x : Point P) → Measurable (regulatedIntegrand P p r x)

    regulatedIntegrable :
      (p : Parameter P) → (r : Regulator P) →
      Integrable (regulatedIntegrand P p r)

    limitIntegrable :
      (p : Parameter P) → Integrable (limitIntegrand P p)

    receiptReading : String

open MeasurabilityIntegrabilityReceipt public

record DominatedLimitReceipt
    (P : MeasureIntegralProblem) : Set₁ where
  field
    Dominator : Parameter P → Point P → Integrand P
    Dominates : Integrand P → Integrand P → Set
    DominatorIntegrable : (p : Parameter P) → Set

    pointwiseDominated :
      (p : Parameter P) → (r : Regulator P) → (x : Point P) →
      Dominates (regulatedIntegrand P p r x) (Dominator p x)

    PointwiseLimit :
      (p : Parameter P) → (x : Point P) → Set

    pointwiseLimitReceipt :
      (p : Parameter P) → (x : Point P) → PointwiseLimit p x

    receiptReading : String

open DominatedLimitReceipt public

record ParameterisedIntegralLimitReceipt
    (P : MeasureIntegralProblem) : Set₁ where
  field
    LimitSemantics :
      (Parameter P → Regulator P → Scalar P) →
      (Parameter P → Scalar P) → Set

    regulatedIntegralsConverge :
      LimitSemantics (regulatedIntegral P) (limitIntegral P)

    convergenceUniformityOrLocalitySemantics : Set
    convergenceUniformityOrLocalityReceipt :
      convergenceUniformityOrLocalitySemantics

    receiptReading : String

open ParameterisedIntegralLimitReceipt public

------------------------------------------------------------------------
-- Interchange kernel.  This handles sum/integral, limit/integral, or another
-- application-defined pair of operations without pretending they are the same
-- theorem.
------------------------------------------------------------------------

record OperationInterchangeProblem : Set₁ where
  field
    Input : Set
    Intermediate : Set
    Output : Set

    leftFirst : Input → Intermediate
    rightSecond : Intermediate → Output

    rightFirst : Input → Intermediate
    leftSecond : Intermediate → Output

    admissible : Input → Set
    reading : String

open OperationInterchangeProblem public

record OperationInterchangeReceipt
    (P : OperationInterchangeProblem) : Set₁ where
  field
    interchangeEquality :
      (x : Input P) → admissible P x →
      rightSecond P (leftFirst P x) ≡
      leftSecond P (rightFirst P x)

    receiptReading : String

open OperationInterchangeReceipt public

------------------------------------------------------------------------
-- BIDI completion and reverse obligations.
------------------------------------------------------------------------

record MeasureIntegralLimitCompletion
    (P : MeasureIntegralProblem) : Set₁ where
  field
    integrability : MeasurabilityIntegrabilityReceipt P
    domination : DominatedLimitReceipt P
    parameterisedLimit : ParameterisedIntegralLimitReceipt P

open MeasureIntegralLimitCompletion public

record MeasureIntegralLimitObligations
    (P : MeasureIntegralProblem) : Set₁ where
  field
    measureSemanticsSameObject : Set
    regulatedIntegrandSameObject : Set
    measurableAndIntegrable : Set
    dominatingFamilyExists : Set
    dominationIsUniformEnoughForConsumer : Set
    pointwiseOrAppropriateLimitClosed : Set
    integrationLimitExchangeClosed : Set
    parameterDependenceControlled : Set
    regulatorRemovalClosed : Set

    obligationReading : String

open MeasureIntegralLimitObligations public

------------------------------------------------------------------------
-- Authority firewalls.
------------------------------------------------------------------------

data IntegrabilityAutomaticallyImpliesDomination : Set where

data DominationAutomaticallyImpliesLimitExchange : Set where

data FormalIntegralAutomaticallyImpliesConvergence : Set where

data ForeignIntegralReceiptClosesLocalApplication : Set where

integrabilityDoesNotAutoSupplyDomination :
  IntegrabilityAutomaticallyImpliesDomination → ⊥
integrabilityDoesNotAutoSupplyDomination ()

dominationDoesNotAutoSupplyLimitExchange :
  DominationAutomaticallyImpliesLimitExchange → ⊥
dominationDoesNotAutoSupplyLimitExchange ()

formalIntegralDoesNotAutoSupplyConvergence :
  FormalIntegralAutomaticallyImpliesConvergence → ⊥
formalIntegralDoesNotAutoSupplyConvergence ()

foreignIntegralReceiptCannotAutoCloseLocalApplication :
  ForeignIntegralReceiptClosesLocalApplication → ⊥
foreignIntegralReceiptCannotAutoCloseLocalApplication ()

------------------------------------------------------------------------
-- Machine-readable generic status.
------------------------------------------------------------------------

record MeasureIntegralKernelStatus : Set where
  field
    measureCarrierInterfaceOwned : Bool
    integrabilityReceiptInterfaceOwned : Bool
    dominationReceiptInterfaceOwned : Bool
    interchangeReceiptInterfaceOwned : Bool
    parameterisedLimitInterfaceOwned : Bool
    concreteMeasureTheoryProvedHere : Bool
    dominatedConvergenceTheoremProvedHere : Bool
    fubiniTonelliTheoremProvedHere : Bool

    measureCarrierInterfaceOwnedIsTrue : measureCarrierInterfaceOwned ≡ true
    integrabilityReceiptInterfaceOwnedIsTrue : integrabilityReceiptInterfaceOwned ≡ true
    dominationReceiptInterfaceOwnedIsTrue : dominationReceiptInterfaceOwned ≡ true
    interchangeReceiptInterfaceOwnedIsTrue : interchangeReceiptInterfaceOwned ≡ true
    parameterisedLimitInterfaceOwnedIsTrue : parameterisedLimitInterfaceOwned ≡ true
    concreteMeasureTheoryProvedHereIsFalse : concreteMeasureTheoryProvedHere ≡ false
    dominatedConvergenceTheoremProvedHereIsFalse : dominatedConvergenceTheoremProvedHere ≡ false
    fubiniTonelliTheoremProvedHereIsFalse : fubiniTonelliTheoremProvedHere ≡ false

open MeasureIntegralKernelStatus public

canonicalMeasureIntegralKernelStatus : MeasureIntegralKernelStatus
canonicalMeasureIntegralKernelStatus = record
  { measureCarrierInterfaceOwned = true
  ; integrabilityReceiptInterfaceOwned = true
  ; dominationReceiptInterfaceOwned = true
  ; interchangeReceiptInterfaceOwned = true
  ; parameterisedLimitInterfaceOwned = true
  ; concreteMeasureTheoryProvedHere = false
  ; dominatedConvergenceTheoremProvedHere = false
  ; fubiniTonelliTheoremProvedHere = false
  ; measureCarrierInterfaceOwnedIsTrue = refl
  ; integrabilityReceiptInterfaceOwnedIsTrue = refl
  ; dominationReceiptInterfaceOwnedIsTrue = refl
  ; interchangeReceiptInterfaceOwnedIsTrue = refl
  ; parameterisedLimitInterfaceOwnedIsTrue = refl
  ; concreteMeasureTheoryProvedHereIsFalse = refl
  ; dominatedConvergenceTheoremProvedHereIsFalse = refl
  ; fubiniTonelliTheoremProvedHereIsFalse = refl
  }
