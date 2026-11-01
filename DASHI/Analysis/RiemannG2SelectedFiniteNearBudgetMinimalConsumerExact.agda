module DASHI.Analysis.RiemannG2SelectedFiniteNearBudgetMinimalConsumerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact as Window
import DASHI.Analysis.RiemannAristotlePoleQuotientFiniteNearEvaluationBidiExact as Eval
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Cast

------------------------------------------------------------------------
-- MINIMAL FINAL-CARRIER FINITE-NEAR BUDGET CONSUMER
--
-- The final Off consumer does not care which historical route label produced a
-- signed finite-near evaluation, nor does it require an upstream source-orbit
-- attachment once the theorem is attached to the exact target window itself.
--
-- The smallest theorem-bearing object is therefore indexed directly by one
-- PoleNearTargetWindow and contains:
--   * one signed finite-near evaluation;
--   * one theorem-bearing budget extraction;
--   * scalar identity;
--   * exact identity with that window's finitePoleNearSigned coordinate.
------------------------------------------------------------------------

record SelectedFiniteNearBudgetPayment
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (window : Window.PoleNearTargetWindow space formula)
    : Set₁ where
  field
    evaluation : Eval.SignedFiniteNearEvaluationSurface
    budget : Eval.EvaluationProducesBudget evaluation

    scalarCarrierIdentity :
      Eval.SignedFiniteNearEvaluationSurface.Scalar evaluation
      ≡ Weil.WeilTestSpace.Scalar space

    signedNearValueIsSelectedFiniteNear :
      Cast.cast scalarCarrierIdentity
        (Eval.SignedFiniteNearEvaluationSurface.signedNearValue evaluation)
      ≡ Window.PoleNearTargetWindow.finitePoleNearSigned window

    budgetToSelectedScalar :
      Eval.EvaluationProducesBudget.Budget budget ->
      Weil.WeilTestSpace.Scalar space

    SelectedUpper :
      Weil.WeilTestSpace.Scalar space ->
      Weil.WeilTestSpace.Scalar space ->
      Set

    evaluatorUpperBecomesSelectedUpper :
      Eval.EvaluationProducesBudget.ProducesRequiredUpper
        budget
        evaluation
        (Eval.EvaluationProducesBudget.nearBudget budget)
      ->
      SelectedUpper
        (Window.PoleNearTargetWindow.finitePoleNearSigned window)
        (budgetToSelectedScalar
          (Eval.EvaluationProducesBudget.nearBudget budget))

    paymentReference : String

open SelectedFiniteNearBudgetPayment public

selectedNearBudget :
  forall {space formula window} ->
  SelectedFiniteNearBudgetPayment space formula window ->
  Weil.WeilTestSpace.Scalar space
selectedNearBudget payment =
  budgetToSelectedScalar payment
    (Eval.EvaluationProducesBudget.nearBudget (budget payment))

selectedFiniteNearUpper :
  forall {space formula window} ->
  (payment : SelectedFiniteNearBudgetPayment space formula window) ->
  SelectedUpper payment
    (Window.PoleNearTargetWindow.finitePoleNearSigned window)
    (selectedNearBudget payment)
selectedFiniteNearUpper payment =
  evaluatorUpperBecomesSelectedUpper payment
    (Eval.EvaluationProducesBudget.producesRequiredUpper (budget payment))

------------------------------------------------------------------------
-- Existing FiniteNearProducer packages compile into the minimal payment once
-- the exact target-window identity/budget transport receipts are supplied.
-- Their route metadata remains audit information rather than a final-consumer
-- prerequisite.
------------------------------------------------------------------------

record FiniteProducerToMinimalPaymentBridge
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (window : Window.PoleNearTargetWindow space formula)
    (finite : Eval.FiniteNearProducer) : Set₁ where
  private
    evaluation0 = Eval.FiniteNearProducer.evaluation finite
    budget0 = Eval.FiniteNearProducer.budget finite
  field
    scalarCarrierIdentity :
      Eval.SignedFiniteNearEvaluationSurface.Scalar evaluation0
      ≡ Weil.WeilTestSpace.Scalar space

    signedNearValueIsSelectedFiniteNear :
      Cast.cast scalarCarrierIdentity
        (Eval.SignedFiniteNearEvaluationSurface.signedNearValue evaluation0)
      ≡ Window.PoleNearTargetWindow.finitePoleNearSigned window

    budgetToSelectedScalar :
      Eval.EvaluationProducesBudget.Budget budget0 ->
      Weil.WeilTestSpace.Scalar space

    SelectedUpper :
      Weil.WeilTestSpace.Scalar space ->
      Weil.WeilTestSpace.Scalar space ->
      Set

    evaluatorUpperBecomesSelectedUpper :
      Eval.EvaluationProducesBudget.ProducesRequiredUpper
        budget0 evaluation0 (Eval.EvaluationProducesBudget.nearBudget budget0)
      ->
      SelectedUpper
        (Window.PoleNearTargetWindow.finitePoleNearSigned window)
        (budgetToSelectedScalar
          (Eval.EvaluationProducesBudget.nearBudget budget0))

    bridgeReference : String

open FiniteProducerToMinimalPaymentBridge public

compileMinimalPaymentFromFiniteProducer :
  forall {space formula window finite} ->
  FiniteProducerToMinimalPaymentBridge
    space formula window finite ->
  SelectedFiniteNearBudgetPayment space formula window
compileMinimalPaymentFromFiniteProducer {finite = finite} bridge = record
  { evaluation = Eval.FiniteNearProducer.evaluation finite
  ; budget = Eval.FiniteNearProducer.budget finite
  ; scalarCarrierIdentity =
      FiniteProducerToMinimalPaymentBridge.scalarCarrierIdentity bridge
  ; signedNearValueIsSelectedFiniteNear =
      FiniteProducerToMinimalPaymentBridge.signedNearValueIsSelectedFiniteNear bridge
  ; budgetToSelectedScalar =
      FiniteProducerToMinimalPaymentBridge.budgetToSelectedScalar bridge
  ; SelectedUpper =
      FiniteProducerToMinimalPaymentBridge.SelectedUpper bridge
  ; evaluatorUpperBecomesSelectedUpper =
      FiniteProducerToMinimalPaymentBridge.evaluatorUpperBecomesSelectedUpper bridge
  ; paymentReference =
      FiniteProducerToMinimalPaymentBridge.bridgeReference bridge
  }

record SelectedFiniteNearMinimalConsumerBoundary : Set where
  constructor selected-finite-near-minimal-consumer-boundary
  field
    routeClassificationRequiredByFinalOffConsumer : Bool
    routeClassificationRequiredByFinalOffConsumerIsFalse :
      routeClassificationRequiredByFinalOffConsumer ≡ false

    sourceOrbitAttachmentRequiredAfterExactWindowAttachment : Bool
    sourceOrbitAttachmentRequiredAfterExactWindowAttachmentIsFalse :
      sourceOrbitAttachmentRequiredAfterExactWindowAttachment ≡ false

    finiteProducerPreservationMetadataRequiredAfterSameObjectAttachment : Bool
    finiteProducerPreservationMetadataRequiredAfterSameObjectAttachmentIsFalse :
      finiteProducerPreservationMetadataRequiredAfterSameObjectAttachment ≡ false

    evaluationAndBudgetAreTheoremBearingCore : Bool
    evaluationAndBudgetAreTheoremBearingCoreIsTrue :
      evaluationAndBudgetAreTheoremBearingCore ≡ true

    selectedSignedValueIdentityStillRequired : Bool
    selectedSignedValueIdentityStillRequiredIsTrue :
      selectedSignedValueIdentityStillRequired ≡ true

    richerFiniteProducerCompilesToMinimalPayment : Bool
    richerFiniteProducerCompilesToMinimalPaymentIsTrue :
      richerFiniteProducerCompilesToMinimalPayment ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalSelectedFiniteNearMinimalConsumerBoundary :
  SelectedFiniteNearMinimalConsumerBoundary
canonicalSelectedFiniteNearMinimalConsumerBoundary =
  selected-finite-near-minimal-consumer-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
    "For the authoritative final pole-quotient Off consumer, index the finite-near payment directly by the exact PoleNearTargetWindow. The minimal theorem-bearing object is one SignedFiniteNearEvaluationSurface plus its EvaluationProducesBudget, attached by exact scalar/signed-value identity to window.finitePoleNearSigned. Historical route classification, source-orbit attachment and preservation metadata remain useful provenance/audit information but are not terminal scalar-consumer prerequisites after exact window attachment. Any richer FiniteNearProducer can compile into this minimal payment. RH is not derived."
