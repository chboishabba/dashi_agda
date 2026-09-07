module DASHI.Analysis.RiemannG2SelectedFiniteNearBudgetMinimalConsumerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact as Window
import DASHI.Analysis.RiemannG2FkOrbitConsumerAttachmentExact as Orbit
import DASHI.Analysis.RiemannG2SelectedPoleNearSingleProducerBidiExact as Selected
import DASHI.Analysis.RiemannAristotlePoleQuotientFiniteNearEvaluationBidiExact as Eval
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Cast

------------------------------------------------------------------------
-- MINIMAL FINAL-CARRIER FINITE-NEAR BUDGET CONSUMER
--
-- The final Off consumer does not care which historical route label produced a
-- signed finite-near evaluation.  Once an evaluation and its theorem-bearing
-- budget are attached to the SAME selected finitePoleNearSigned value, route
-- classification/preservation metadata is no longer a logical prerequisite.
------------------------------------------------------------------------

record SelectedFiniteNearBudgetPayment
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (orbit : Orbit.SourceFkOrbit)
    (selected : Selected.ActualSelectedPoleNearProducer space formula orbit)
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
      ≡ Window.PoleNearTargetWindow.finitePoleNearSigned
          (Selected.ActualSelectedPoleNearProducer.targetWindow selected)

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
        (Window.PoleNearTargetWindow.finitePoleNearSigned
          (Selected.ActualSelectedPoleNearProducer.targetWindow selected))
        (budgetToSelectedScalar
          (Eval.EvaluationProducesBudget.nearBudget budget))

    paymentReference : String

open SelectedFiniteNearBudgetPayment public

selectedNearBudget :
  forall {space formula orbit selected} ->
  SelectedFiniteNearBudgetPayment space formula orbit selected ->
  Weil.WeilTestSpace.Scalar space
selectedNearBudget payment =
  budgetToSelectedScalar payment
    (Eval.EvaluationProducesBudget.nearBudget (budget payment))

selectedFiniteNearUpper :
  forall {space formula orbit selected} ->
  (payment : SelectedFiniteNearBudgetPayment space formula orbit selected) ->
  SelectedUpper payment
    (Window.PoleNearTargetWindow.finitePoleNearSigned
      (Selected.ActualSelectedPoleNearProducer.targetWindow selected))
    (selectedNearBudget payment)
selectedFiniteNearUpper payment =
  evaluatorUpperBecomesSelectedUpper payment
    (Eval.EvaluationProducesBudget.producesRequiredUpper (budget payment))

------------------------------------------------------------------------
-- Existing FiniteNearProducer packages compile into the minimal payment once
-- the selected same-object/budget transport receipts are supplied.  This keeps
-- the older richer route as a lawful compatibility source without making its
-- route metadata part of the final consumer API.
------------------------------------------------------------------------

record FiniteProducerToMinimalPaymentBridge
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (orbit : Orbit.SourceFkOrbit)
    (selected : Selected.ActualSelectedPoleNearProducer space formula orbit)
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
      ≡ Window.PoleNearTargetWindow.finitePoleNearSigned
          (Selected.ActualSelectedPoleNearProducer.targetWindow selected)

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
        (Window.PoleNearTargetWindow.finitePoleNearSigned
          (Selected.ActualSelectedPoleNearProducer.targetWindow selected))
        (budgetToSelectedScalar
          (Eval.EvaluationProducesBudget.nearBudget budget0))

    bridgeReference : String

open FiniteProducerToMinimalPaymentBridge public

compileMinimalPaymentFromFiniteProducer :
  forall {space formula orbit selected finite} ->
  FiniteProducerToMinimalPaymentBridge
    space formula orbit selected finite ->
  SelectedFiniteNearBudgetPayment space formula orbit selected
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
    true refl
    true refl
    true refl
    false refl
    "For the authoritative final pole-quotient Off consumer, the minimal finite-near theorem-bearing object is one SignedFiniteNearEvaluationSurface plus its EvaluationProducesBudget, attached by exact scalar/signed-value identity to the selected finitePoleNearSigned coordinate. Historical route classification and preservation metadata remain useful audit information but are not final-consumer prerequisites after same-object attachment. Any richer FiniteNearProducer can compile into this minimal payment. RH is not derived."
