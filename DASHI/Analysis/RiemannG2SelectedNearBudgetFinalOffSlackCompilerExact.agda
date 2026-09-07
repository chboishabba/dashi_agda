module DASHI.Analysis.RiemannG2SelectedNearBudgetFinalOffSlackCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannG2FkOrbitConsumerAttachmentExact as Orbit
import DASHI.Analysis.RiemannG2SelectedPoleNearSingleProducerBidiExact as Selected
import DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact as Window
import DASHI.Analysis.RiemannAristotlePoleQuotientFiniteNearEvaluationBidiExact as Eval
import DASHI.Analysis.RiemannG2SelectedPoleNearFiniteEvaluationSameObjectExact as SameObject
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2PoleQuotientOffIntermediateAllowanceCompilerExact as Intermediate
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Cast

------------------------------------------------------------------------
-- SELECTED FINITE-NEAR BUDGET -> FINAL OFF EPSILON-SLACK COMPILER
--
-- A generic finite-near evaluator may already carry a theorem-bearing budget.
-- The selected-window owner then transports that budget into the selected Weil
-- scalar. The final Off near/far compiler uses a possibly separately presented
-- scalar carrier. This file pays only the representation/order seam between
-- those views.
--
-- The analytic theorem remaining after this seam is explicit:
--
--   cast(selectedNearBudget) + epsilon <= A_off.
--
-- No determinant DirectSignedConsumerPayment is imported or promoted here.
------------------------------------------------------------------------

record SelectedNearBudgetFinalOffSlackBridge
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (orbit : Orbit.SourceFkOrbit)
    (selected : Selected.ActualSelectedPoleNearProducer space formula orbit)
    (finite : Eval.FiniteNearProducer)
    (attachment :
      SameObject.SelectedFiniteNearEvaluationAttachment
        space formula orbit selected finite)
    (transport :
      SameObject.SelectedFiniteNearBudgetTransport
        space formula orbit selected finite attachment)
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (d : NearFar.NearFarOffOrdinateBudget S)
    (assigned : NearFar.Scalar S) : Set₁ where
  field
    selectedScalarIdentity :
      Weil.WeilTestSpace.Scalar space ≡ NearFar.Scalar S

    selectedNearBudgetIsFinalNearBudget :
      Cast.cast selectedScalarIdentity
        (SameObject.selectedNearBudget transport)
      ≡ NearFar.nearBudget d

    selectedOrderTransport :
      {x y : Weil.WeilTestSpace.Scalar space} →
      SameObject.SelectedFiniteNearBudgetTransport.SelectedUpper transport x y →
      NearFar._≤_ S
        (Cast.cast selectedScalarIdentity x)
        (Cast.cast selectedScalarIdentity y)

    finalNearBudgetSelfOrder :
      NearFar._≤_ S
        (NearFar.nearBudget d)
        (NearFar.nearBudget d)

    intermediateFarAllowance : NearFar.Scalar S

    farBudgetBelowIntermediateAllowance :
      NearFar._≤_ S
        (NearFar.farBudget d)
        intermediateFarAllowance

    selectedNearBudgetPlusIntermediateBelowAssigned :
      NearFar._≤_ S
        (NearFar.add S
          (Cast.cast selectedScalarIdentity
            (SameObject.selectedNearBudget transport))
          intermediateFarAllowance)
        assigned

    bridgeReference : String

open SelectedNearBudgetFinalOffSlackBridge public

compiledSelectedUpperInFinalOrder :
  ∀ {space formula orbit selected finite attachment transport S d assigned} →
  (bridge :
    SelectedNearBudgetFinalOffSlackBridge
      space formula orbit selected finite attachment transport S d assigned) →
  NearFar._≤_ S
    (Cast.cast (selectedScalarIdentity bridge)
      (Window.PoleNearTargetWindow.finitePoleNearSigned
        (Selected.ActualSelectedPoleNearProducer.targetWindow selected)))
    (Cast.cast (selectedScalarIdentity bridge)
      (SameObject.selectedNearBudget transport))
compiledSelectedUpperInFinalOrder {transport = transport} bridge =
  selectedOrderTransport bridge
    (SameObject.selectedFiniteNearUpper transport)

compiledFinalNearPlusIntermediateBelowAssigned :
  ∀ {space formula orbit selected finite attachment transport S d assigned} →
  (bridge :
    SelectedNearBudgetFinalOffSlackBridge
      space formula orbit selected finite attachment transport S d assigned) →
  NearFar._≤_ S
    (NearFar.add S
      (NearFar.nearBudget d)
      (intermediateFarAllowance bridge))
    assigned
compiledFinalNearPlusIntermediateBelowAssigned bridge
  with selectedNearBudgetIsFinalNearBudget bridge
... | refl = selectedNearBudgetPlusIntermediateBelowAssigned bridge

compileIntermediateAllowanceFit :
  ∀ {space formula orbit selected finite attachment transport S d assigned} →
  SelectedNearBudgetFinalOffSlackBridge
    space formula orbit selected finite attachment transport S d assigned →
  Intermediate.IntermediateNearFarAllowanceFit S d assigned
compileIntermediateAllowanceFit bridge = record
  { Intermediate.intermediateFarAllowance = intermediateFarAllowance bridge
  ; Intermediate.nearBudgetSelfOrder = finalNearBudgetSelfOrder bridge
  ; Intermediate.farBudgetBelowIntermediateAllowance =
      farBudgetBelowIntermediateAllowance bridge
  ; Intermediate.nearBudgetPlusIntermediateBelowAssigned =
      compiledFinalNearPlusIntermediateBelowAssigned bridge
  }

compiledFinalNearPlusFarBelowAssigned :
  ∀ {space formula orbit selected finite attachment transport S d assigned} →
  (bridge :
    SelectedNearBudgetFinalOffSlackBridge
      space formula orbit selected finite attachment transport S d assigned) →
  NearFar._≤_ S
    (NearFar.add S
      (NearFar.nearBudget d)
      (NearFar.farBudget d))
    assigned
compiledFinalNearPlusFarBelowAssigned {S = S} {d = d} {assigned = assigned} bridge =
  Intermediate.compiledNearPlusFarBelowAssigned
    S d assigned (compileIntermediateAllowanceFit bridge)

record SelectedNearBudgetFinalOffSlackBoundary : Set where
  constructor selected-near-budget-final-off-slack-boundary
  field
    genericEvaluatorBudgetRequiresSecondAnalyticEvaluation : Bool
    genericEvaluatorBudgetRequiresSecondAnalyticEvaluationIsFalse :
      genericEvaluatorBudgetRequiresSecondAnalyticEvaluation ≡ false

    selectedBudgetExtractionIsRepresentationWork : Bool
    selectedBudgetExtractionIsRepresentationWorkIsTrue :
      selectedBudgetExtractionIsRepresentationWork ≡ true

    selectedOrderNeedsOneTransportToFinalOffOrder : Bool
    selectedOrderNeedsOneTransportToFinalOffOrderIsTrue :
      selectedOrderNeedsOneTransportToFinalOffOrder ≡ true

    selectedNearBudgetNeedsSameObjectIdentityWithFinalNearBudget : Bool
    selectedNearBudgetNeedsSameObjectIdentityWithFinalNearBudgetIsTrue :
      selectedNearBudgetNeedsSameObjectIdentityWithFinalNearBudget ≡ true

    determinantDirectConsumerPaymentRequiredByThisCompiler : Bool
    determinantDirectConsumerPaymentRequiredByThisCompilerIsFalse :
      determinantDirectConsumerPaymentRequiredByThisCompiler ≡ false

    liveAnalyticLeafIsSelectedNearBudgetPlusEpsilonBelowAssigned : Bool
    liveAnalyticLeafIsSelectedNearBudgetPlusEpsilonBelowAssignedIsTrue :
      liveAnalyticLeafIsSelectedNearBudgetPlusEpsilonBelowAssigned ≡ true

    finalNearPlusFarFitCompilesAfterBridge : Bool
    finalNearPlusFarFitCompilesAfterBridgeIsTrue :
      finalNearPlusFarFitCompilesAfterBridge ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalSelectedNearBudgetFinalOffSlackBoundary :
  SelectedNearBudgetFinalOffSlackBoundary
canonicalSelectedNearBudgetFinalOffSlackBoundary =
  selected-near-budget-final-off-slack-boundary
    false refl
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    "Do not recover a second signed evaluation after a FiniteNearProducer already carries one, and do not promote the determinant DirectSignedConsumerPayment into the final pole-quotient carrier. Transport the evaluator budget to the selected Weil scalar, identify that selected budget with the final near budget, and transport the selected upper relation once. The live scalar theorem is then exactly cast(B_near_selected)+epsilon <= A_off at the same chosen cutoff, while the owned far-tail channel pays B_far <= epsilon. From these, the intermediate-allowance compiler produces the final near+far fit. RH remains open."
