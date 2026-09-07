module DASHI.Analysis.RiemannG2MinimalNearBudgetFinalOffSlackCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact as Window
import DASHI.Analysis.RiemannG2SelectedFiniteNearBudgetMinimalConsumerExact as Minimal
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2PoleQuotientOffIntermediateAllowanceCompilerExact as Intermediate
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Cast

------------------------------------------------------------------------
-- MINIMAL TARGET-WINDOW NEAR BUDGET -> FINAL OFF EPSILON-SLACK
--
-- This is the preferred final-carrier bridge.  It does not require a richer
-- FiniteNearProducer, selected source-orbit producer, or route classification.
-- The analytic input is exactly the target-window budget plus epsilon fit;
-- everything else is representation/order or the independently-owned far tail.
------------------------------------------------------------------------

record MinimalNearFinalOffSlackBridge
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (window : Window.PoleNearTargetWindow space formula)
    (payment : Minimal.SelectedFiniteNearBudgetPayment space formula window)
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (d : NearFar.NearFarOffOrdinateBudget S)
    (assigned : NearFar.Scalar S) : Set₁ where
  field
    selectedScalarIdentity :
      Weil.WeilTestSpace.Scalar space ≡ NearFar.Scalar S

    selectedNearBudgetIsFinalNearBudget :
      Cast.cast selectedScalarIdentity
        (Minimal.selectedNearBudget payment)
      ≡ NearFar.nearBudget d

    selectedOrderTransport :
      {x y : Weil.WeilTestSpace.Scalar space} ->
      Minimal.SelectedFiniteNearBudgetPayment.SelectedUpper payment x y ->
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
            (Minimal.selectedNearBudget payment))
          intermediateFarAllowance)
        assigned

    bridgeReference : String

open MinimalNearFinalOffSlackBridge public

compiledSelectedUpperInFinalOrder :
  forall {space formula window payment S d assigned} ->
  (bridge :
    MinimalNearFinalOffSlackBridge
      space formula window payment S d assigned) ->
  NearFar._≤_ S
    (Cast.cast (selectedScalarIdentity bridge)
      (Window.PoleNearTargetWindow.finitePoleNearSigned window))
    (Cast.cast (selectedScalarIdentity bridge)
      (Minimal.selectedNearBudget payment))
compiledSelectedUpperInFinalOrder {payment = payment} bridge =
  selectedOrderTransport bridge (Minimal.selectedFiniteNearUpper payment)

compiledFinalNearPlusIntermediateBelowAssigned :
  forall {space formula window payment S d assigned} ->
  (bridge :
    MinimalNearFinalOffSlackBridge
      space formula window payment S d assigned) ->
  NearFar._≤_ S
    (NearFar.add S
      (NearFar.nearBudget d)
      (intermediateFarAllowance bridge))
    assigned
compiledFinalNearPlusIntermediateBelowAssigned bridge
  with selectedNearBudgetIsFinalNearBudget bridge
... | refl = selectedNearBudgetPlusIntermediateBelowAssigned bridge

compileIntermediateAllowanceFit :
  forall {space formula window payment S d assigned} ->
  MinimalNearFinalOffSlackBridge
    space formula window payment S d assigned ->
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
  forall {space formula window payment S d assigned} ->
  (bridge :
    MinimalNearFinalOffSlackBridge
      space formula window payment S d assigned) ->
  NearFar._≤_ S
    (NearFar.add S
      (NearFar.nearBudget d)
      (NearFar.farBudget d))
    assigned
compiledFinalNearPlusFarBelowAssigned {S = S} {d = d} {assigned = assigned} bridge =
  Intermediate.compiledNearPlusFarBelowAssigned
    S d assigned (compileIntermediateAllowanceFit bridge)

record MinimalNearFinalOffSlackBoundary : Set where
  constructor minimal-near-final-off-slack-boundary
  field
    finiteNearRouteMetadataRequired : Bool
    finiteNearRouteMetadataRequiredIsFalse :
      finiteNearRouteMetadataRequired ≡ false

    sourceOrbitProducerRequired : Bool
    sourceOrbitProducerRequiredIsFalse : sourceOrbitProducerRequired ≡ false

    targetWindowBudgetSameObjectIdentityRequired : Bool
    targetWindowBudgetSameObjectIdentityRequiredIsTrue :
      targetWindowBudgetSameObjectIdentityRequired ≡ true

    oneSelectedOrderTransportRequired : Bool
    oneSelectedOrderTransportRequiredIsTrue :
      oneSelectedOrderTransportRequired ≡ true

    farTailEstimateReprovedHere : Bool
    farTailEstimateReprovedHereIsFalse : farTailEstimateReprovedHere ≡ false

    liveAnalyticScalarLeaf : Bool
    liveAnalyticScalarLeafIsTrue : liveAnalyticScalarLeaf ≡ true

    jointNearFarFitIsCompilerOutput : Bool
    jointNearFarFitIsCompilerOutputIsTrue :
      jointNearFarFitIsCompilerOutput ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalMinimalNearFinalOffSlackBoundary : MinimalNearFinalOffSlackBoundary
canonicalMinimalNearFinalOffSlackBoundary =
  minimal-near-final-off-slack-boundary
    false refl
    false refl
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    "The preferred final Off route consumes the minimal target-window finite-near budget payment, not a historical route-classified FiniteNearProducer or source-orbit producer. After exact target-window budget identity and one order transport, the only new scalar analytic payment is cast(B_near_window)+epsilon <= A_off at the same final cutoff; the far-tail channel supplies B_far <= epsilon independently. The intermediate-allowance compiler then produces B_near+B_far <= A_off. RH remains open."
