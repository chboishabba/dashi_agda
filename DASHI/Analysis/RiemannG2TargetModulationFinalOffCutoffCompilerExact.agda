module DASHI.Analysis.RiemannG2TargetModulationFinalOffCutoffCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannAristotlePoleNearTargetModulationExact as Target
import DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact as Window
import DASHI.Analysis.RiemannG2PoleNearTargetWindowSpectralIdentificationCompilerExact as WindowId
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2PoleQuotientOffIntermediateAllowanceCompilerExact as Intermediate
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Cast

------------------------------------------------------------------------
-- SOURCE-NATIVE f_{t,J} CUTOFF -> FINAL OFF CUTOFF
--
-- PoleNearTargetModulation already owns the typed Cutoff carrier and the actual
-- cutoff used to construct the selected test:
--
--   modulatedPoleTest = windowAt cutoff (modulateAt target basePoleTest).
--
-- SameLiteralPoleNearWindowAttachment identifies the theorem-bearing target
-- window's selected test with that same modulatedPoleTest. Therefore the final
-- Off route should reuse this J rather than minting a second selected cutoff.
------------------------------------------------------------------------

record TargetModulationFinalOffCutoffBridge
    {space : Weil.WeilTestSpace}
    {formula : Explicit.RiemannExplicitFormula space}
    (m : Target.PoleNearTargetModulation space)
    (w : Window.PoleNearTargetWindow space formula)
    (sameWindow : WindowId.SameLiteralPoleNearWindowAttachment m w)
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (input : Intermediate.DirectPoleQuotientOffIntermediateAllowanceInput S)
    : Set₁ where
  field
    modulationCutoffCarrierIdentity :
      Target.PoleNearTargetModulation.Cutoff m
      ≡ Intermediate.DirectPoleQuotientOffIntermediateAllowanceInput.Cutoff input

    modulationCutoffIsFinalChosenCutoff :
      Cast.cast modulationCutoffCarrierIdentity
        (Target.PoleNearTargetModulation.cutoff m)
      ≡ Intermediate.DirectPoleQuotientOffIntermediateAllowanceInput.chosenCutoff input

    cutoffBridgeReference : String

open TargetModulationFinalOffCutoffBridge public

selectedWindowIsSourceNativeModulatedTest :
  ∀ {space formula}
    {m : Target.PoleNearTargetModulation space}
    {w : Window.PoleNearTargetWindow space formula}
    {sameWindow S input} →
  TargetModulationFinalOffCutoffBridge m w sameWindow S input →
  Window.PoleNearTargetWindow.targetWindowTest w
    ≡ Target.PoleNearTargetModulation.modulatedPoleTest m
selectedWindowIsSourceNativeModulatedTest {sameWindow = sameWindow} bridge =
  WindowId.sameSelectedTest sameWindow

compiledFinalChosenCutoffCrossing :
  ∀ {space formula}
    {m : Target.PoleNearTargetModulation space}
    {w : Window.PoleNearTargetWindow space formula}
    {sameWindow S input} →
  TargetModulationFinalOffCutoffBridge m w sameWindow S input →
  Intermediate.DirectPoleQuotientOffIntermediateAllowanceInput.CrossingCutoff input
    (Intermediate.DirectPoleQuotientOffIntermediateAllowanceInput.chosenCutoff input)
compiledFinalChosenCutoffCrossing {input = input} bridge =
  Intermediate.DirectPoleQuotientOffIntermediateAllowanceInput.chosenCutoffCrosses input

record TargetModulationFinalOffCutoffBoundary : Set where
  constructor target-modulation-final-off-cutoff-boundary
  field
    sourceNativeTargetModulationAlreadyOwnsTypedCutoff : Bool
    sourceNativeTargetModulationAlreadyOwnsTypedCutoffIsTrue :
      sourceNativeTargetModulationAlreadyOwnsTypedCutoff ≡ true

    selectedTargetWindowCanBeIdentifiedWithSameModulatedTest : Bool
    selectedTargetWindowCanBeIdentifiedWithSameModulatedTestIsTrue :
      selectedTargetWindowCanBeIdentifiedWithSameModulatedTest ≡ true

    secondSelectedCutoffOntologyRequired : Bool
    secondSelectedCutoffOntologyRequiredIsFalse :
      secondSelectedCutoffOntologyRequired ≡ false

    directProducerCutoffIsPreferredSourceOfSelectedJ : Bool
    directProducerCutoffIsPreferredSourceOfSelectedJIsFalse :
      directProducerCutoffIsPreferredSourceOfSelectedJ ≡ false

    finalCutoffCarrierAndValueIdentityStillRequired : Bool
    finalCutoffCarrierAndValueIdentityStillRequiredIsTrue :
      finalCutoffCarrierAndValueIdentityStillRequired ≡ true

    crossingReceiptAlreadyOwnedByFinalInput : Bool
    crossingReceiptAlreadyOwnedByFinalInputIsTrue :
      crossingReceiptAlreadyOwnedByFinalInput ≡ true

    newAnalyticEstimateIntroduced : Bool
    newAnalyticEstimateIntroducedIsFalse :
      newAnalyticEstimateIntroduced ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalTargetModulationFinalOffCutoffBoundary :
  TargetModulationFinalOffCutoffBoundary
canonicalTargetModulationFinalOffCutoffBoundary =
  target-modulation-final-off-cutoff-boundary
    true refl
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "Use PoleNearTargetModulation.cutoff as the source-native typed J of f_{t,J}. SameLiteralPoleNearWindowAttachment identifies the theorem-bearing PoleNearTargetWindow test with that same modulated test, so do not invent another selected cutoff. The only remaining cutoff seam is typed carrier/value identity into the final Off input; its crossing receipt is already present there. The direct-producer cutoff bridge remains a compatibility route, not the preferred source of J. No new analytic estimate and no RH theorem are introduced."
