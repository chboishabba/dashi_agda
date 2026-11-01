module DASHI.Analysis.RiemannG2WindowBudgetToTransportedNearUpperExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact as Window
import DASHI.Analysis.RiemannG2SelectedFiniteNearBudgetMinimalConsumerExact as Minimal
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Cast

------------------------------------------------------------------------
-- TARGET-WINDOW BUDGET -> TRANSPORTED CHOSEN-CUTOFF NEAR UPPER
--
-- This owner is purely a same-object/order bridge.  It does not evaluate the
-- finite near sum again.  A minimal target-window payment already contains the
-- theorem-bearing upper; we identify its value and budget with the transported
-- cutoff coordinates and move that one inequality into the final Agda order.
------------------------------------------------------------------------

record WindowBudgetTransportAttachment
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (window : Window.PoleNearTargetWindow space formula)
    (payment : Minimal.SelectedFiniteNearBudgetPayment space formula window)
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (transport : Transport.ExplicitCutoffNearFarAgdaTransport S)
    (J : Transport.Cutoff transport) : Set₁ where
  field
    scalarCarrierIdentity :
      Weil.WeilTestSpace.Scalar space ≡ NearFar.Scalar S

    windowFiniteNearIsTransportNearResponse :
      Cast.cast scalarCarrierIdentity
        (Window.PoleNearTargetWindow.finitePoleNearSigned window)
      ≡ Transport.nearResponseAt transport J

    windowNearBudgetIsTransportNearBudget :
      Cast.cast scalarCarrierIdentity
        (Minimal.selectedNearBudget payment)
      ≡ Transport.nearBudgetAt transport J

    selectedOrderTransport :
      {x y : Weil.WeilTestSpace.Scalar space} ->
      Minimal.SelectedFiniteNearBudgetPayment.SelectedUpper payment x y ->
      NearFar._≤_ S
        (Cast.cast scalarCarrierIdentity x)
        (Cast.cast scalarCarrierIdentity y)

    attachmentReference : String

open WindowBudgetTransportAttachment public

compiledTransportedNearUpper :
  forall {space formula window payment S transport J} ->
  WindowBudgetTransportAttachment
    space formula window payment S transport J ->
  NearFar._≤_ S
    (Transport.nearResponseAt transport J)
    (Transport.nearBudgetAt transport J)
compiledTransportedNearUpper {payment = payment} attachment
  with windowFiniteNearIsTransportNearResponse attachment
     | windowNearBudgetIsTransportNearBudget attachment
... | refl | refl =
  selectedOrderTransport attachment
    (Minimal.selectedFiniteNearUpper payment)

compileFiniteNearUpperAt :
  forall {space formula window payment S transport J} ->
  (attachment :
    WindowBudgetTransportAttachment
      space formula window payment S transport J) ->
  Transport.FiniteNearUpperAt transport J
compileFiniteNearUpperAt attachment = record
  { Transport.nearUpper = compiledTransportedNearUpper attachment
  ; Transport.nearUpperReference = attachmentReference attachment
  }

record WindowBudgetTransportBoundary : Set where
  constructor window-budget-transport-boundary
  field
    secondFiniteNearEvaluationRequired : Bool
    secondFiniteNearEvaluationRequiredIsFalse :
      secondFiniteNearEvaluationRequired ≡ false

    finiteNearValueIdentityRequired : Bool
    finiteNearValueIdentityRequiredIsTrue :
      finiteNearValueIdentityRequired ≡ true

    nearBudgetIdentityRequired : Bool
    nearBudgetIdentityRequiredIsTrue :
      nearBudgetIdentityRequired ≡ true

    oneOrderTransportRequired : Bool
    oneOrderTransportRequiredIsTrue : oneOrderTransportRequired ≡ true

    transportedNearUpperIsCompilerOutput : Bool
    transportedNearUpperIsCompilerOutputIsTrue :
      transportedNearUpperIsCompilerOutput ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalWindowBudgetTransportBoundary : WindowBudgetTransportBoundary
canonicalWindowBudgetTransportBoundary =
  window-budget-transport-boundary
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    "Do not re-evaluate the finite pole-near sum after a target-window budget payment exists. Identify window.finitePoleNearSigned with the transported nearResponse(J), identify the selected near budget with transported nearBudget(J), and transport the selected upper relation once. The exact FiniteNearUpperAt needed by the chosen-cutoff Off compiler is then generated mechanically. RH is not derived."
