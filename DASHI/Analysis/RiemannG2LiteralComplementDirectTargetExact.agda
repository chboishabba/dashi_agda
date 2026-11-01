module DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2QuarterPeriodScalingPropagationExact as Scaling
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma

------------------------------------------------------------------------
-- DIRECT LITERAL COMPLEMENT TARGETS, WITHOUT PRODUCER-CHOSEN ALLOWANCES
--
-- The final split-complement consumer needs actual channel budgets and a strict
-- bound on their sum.  It does not intrinsically need the historical
-- consumer-assigned allowance layer.
--
-- For Off, use the selected literal signed near response itself plus the already
-- transported far-shell budget:
--
--   B_off(J) := D_near(J) + B_far(J).
--
-- The chosen J is definitionally tied, through an explicit carrier equality, to
-- the existing MinimalQuarterPeriodCutoff inside QuarterPeriodScalingAdmission.
-- This preserves the checked narrow-window no-go: the direct route cannot hide a
-- subcritical cutoff behind the one-leaf API.
--
-- `full <= B_off` is compiler output from the checked split theorem, source-order
-- reflexivity on D_near, and the transported far upper.  No separate finite-near
-- envelope is introduced.
--
-- For Gamma, use the literal response itself as its source-order budget:
--
--   B_Gamma(g) := D_Gamma(g).
--
-- This is not a consumer allowance and does not violate the rule that an
-- analytic producer may not choose its own downstream allowance.
------------------------------------------------------------------------

cast : {A B : Set} -> A ≡ B -> A -> B
cast refl x = x

record DirectLiteralOffTargetInput
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (transport : Transport.ExplicitCutoffNearFarAgdaTransport S) : Set₁ where
  field
    chosenCutoff : Transport.Cutoff transport

    widthLaw : Scaling.LiteralHighOrdinateWidthLaw
    crossingAdmission : Scaling.QuarterPeriodScalingAdmission widthLaw

    crossingCutoffCarrierIdentity :
      Scaling.MinimalQuarterPeriodCutoff.Cutoff
        (Scaling.QuarterPeriodScalingAdmission.cutoff crossingAdmission)
      ≡ Transport.Cutoff transport

    chosenCutoffIsCrossingCutoff :
      cast crossingCutoffCarrierIdentity
        (Scaling.MinimalQuarterPeriodCutoff.chosenCutoff
          (Scaling.QuarterPeriodScalingAdmission.cutoff crossingAdmission))
      ≡ chosenCutoff

    sourceOrderReflexive :
      (x : NearFar.Scalar S) -> NearFar._≤_ S x x

    independentOfFinalBalanceIdentity : Set
    independentOfFinalBalanceIdentityReceipt :
      independentOfFinalBalanceIdentity

    targetReference : String

open DirectLiteralOffTargetInput public

directOffBudget :
  forall {S transport} ->
  DirectLiteralOffTargetInput S transport ->
  Transport.Taper transport ->
  NearFar.Scalar S
directOffBudget {S = S} {transport = transport} input taper =
  NearFar.add S
    (Transport.nearResponseAt transport (chosenCutoff input))
    (Transport.farBudgetAt transport (chosenCutoff input))

directSignedOffUpper :
  forall {S transport} ->
  (input : DirectLiteralOffTargetInput S transport) ->
  NearFar._≤_ S
    (Transport.fullResponse transport
      (Transport.universalPoleQuotientTaper transport))
    (directOffBudget input
      (Transport.universalPoleQuotientTaper transport))
directSignedOffUpper {S = S} {transport = transport} input =
  NearFar.≤-trans S
    (Transport.fullBelowNearPlusFarAt transport (chosenCutoff input))
    (NearFar.addMonotone S
      (sourceOrderReflexive input
        (Transport.nearResponseAt transport (chosenCutoff input)))
      (Transport.farUpperAt transport (chosenCutoff input)))

compileDirectOffTarget :
  forall {S transport} ->
  DirectLiteralOffTargetInput S transport ->
  Off.PoleQuotientOffOrdinateBudgetTarget
compileDirectOffTarget {S = S} {transport = transport} input =
  Off.pole-quotient-off-ordinate-budget-target
    (NearFar.Scalar S)
    (Transport.Taper transport)
    (Transport.fullResponse transport)
    (directOffBudget input)
    (NearFar._≤_ S)
    (Transport.universalPoleQuotientTaper transport)
    (directSignedOffUpper input)

record DirectLiteralGammaTargetInput : Set₁ where
  field
    Scalar : Set
    Taper : Set
    _≤_ : Scalar -> Scalar -> Set

    gammaResponse : Taper -> Scalar
    universalPoleQuotientTaper : Taper

    sourceOrderReflexive : (x : Scalar) -> _≤_ x x

    independentOfFinalBalanceIdentity : Set
    independentOfFinalBalanceIdentityReceipt :
      independentOfFinalBalanceIdentity

    targetReference : String

open DirectLiteralGammaTargetInput public

compileDirectGammaTarget :
  DirectLiteralGammaTargetInput ->
  Gamma.PoleQuotientGammaBudgetTarget
compileDirectGammaTarget input =
  Gamma.pole-quotient-gamma-budget-target
    (Scalar input)
    (Taper input)
    (gammaResponse input)
    (gammaResponse input)
    (_≤_ input)
    (universalPoleQuotientTaper input)
    (sourceOrderReflexive input
      (gammaResponse input (universalPoleQuotientTaper input)))

record DirectLiteralComplementTargets
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (transport : Transport.ExplicitCutoffNearFarAgdaTransport S) : Set₁ where
  field
    offInput : DirectLiteralOffTargetInput S transport
    gammaInput : DirectLiteralGammaTargetInput
    targetReference : String

open DirectLiteralComplementTargets public

directOffTarget :
  forall {S transport} ->
  DirectLiteralComplementTargets S transport ->
  Off.PoleQuotientOffOrdinateBudgetTarget
directOffTarget targets = compileDirectOffTarget (offInput targets)

directGammaTarget :
  forall {S transport} ->
  DirectLiteralComplementTargets S transport ->
  Gamma.PoleQuotientGammaBudgetTarget
directGammaTarget targets = compileDirectGammaTarget (gammaInput targets)

record DirectLiteralComplementTargetBoundary : Set where
  constructor direct-literal-complement-target-boundary
  field
    producerAssignedAllowanceUsed : Bool
    producerAssignedAllowanceUsedIsFalse :
      producerAssignedAllowanceUsed ≡ false

    quarterPeriodCrossingAdmissionRequired : Bool
    quarterPeriodCrossingAdmissionRequiredIsTrue :
      quarterPeriodCrossingAdmissionRequired ≡ true

    exactCrossingCutoffIdentifiedWithOffCutoff : Bool
    exactCrossingCutoffIdentifiedWithOffCutoffIsTrue :
      exactCrossingCutoffIdentifiedWithOffCutoff ≡ true

    quarterPeriodAdmissionIsSeparateTerminalAnalyticLeaf : Bool
    quarterPeriodAdmissionIsSeparateTerminalAnalyticLeafIsFalse :
      quarterPeriodAdmissionIsSeparateTerminalAnalyticLeaf ≡ false

    separateFiniteNearEnvelopeRequired : Bool
    separateFiniteNearEnvelopeRequiredIsFalse :
      separateFiniteNearEnvelopeRequired ≡ false

    transportedFarShellUpperStillUsed : Bool
    transportedFarShellUpperStillUsedIsTrue :
      transportedFarShellUpperStillUsed ≡ true

    separateGammaEnvelopeRequired : Bool
    separateGammaEnvelopeRequiredIsFalse :
      separateGammaEnvelopeRequired ≡ false

    offUpperCompilesFromSplitReflexivityAndFarUpper : Bool
    offUpperCompilesFromSplitReflexivityAndFarUpperIsTrue :
      offUpperCompilesFromSplitReflexivityAndFarUpper ≡ true

    gammaUpperIsSourceOrderReflexivity : Bool
    gammaUpperIsSourceOrderReflexivityIsTrue :
      gammaUpperIsSourceOrderReflexivity ≡ true

    finalBalanceMayManufactureTargets : Bool
    finalBalanceMayManufactureTargetsIsFalse :
      finalBalanceMayManufactureTargets ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalDirectLiteralComplementTargetBoundary :
  DirectLiteralComplementTargetBoundary
canonicalDirectLiteralComplementTargetBoundary =
  direct-literal-complement-target-boundary
    false refl
    true refl
    true refl
    false refl
    false refl
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "Bypass the consumer-assigned allowance layer while preserving the checked narrow-window no-go. The chosen Off cutoff is exactly identified with the MinimalQuarterPeriodCutoff carried by the existing scaling admission. Then B_off(J)=D_near(J)+B_far(J), with full<=B_off compiled from the checked split theorem, source-order reflexivity, and the transported far upper. B_Gamma=D_Gamma by source-order reflexivity. Crossing is an admission/representation coordinate, not a second terminal analytic theorem. No producer chooses a downstream allowance and neither target is manufactured from the final cluster balance. RH is not derived here."
