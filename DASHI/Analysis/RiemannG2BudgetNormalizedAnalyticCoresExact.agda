module DASHI.Analysis.RiemannG2BudgetNormalizedAnalyticCoresExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2TransportedDirectCombinedOffAnalyticCoreExact as OffCore
import DASHI.Analysis.RiemannG2FreshGammaEnvelopeAnalyticCoreExact as GammaCore
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as Core

------------------------------------------------------------------------
-- BUDGET-NORMALIZED ANALYTIC CORES
--
-- `assignedOffAllowance` and `assignedGammaAllowance` are bookkeeping values
-- used by the downstream two-channel margin.  They need not be analytically
-- larger than the producer budgets.  The least-privilege choice is to assign
-- each allowance definitionally to its actual producer budget.
--
-- Consequently the per-channel allowance-fit fields become self-order receipts:
--
--   B_off <= B_off
--   B_Gamma <= B_Gamma.
--
-- The nontrivial compatibility theorem is then concentrated where it belongs:
-- the final joint strict margin for the two actual budgets.
------------------------------------------------------------------------

chosenOffBudget :
  forall {S transport} ->
  Transport.Cutoff transport ->
  NearFar.Scalar S
chosenOffBudget {S = S} {transport = transport} J =
  NearFar.add S
    (Transport.nearBudgetAt transport J)
    (Transport.farBudgetAt transport J)

record BudgetNormalizedOffCoreInput
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (transport : Transport.ExplicitCutoffNearFarAgdaTransport S) : Set₁ where
  field
    chosenCutoff : Transport.Cutoff transport
    nearUpperAtChosen : Transport.FiniteNearUpperAt transport chosenCutoff

    chosenBudgetSelfOrder :
      NearFar._≤_ S
        (chosenOffBudget {S = S} {transport = transport} chosenCutoff)
        (chosenOffBudget {S = S} {transport = transport} chosenCutoff)

    analyticReference : String

open BudgetNormalizedOffCoreInput public

compileNormalizedOffInput :
  forall {S transport} ->
  BudgetNormalizedOffCoreInput S transport ->
  OffCore.DirectCombinedTransportedOffCoreInput S transport
compileNormalizedOffInput {S = S} {transport = transport} input = record
  { OffCore.chosenCutoff = chosenCutoff input
  ; OffCore.nearUpperAtChosen = nearUpperAtChosen input
  ; OffCore.assignedOffAllowance =
      chosenOffBudget {S = S} {transport = transport} (chosenCutoff input)
  ; OffCore.chosenCombinedBudgetBelowAssigned = chosenBudgetSelfOrder input
  ; OffCore.analyticReference = analyticReference input
  }

compileBudgetNormalizedOffCore :
  forall {S transport} ->
  BudgetNormalizedOffCoreInput S transport ->
  Core.OffAnalyticCore
compileBudgetNormalizedOffCore input =
  OffCore.compileOffAnalyticCore (compileNormalizedOffInput input)

normalizedOffAllowanceIsActualBudget :
  forall {S transport} ->
  (input : BudgetNormalizedOffCoreInput S transport) ->
  Core.OffAnalyticCore.assignedOffAllowance
    (compileBudgetNormalizedOffCore input)
  ≡ chosenOffBudget {S = S} {transport = transport} (chosenCutoff input)
normalizedOffAllowanceIsActualBudget input = refl

------------------------------------------------------------------------
-- GAMMA: ASSIGN THE ALLOWANCE TO THE FRESH ENVELOPE ITSELF
------------------------------------------------------------------------

record BudgetNormalizedGammaCoreInput : Set₁ where
  field
    Scalar : Set
    Taper : Set
    _≤_ : Scalar -> Scalar -> Set

    gammaResponse : Taper -> Scalar
    gammaEnvelope : Taper -> Scalar
    universalPoleQuotientTaper : Taper

    gammaResponseBelowEnvelope :
      _≤_
        (gammaResponse universalPoleQuotientTaper)
        (gammaEnvelope universalPoleQuotientTaper)

    envelopeSelfOrder :
      _≤_
        (gammaEnvelope universalPoleQuotientTaper)
        (gammaEnvelope universalPoleQuotientTaper)

    analyticReference : String

open BudgetNormalizedGammaCoreInput public

compileNormalizedGammaInput :
  BudgetNormalizedGammaCoreInput ->
  GammaCore.FreshGammaEnvelopeCoreInput
compileNormalizedGammaInput input = record
  { GammaCore.Scalar = Scalar input
  ; GammaCore.Taper = Taper input
  ; GammaCore._≤_ = _≤_ input
  ; GammaCore.gammaResponse = gammaResponse input
  ; GammaCore.gammaEnvelope = gammaEnvelope input
  ; GammaCore.universalPoleQuotientTaper = universalPoleQuotientTaper input
  ; GammaCore.gammaResponseBelowEnvelope = gammaResponseBelowEnvelope input
  ; GammaCore.assignedGammaAllowance =
      gammaEnvelope input (universalPoleQuotientTaper input)
  ; GammaCore.envelopeBelowAssignedAllowance = envelopeSelfOrder input
  ; GammaCore.analyticReference = analyticReference input
  }

compileBudgetNormalizedGammaCore :
  BudgetNormalizedGammaCoreInput ->
  Core.GammaAnalyticCore
compileBudgetNormalizedGammaCore input =
  GammaCore.compileGammaAnalyticCore (compileNormalizedGammaInput input)

normalizedGammaAllowanceIsActualBudget :
  (input : BudgetNormalizedGammaCoreInput) ->
  Core.GammaAnalyticCore.assignedGammaAllowance
    (compileBudgetNormalizedGammaCore input)
  ≡ gammaEnvelope input (universalPoleQuotientTaper input)
normalizedGammaAllowanceIsActualBudget input = refl

------------------------------------------------------------------------
-- BOUNDARY
------------------------------------------------------------------------

record BudgetNormalizedAnalyticCoreBoundary : Set where
  constructor budget-normalized-analytic-core-boundary
  field
    offSeparateAssignedAllowanceSlackRequired : Bool
    offSeparateAssignedAllowanceSlackRequiredIsFalse :
      offSeparateAssignedAllowanceSlackRequired ≡ false

    gammaSeparateAssignedAllowanceSlackRequired : Bool
    gammaSeparateAssignedAllowanceSlackRequiredIsFalse :
      gammaSeparateAssignedAllowanceSlackRequired ≡ false

    sourceBudgetSelfOrderReceiptStillRequired : Bool
    sourceBudgetSelfOrderReceiptStillRequiredIsTrue :
      sourceBudgetSelfOrderReceiptStillRequired ≡ true

    offTargetUpperStillRequiresChosenNearUpper : Bool
    offTargetUpperStillRequiresChosenNearUpperIsTrue :
      offTargetUpperStillRequiresChosenNearUpper ≡ true

    gammaTargetUpperStillRequiresResponseEnvelopeTheorem : Bool
    gammaTargetUpperStillRequiresResponseEnvelopeTheoremIsTrue :
      gammaTargetUpperStillRequiresResponseEnvelopeTheorem ≡ true

    actualTwoBudgetStrictMarginRemainsNontrivial : Bool
    actualTwoBudgetStrictMarginRemainsNontrivialIsTrue :
      actualTwoBudgetStrictMarginRemainsNontrivial ≡ true

    allowancesCanBeChosenDefinitionallyAsBudgets : Bool
    allowancesCanBeChosenDefinitionallyAsBudgetsIsTrue :
      allowancesCanBeChosenDefinitionallyAsBudgets ≡ true

    analyticCoreInhabitanceFabricatedHere : Bool
    analyticCoreInhabitanceFabricatedHereIsFalse :
      analyticCoreInhabitanceFabricatedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalBudgetNormalizedAnalyticCoreBoundary :
  BudgetNormalizedAnalyticCoreBoundary
canonicalBudgetNormalizedAnalyticCoreBoundary =
  budget-normalized-analytic-core-boundary
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "Choose each downstream allowance to be the actual producer budget. Then Off's B_off<=A_off and Gamma's B_Gamma<=A_Gamma are only self-order receipts, not fresh sharpness estimates. The genuinely quantitative work is concentrated in the producer upper theorems themselves and the final strict inequality for the sum of the actual Off and Gamma budgets against the cluster margin. This removes two arbitrary slack variables without weakening the final consumer. No core inhabitant or RH theorem is fabricated here."
