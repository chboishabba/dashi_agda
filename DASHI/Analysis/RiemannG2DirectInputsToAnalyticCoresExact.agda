module DASHI.Analysis.RiemannG2DirectInputsToAnalyticCoresExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2TransportedChosenCutoffOffAllowanceCompilerExact as OffRoute
import DASHI.Analysis.RiemannG2FreshSameTaperGammaEnvelopeCompilerExact as GammaRoute
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as Payment
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as Core

------------------------------------------------------------------------
-- DIRECT EXISTING ROUTES -> AUTHORITATIVE ANALYTIC CORES
--
-- The chosen-cutoff Off route and the fresh same-taper Gamma route already
-- compile the historical allowance-payment records.  The authoritative final
-- search surface, however, is now OffAnalyticCore + GammaAnalyticCore.
--
-- This owner removes that stale detour: project the theorem-bearing analytic
-- fields out of the already-owned route compilers directly into the current
-- cores.  Representation receipts remain representation receipts; no analytic
-- theorem is manufactured here.
------------------------------------------------------------------------

offPaymentToAnalyticCore :
  Payment.PoleQuotientOffAllowancePayment ->
  Core.OffAnalyticCore
offPaymentToAnalyticCore payment =
  Core.off-analytic-core
    (Payment.PoleQuotientOffAllowancePayment.target payment)
    (Payment.PoleQuotientOffAllowancePayment.assignedOffAllowance payment)
    (Payment.PoleQuotientOffAllowancePayment.offBudgetBelowAssignedAllowance payment)
    (Payment.PoleQuotientOffAllowancePayment.producerReference payment)

gammaPaymentToAnalyticCore :
  Payment.PoleQuotientGammaAllowancePayment ->
  Core.GammaAnalyticCore
gammaPaymentToAnalyticCore payment =
  Core.gamma-analytic-core
    (Payment.PoleQuotientGammaAllowancePayment.target payment)
    (Payment.PoleQuotientGammaAllowancePayment.assignedGammaAllowance payment)
    (Payment.PoleQuotientGammaAllowancePayment.gammaBudgetBelowAssignedAllowance payment)
    (Payment.PoleQuotientGammaAllowancePayment.producerReference payment)

compileChosenCutoffOffAnalyticCore :
  forall {S transport} ->
  OffRoute.TransportedChosenCutoffOffAllowanceInput S transport ->
  Core.OffAnalyticCore
compileChosenCutoffOffAnalyticCore input =
  offPaymentToAnalyticCore
    (OffRoute.compileFinalOffAllowancePayment input)

compileFreshGammaAnalyticCore :
  (envelope : GammaRoute.FreshSameTaperGammaEnvelope) ->
  GammaRoute.FreshSameTaperGammaAllowanceInput envelope ->
  Core.GammaAnalyticCore
compileFreshGammaAnalyticCore envelope input =
  gammaPaymentToAnalyticCore
    (GammaRoute.compileFreshSameTaperGammaAllowancePayment envelope input)

compileDirectTwoAnalyticCores :
  forall {S transport} ->
  (offInput : OffRoute.TransportedChosenCutoffOffAllowanceInput S transport) ->
  (envelope : GammaRoute.FreshSameTaperGammaEnvelope) ->
  GammaRoute.FreshSameTaperGammaAllowanceInput envelope ->
  Core.FinalPoleQuotientTwoAnalyticCores
compileDirectTwoAnalyticCores offInput envelope gammaInput =
  Core.final-pole-quotient-two-analytic-cores
    (compileChosenCutoffOffAnalyticCore offInput)
    (compileFreshGammaAnalyticCore envelope gammaInput)
    "chosen-cutoff Off route + fresh same-taper Gamma route compile directly to final analytic cores"

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record DirectInputsToAnalyticCoresBoundary : Set where
  constructor direct-inputs-to-analytic-cores-boundary
  field
    historicalPaymentDetourRequiredForSearch : Bool
    historicalPaymentDetourRequiredForSearchIsFalse :
      historicalPaymentDetourRequiredForSearch ≡ false

    chosenCutoffOffRouteCompilesCurrentOffCore : Bool
    chosenCutoffOffRouteCompilesCurrentOffCoreIsTrue :
      chosenCutoffOffRouteCompilesCurrentOffCore ≡ true

    freshGammaRouteCompilesCurrentGammaCore : Bool
    freshGammaRouteCompilesCurrentGammaCoreIsTrue :
      freshGammaRouteCompilesCurrentGammaCore ≡ true

    representationReceiptsPromotedToAnalysis : Bool
    representationReceiptsPromotedToAnalysisIsFalse :
      representationReceiptsPromotedToAnalysis ≡ false

    analyticCoresInhabitedWithoutRouteInputs : Bool
    analyticCoresInhabitedWithoutRouteInputsIsFalse :
      analyticCoresInhabitedWithoutRouteInputs ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalDirectInputsToAnalyticCoresBoundary :
  DirectInputsToAnalyticCoresBoundary
canonicalDirectInputsToAnalyticCoresBoundary =
  direct-inputs-to-analytic-cores-boundary
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "The existing chosen-cutoff Off compiler and fresh same-taper Gamma compiler already carry exactly the budget-fit mathematics required by the authoritative OffAnalyticCore and GammaAnalyticCore. Project those analytic fields directly and keep cutoff/taper identity outside the cores. This removes the historical payment records from proof-search accounting without fabricating either analytic theorem. RH remains open."
