module DASHI.Analysis.RiemannG2UniformBudgetNormalizedHighProducerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as OffTransport
import DASHI.Analysis.RiemannG2BudgetNormalizedFinalOrderTransportExact as Normalized
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as Core
import DASHI.Analysis.RiemannG2FinalPoleQuotientTwoPaymentCutExact as Two

------------------------------------------------------------------------
-- UNIFORM CLAY QUANTIFIER FOR THE BUDGET-NORMALIZED ROUTE
--
-- A single finite certificate / cutoff / Gamma envelope is not the high theorem.
-- For every arbitrary high nontrivial zero, under the hypothesis that it is off
-- the critical line, the producer must return one SAME-CASE normalized packet.
--
-- The packet already contains the literal current scalar leaves through its
-- normalized Off/Gamma inputs and final actual-budget strict margin.  Everything
-- from that packet to HighOffLineAnalyticCoreProducer is compiler output here.
------------------------------------------------------------------------

record BudgetNormalizedHighOffLineCase : Set₁ where
  field
    offSurface : NearFar.OrderedAdditiveNearFarSurface
    offTransport : OffTransport.ExplicitCutoffNearFarAgdaTransport offSurface

    pair : Normalized.BudgetNormalizedCorePair offSurface offTransport

    attachments :
      Core.FinalPoleQuotientAnalyticCoreAttachments
        (Normalized.compiledCores pair)

    finalTransport :
      Normalized.BudgetNormalizedFinalOrderTransportInput pair attachments

    caseReference : String

open BudgetNormalizedHighOffLineCase public

caseCores :
  BudgetNormalizedHighOffLineCase ->
  Core.FinalPoleQuotientTwoAnalyticCores
caseCores c = Normalized.compiledCores (pair c)

caseAttachments :
  (c : BudgetNormalizedHighOffLineCase) ->
  Core.FinalPoleQuotientAnalyticCoreAttachments (caseCores c)
caseAttachments c = attachments c

caseFinalAttachment :
  (c : BudgetNormalizedHighOffLineCase) ->
  Two.FinalPoleQuotientTwoPaymentAttachment
    (Core.compileFinalTwoPayments (caseCores c) (caseAttachments c))
caseFinalAttachment c = record
  { Two.surface = Normalized.surface (finalTransport c)
  ; Two.cluster = Normalized.cluster (finalTransport c)
  ; Two.transport = Normalized.compileFinalOrderTransport (finalTransport c)
  ; Two.attachmentReference = caseReference c
  }

caseCompletion :
  (c : BudgetNormalizedHighOffLineCase) ->
  Core.FinalPoleQuotientAnalyticCompletion (caseCores c) (caseAttachments c)
caseCompletion c = record
  { Core.finalAttachment = caseFinalAttachment c
  ; Core.completionReference = caseReference c
  }

caseContradiction :
  BudgetNormalizedHighOffLineCase -> ⊥
caseContradiction c =
  Core.compileAnalyticCoresToHighOrdinateContradiction
    (caseCores c)
    (caseAttachments c)
    (caseCompletion c)

record UniformBudgetNormalizedHighProducer
    (analytic : Analytic.AnalyticSubstrate)
    (High : Universal.AnalyticNontrivialZero analytic -> Set) : Set₁ where
  field
    caseForOffLineHigh :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      High rho ->
      Neg (Universal.analyticCritical rho) ->
      BudgetNormalizedHighOffLineCase

open UniformBudgetNormalizedHighProducer public

compileUniformHighProducer :
  {analytic : Analytic.AnalyticSubstrate} ->
  {High : Universal.AnalyticNontrivialZero analytic -> Set} ->
  UniformBudgetNormalizedHighProducer analytic High ->
  Universal.HighOffLineAnalyticCoreProducer analytic High
compileUniformHighProducer producer = record
  { Universal.coresForOffLineHigh =
      lambda rho high offLine ->
        caseCores (caseForOffLineHigh producer rho high offLine)
  ; Universal.attachmentsForOffLineHigh =
      lambda rho high offLine ->
        caseAttachments (caseForOffLineHigh producer rho high offLine)
  ; Universal.completionForOffLineHigh =
      lambda rho high offLine ->
        caseCompletion (caseForOffLineHigh producer rho high offLine)
  }

uniformHighContradiction :
  {analytic : Analytic.AnalyticSubstrate} ->
  {High : Universal.AnalyticNontrivialZero analytic -> Set} ->
  UniformBudgetNormalizedHighProducer analytic High ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  High rho ->
  Neg (Universal.analyticCritical rho) ->
  ⊥
uniformHighContradiction producer =
  Universal.highOffLineAnalyticCoreContradiction
    (compileUniformHighProducer producer)

------------------------------------------------------------------------
-- BOUNDARY
------------------------------------------------------------------------

record UniformBudgetNormalizedHighBoundary : Set where
  constructor uniform-budget-normalized-high-boundary
  field
    oneFixedNormalizedCaseSufficesForClayHighQuantifier : Bool
    oneFixedNormalizedCaseSufficesForClayHighQuantifierIsFalse :
      oneFixedNormalizedCaseSufficesForClayHighQuantifier ≡ false

    arbitraryHighOffLineCaseFamilyStillRequired : Bool
    arbitraryHighOffLineCaseFamilyStillRequiredIsTrue :
      arbitraryHighOffLineCaseFamilyStillRequired ≡ true

    perCaseSeparateAllowanceSlackRequired : Bool
    perCaseSeparateAllowanceSlackRequiredIsFalse :
      perCaseSeparateAllowanceSlackRequired ≡ false

    perCaseActualBudgetStrictMarginStillRequired : Bool
    perCaseActualBudgetStrictMarginStillRequiredIsTrue :
      perCaseActualBudgetStrictMarginStillRequired ≡ true

    normalizedCaseCompilesPrizeFacingHighProducer : Bool
    normalizedCaseCompilesPrizeFacingHighProducerIsTrue :
      normalizedCaseCompilesPrizeFacingHighProducer ≡ true

    lowOrdinateCertificateManufacturedHere : Bool
    lowOrdinateCertificateManufacturedHereIsFalse :
      lowOrdinateCertificateManufacturedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalUniformBudgetNormalizedHighBoundary :
  UniformBudgetNormalizedHighBoundary
canonicalUniformBudgetNormalizedHighBoundary =
  uniform-budget-normalized-high-boundary
    false refl
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "The normalized concrete route reaches the literal prize-facing HighOffLineAnalyticCoreProducer with no extra payment theorem. For every arbitrary high off-line nontrivial zero, produce one same-case packet carrying the Off finite-near upper, Gamma response upper, actual two-budget strict margin, and required representation/order attachments. Separate channel allowance slack is absent. A single fixed case is insufficient, low ordinates remain independent, and RH is not derived here."
