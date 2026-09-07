module DASHI.Analysis.RiemannG2UniformIndependentComplementHighProducerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as OffTransport
import DASHI.Analysis.RiemannG2LiteralResponseNormalizedAnalyticCoresExact as Literal
import DASHI.Analysis.RiemannG2IndependentComplementMarginFinalExact as OneLeaf
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as Core
import DASHI.Analysis.RiemannG2FinalPoleQuotientTwoPaymentCutExact as Two

------------------------------------------------------------------------
-- UNIFORM HIGH-ZERO COMPILER FOR THE ONE-LEAF ROUTE
--
-- For every arbitrary high off-line nontrivial zero, produce one SAME-CASE
-- literal-response-normalized packet plus the independently proved complement
-- margin and representation/order attachments.  Everything from that packet to
-- the existing prize-facing HighOffLineAnalyticCoreProducer is compiler output.
------------------------------------------------------------------------

record IndependentComplementHighOffLineCase : Set₁ where
  field
    offSurface : NearFar.OrderedAdditiveNearFarSurface
    offTransport : OffTransport.ExplicitCutoffNearFarAgdaTransport offSurface

    pair : Literal.LiteralResponseNormalizedCorePair offSurface offTransport

    attachments :
      Core.FinalPoleQuotientAnalyticCoreAttachments
        (Literal.compiledLiteralCores pair)

    finalInput :
      OneLeaf.IndependentComplementMarginFinalInput pair attachments

    caseReference : String

open IndependentComplementHighOffLineCase public

caseCores :
  IndependentComplementHighOffLineCase ->
  Core.FinalPoleQuotientTwoAnalyticCores
caseCores c = Literal.compiledLiteralCores (pair c)

caseAttachments :
  (c : IndependentComplementHighOffLineCase) ->
  Core.FinalPoleQuotientAnalyticCoreAttachments (caseCores c)
caseAttachments c = attachments c

caseFinalAttachment :
  (c : IndependentComplementHighOffLineCase) ->
  Two.FinalPoleQuotientTwoPaymentAttachment
    (Core.compileFinalTwoPayments (caseCores c) (caseAttachments c))
caseFinalAttachment c = record
  { Two.surface = OneLeaf.surface (finalInput c)
  ; Two.cluster = OneLeaf.cluster (finalInput c)
  ; Two.transport = OneLeaf.compileFinalOrderTransport (finalInput c)
  ; Two.attachmentReference = caseReference c
  }

caseCompletion :
  (c : IndependentComplementHighOffLineCase) ->
  Core.FinalPoleQuotientAnalyticCompletion (caseCores c) (caseAttachments c)
caseCompletion c = record
  { Core.finalAttachment = caseFinalAttachment c
  ; Core.completionReference = caseReference c
  }

caseContradiction :
  IndependentComplementHighOffLineCase -> ⊥
caseContradiction c =
  Core.compileAnalyticCoresToHighOrdinateContradiction
    (caseCores c)
    (caseAttachments c)
    (caseCompletion c)

record UniformIndependentComplementHighProducer
    (analytic : Analytic.AnalyticSubstrate)
    (High : Universal.AnalyticNontrivialZero analytic -> Set) : Set₁ where
  field
    caseForOffLineHigh :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      High rho ->
      Neg (Universal.analyticCritical rho) ->
      IndependentComplementHighOffLineCase

open UniformIndependentComplementHighProducer public

compileUniformHighProducer :
  {analytic : Analytic.AnalyticSubstrate} ->
  {High : Universal.AnalyticNontrivialZero analytic -> Set} ->
  UniformIndependentComplementHighProducer analytic High ->
  Universal.HighOffLineAnalyticCoreProducer analytic High
compileUniformHighProducer producer = record
  { Universal.coresForOffLineHigh =
      λ rho high offLine ->
        caseCores (caseForOffLineHigh producer rho high offLine)
  ; Universal.attachmentsForOffLineHigh =
      λ rho high offLine ->
        caseAttachments (caseForOffLineHigh producer rho high offLine)
  ; Universal.completionForOffLineHigh =
      λ rho high offLine ->
        caseCompletion (caseForOffLineHigh producer rho high offLine)
  }

uniformHighContradiction :
  {analytic : Analytic.AnalyticSubstrate} ->
  {High : Universal.AnalyticNontrivialZero analytic -> Set} ->
  UniformIndependentComplementHighProducer analytic High ->
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

record UniformIndependentComplementHighBoundary : Set where
  constructor uniform-independent-complement-high-boundary
  field
    fixedCaseSufficesForPrizeFacingHighQuantifier : Bool
    fixedCaseSufficesForPrizeFacingHighQuantifierIsFalse :
      fixedCaseSufficesForPrizeFacingHighQuantifier ≡ false

    arbitraryHighOffLineCaseFamilyStillRequired : Bool
    arbitraryHighOffLineCaseFamilyStillRequiredIsTrue :
      arbitraryHighOffLineCaseFamilyStillRequired ≡ true

    separateFiniteNearEnvelopeLeafRequiredPerCase : Bool
    separateFiniteNearEnvelopeLeafRequiredPerCaseIsFalse :
      separateFiniteNearEnvelopeLeafRequiredPerCase ≡ false

    separateGammaEnvelopeLeafRequiredPerCase : Bool
    separateGammaEnvelopeLeafRequiredPerCaseIsFalse :
      separateGammaEnvelopeLeafRequiredPerCase ≡ false

    independentLiteralComplementMarginRequiredPerCase : Bool
    independentLiteralComplementMarginRequiredPerCaseIsTrue :
      independentLiteralComplementMarginRequiredPerCase ≡ true

    normalizedCaseCompilesPrizeFacingHighProducer : Bool
    normalizedCaseCompilesPrizeFacingHighProducerIsTrue :
      normalizedCaseCompilesPrizeFacingHighProducer ≡ true

    lowOrdinateCertificateManufacturedHere : Bool
    lowOrdinateCertificateManufacturedHereIsFalse :
      lowOrdinateCertificateManufacturedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalUniformIndependentComplementHighBoundary :
  UniformIndependentComplementHighBoundary
canonicalUniformIndependentComplementHighBoundary =
  uniform-independent-complement-high-boundary
    false refl
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "There is no extra high-side theorem after the one-leaf packet. For every arbitrary high off-line nontrivial zero, provide the same-case cutoff/far transport, source-order reflexivity, literal-response channel cores, the independently proved complement margin, and the representation/order/cluster attachments. That compiles definitionally to the existing prize-facing HighOffLineAnalyticCoreProducer. Separate near/Gamma envelope leaves are not primitive per-case obligations, but their literal channel values remain inside the joint margin. Low ordinates stay independent and RH is not derived here."
