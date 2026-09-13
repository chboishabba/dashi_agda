module DASHI.Analysis.RiemannG2UniformIndependentComplementHighProducerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as OffTransport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2DirectIndependentComplementMarginExact as Margin

------------------------------------------------------------------------
-- UNIFORM HIGH-ZERO COMPILER FOR THE DIRECT ONE-LEAF ROUTE
------------------------------------------------------------------------

record IndependentComplementHighOffLineCase : Set₁ where
  field
    offSurface : NearFar.OrderedAdditiveNearFarSurface
    offTransport : OffTransport.ExplicitCutoffNearFarAgdaTransport offSurface
    targets : Direct.DirectLiteralComplementTargets offSurface offTransport
    finalInput : Margin.DirectIndependentComplementMarginInput targets
    caseReference : String

open IndependentComplementHighOffLineCase public

caseContradiction : IndependentComplementHighOffLineCase -> ⊥
caseContradiction c =
  Margin.directIndependentComplementContradiction (finalInput c)

record UniformIndependentComplementHighProducer
    (analytic : Analytic.AnalyticSubstrate)
    (High : Universal.AnalyticNontrivialZero analytic -> Set) : Set₁ where
  field
    caseForOffLineHigh :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      High rho ->
      (Universal.analyticCritical rho -> ⊥) ->
      IndependentComplementHighOffLineCase

open UniformIndependentComplementHighProducer public

uniformHighContradiction :
  {analytic : Analytic.AnalyticSubstrate} ->
  {High : Universal.AnalyticNontrivialZero analytic -> Set} ->
  UniformIndependentComplementHighProducer analytic High ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  High rho ->
  (Universal.analyticCritical rho -> ⊥) ->
  ⊥
uniformHighContradiction producer rho high offLine =
  caseContradiction (caseForOffLineHigh producer rho high offLine)

highCriticalFromIndependentComplement :
  {analytic : Analytic.AnalyticSubstrate} ->
  {High : Universal.AnalyticNontrivialZero analytic -> Set} ->
  Universal.CriticalLineStable analytic ->
  UniformIndependentComplementHighProducer analytic High ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  High rho ->
  Universal.analyticCritical rho
highCriticalFromIndependentComplement stable producer rho high =
  stable
    (Universal.point rho)
    (λ offLine -> uniformHighContradiction producer rho high offLine)

record UniformIndependentComplementHighBoundary : Set where
  constructor uniform-independent-complement-high-boundary
  field
    fixedCaseSufficesForPrizeFacingHighQuantifier : Bool
    fixedCaseSufficesForPrizeFacingHighQuantifierIsFalse :
      fixedCaseSufficesForPrizeFacingHighQuantifier ≡ false
    arbitraryHighOffLineCaseFamilyStillRequired : Bool
    arbitraryHighOffLineCaseFamilyStillRequiredIsTrue :
      arbitraryHighOffLineCaseFamilyStillRequired ≡ true
    consumerAssignedAllowanceLayerUsedPerCase : Bool
    consumerAssignedAllowanceLayerUsedPerCaseIsFalse :
      consumerAssignedAllowanceLayerUsedPerCase ≡ false
    separateFiniteNearEnvelopeLeafRequiredPerCase : Bool
    separateFiniteNearEnvelopeLeafRequiredPerCaseIsFalse :
      separateFiniteNearEnvelopeLeafRequiredPerCase ≡ false
    separateGammaEnvelopeLeafRequiredPerCase : Bool
    separateGammaEnvelopeLeafRequiredPerCaseIsFalse :
      separateGammaEnvelopeLeafRequiredPerCase ≡ false
    independentLiteralComplementMarginRequiredPerCase : Bool
    independentLiteralComplementMarginRequiredPerCaseIsTrue :
      independentLiteralComplementMarginRequiredPerCase ≡ true
    directCaseCompilesContradiction : Bool
    directCaseCompilesContradictionIsTrue :
      directCaseCompilesContradiction ≡ true
    criticalLineStabilityTurnsPerCaseContradictionIntoCriticality : Bool
    criticalLineStabilityTurnsPerCaseContradictionIntoCriticalityIsTrue :
      criticalLineStabilityTurnsPerCaseContradictionIntoCriticality ≡ true
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
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "The canonical high route is allowance-free. For every arbitrary high off-line nontrivial zero, provide one same-case direct literal complement target and its independently proved joint margin plus representation/order/cluster receipts. That case compiles directly to bottom through SplitPoleQuotientComplementMargin. Critical-line stability then converts the exclusion of off-line high zeros into high criticality. Separate near/Gamma envelope APIs and consumer-assigned allowances are absent from the canonical path; low ordinates remain independent and RH is not derived here."
