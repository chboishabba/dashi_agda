module DASHI.Analysis.RiemannG2UniformLiteralPhaseHighProducerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2DirectClusterResponseContradictionExact as ClusterDirect
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as Literal
import DASHI.Analysis.RiemannG2LiteralPhaseDirectClusterResponseExact as Phase

record LiteralPhaseHighOffLineCase : Set₁ where
  field
    offSurface : NearFar.OrderedAdditiveNearFarSurface
    offTransport : Transport.ExplicitCutoffNearFarAgdaTransport offSurface
    targets : Direct.DirectLiteralComplementTargets offSurface offTransport
    analyticContext : ClusterDirect.BalanceFreeClusterResponseContext targets
    literalNearModel : Literal.FinalPoleNearLiteralModel (Direct.offInput targets)
    phasePayment : Phase.LiteralPhaseDirectClusterPayment targets literalNearModel analyticContext
    finalBalance : ClusterDirect.DirectClusterResponseBalanceAttachment analyticContext
    caseReference : String

open LiteralPhaseHighOffLineCase public

literalPhaseCaseContradiction : LiteralPhaseHighOffLineCase -> ⊥
literalPhaseCaseContradiction c =
  Phase.literalPhaseDirectClusterContradiction (phasePayment c) (finalBalance c)

record UniformLiteralPhaseHighProducer
    (analytic : Analytic.AnalyticSubstrate)
    (High : Universal.AnalyticNontrivialZero analytic -> Set) : Set₁ where
  field
    literalCaseForOffLineHigh :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      High rho ->
      (Universal.analyticCritical rho -> ⊥) ->
      LiteralPhaseHighOffLineCase

open UniformLiteralPhaseHighProducer public

uniformLiteralPhaseHighContradiction :
  forall {analytic High} ->
  UniformLiteralPhaseHighProducer analytic High ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  High rho ->
  (Universal.analyticCritical rho -> ⊥) ->
  ⊥
uniformLiteralPhaseHighContradiction producer rho high offLine =
  literalPhaseCaseContradiction
    (literalCaseForOffLineHigh producer rho high offLine)

record UniformLiteralPhaseHighBoundary : Set where
  constructor uniform-literal-phase-high-boundary
  field
    literalPhaseTheoremFamilyMatchesPrizeHighQuantifier : Bool
    literalPhaseTheoremFamilyMatchesPrizeHighQuantifierIsTrue :
      literalPhaseTheoremFamilyMatchesPrizeHighQuantifier ≡ true
    fixedLiteralPhaseCaseSuffices : Bool
    fixedLiteralPhaseCaseSufficesIsFalse : fixedLiteralPhaseCaseSuffices ≡ false
    intermediateClusterMarginPrimitivePerCase : Bool
    intermediateClusterMarginPrimitivePerCaseIsFalse :
      intermediateClusterMarginPrimitivePerCase ≡ false
    quantitativeClusterMarginLowerPrimitivePerCase : Bool
    quantitativeClusterMarginLowerPrimitivePerCaseIsFalse :
      quantitativeClusterMarginLowerPrimitivePerCase ≡ false
    analyticPaymentCanAccessFinalBalanceThroughContext : Bool
    analyticPaymentCanAccessFinalBalanceThroughContextIsFalse :
      analyticPaymentCanAccessFinalBalanceThroughContext ≡ false
    finalBalanceIsSeparateDownstreamCaseAttachment : Bool
    finalBalanceIsSeparateDownstreamCaseAttachmentIsTrue :
      finalBalanceIsSeparateDownstreamCaseAttachment ≡ true
    literalPhaseFamilyCompilesContradiction : Bool
    literalPhaseFamilyCompilesContradictionIsTrue :
      literalPhaseFamilyCompilesContradiction ≡ true
    producerInhabitedHere : Bool
    producerInhabitedHereIsFalse : producerInhabitedHere ≡ false
    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false
    highestAlphaReading : String

canonicalUniformLiteralPhaseHighBoundary : UniformLiteralPhaseHighBoundary
canonicalUniformLiteralPhaseHighBoundary =
  uniform-literal-phase-high-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "For every arbitrary high off-line nontrivial zero, prove literalNear+far+Gamma < actual ClusterResponse using a balance-free context and exact final-near model. The final cluster=Off+Gamma equality is downstream only. No intermediate M_cluster or M_cluster<=ClusterResponse theorem is primitive."
