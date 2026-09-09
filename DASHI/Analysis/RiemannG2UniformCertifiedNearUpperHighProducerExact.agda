module DASHI.Analysis.RiemannG2UniformCertifiedNearUpperHighProducerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2FinalNearLiteralKernelExact as Literal
import DASHI.Analysis.RiemannG2FinalCarrierFiniteSumCertificateExact as FinalCert
import DASHI.Analysis.RiemannG2CertifiedNearUpperClusterResponseCompilerExact as Certified
import DASHI.Analysis.RiemannG2DirectClusterResponseContradictionExact as Cluster
import DASHI.Analysis.RiemannG2UniformHighContradictionExact as Generic

record CertifiedNearUpperHighOffLineCase : Set₁ where
  field
    offSurface : NearFar.OrderedAdditiveNearFarSurface
    offTransport : Transport.ExplicitCutoffNearFarAgdaTransport offSurface
    targets : Direct.DirectLiteralComplementTargets offSurface offTransport
    literalKernel : Literal.FinalNearLiteralKernel (Direct.offInput targets)
    certificate :
      FinalCert.FinalCarrierFiniteSumCertificate
        (Direct.offInput targets) literalKernel
    upper :
      FinalCert.FinalCarrierFiniteSumUpper
        (Direct.offInput targets) literalKernel certificate
    orderAttachment :
      Certified.CertifiedNearUpperOrderAttachment
        (Direct.offInput targets) literalKernel upper
    analyticContext : Cluster.BalanceFreeClusterResponseContext targets
    certifiedMargin :
      Certified.CertifiedNearUpperClusterMargin
        targets literalKernel upper orderAttachment analyticContext
    finalBalance :
      Cluster.DirectClusterResponseBalanceAttachment analyticContext
    caseReference : String

open CertifiedNearUpperHighOffLineCase public

certifiedCaseContradiction : CertifiedNearUpperHighOffLineCase -> ⊥
certifiedCaseContradiction c =
  Cluster.directClusterResponseContradiction
    (analyticContext c)
    (Certified.compileCertifiedUpperToDirectClusterPayment
      (certifiedMargin c))
    (finalBalance c)

record UniformCertifiedNearUpperHighProducer
    (analytic : Analytic.AnalyticSubstrate)
    (High : Universal.AnalyticNontrivialZero analytic -> Set) : Set₁ where
  field
    certifiedCaseForOffLineHigh :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      High rho ->
      (Universal.analyticCritical rho -> ⊥) ->
      CertifiedNearUpperHighOffLineCase

open UniformCertifiedNearUpperHighProducer public

uniformCertifiedNearUpperHighContradiction :
  forall {analytic High} ->
  UniformCertifiedNearUpperHighProducer analytic High ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  High rho ->
  (Universal.analyticCritical rho -> ⊥) ->
  ⊥
uniformCertifiedNearUpperHighContradiction producer rho high offLine =
  certifiedCaseContradiction
    (certifiedCaseForOffLineHigh producer rho high offLine)

compileUniformCertifiedToHighContradiction :
  forall {analytic High} ->
  UniformCertifiedNearUpperHighProducer analytic High ->
  Generic.UniformHighContradictionProducer analytic High
compileUniformCertifiedToHighContradiction producer = record
  { Generic.contradictionForOffLineHigh =
      uniformCertifiedNearUpperHighContradiction producer
  ; Generic.producerReference =
      "compiled from UniformCertifiedNearUpperHighProducer"
  }

record UniformCertifiedNearUpperHighBoundary : Set where
  constructor uniform-certified-near-upper-high-boundary
  field
    certifiedRouteMatchesPrizeHighQuantifier : Bool
    certifiedRouteMatchesPrizeHighQuantifierIsTrue :
      certifiedRouteMatchesPrizeHighQuantifier ≡ true
    certifiedRouteCompilesGenericHighContradiction : Bool
    certifiedRouteCompilesGenericHighContradictionIsTrue :
      certifiedRouteCompilesGenericHighContradiction ≡ true
    selectedWeilWindowRequiredPerCase : Bool
    selectedWeilWindowRequiredPerCaseIsFalse :
      selectedWeilWindowRequiredPerCase ≡ false
    determinantConsumerRequiredPerCase : Bool
    determinantConsumerRequiredPerCaseIsFalse :
      determinantConsumerRequiredPerCase ≡ false
    finalBalanceAvailableToCertifiedMargin : Bool
    finalBalanceAvailableToCertifiedMarginIsFalse :
      finalBalanceAvailableToCertifiedMargin ≡ false
    fixedCertifiedCaseSuffices : Bool
    fixedCertifiedCaseSufficesIsFalse :
      fixedCertifiedCaseSuffices ≡ false
    producerInhabitedHere : Bool
    producerInhabitedHereIsFalse : producerInhabitedHere ≡ false
    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false
    highestAlphaReading : String

canonicalUniformCertifiedNearUpperHighBoundary :
  UniformCertifiedNearUpperHighBoundary
canonicalUniformCertifiedNearUpperHighBoundary =
  uniform-certified-near-upper-high-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "For every arbitrary high off-line zero, the window-free evaluator-independent literal kernel plus a proof-carrying finite upper and an independent certified envelope U+B_far+D_Gamma<ClusterResponse compile the same generic high contradiction consumed by the Clay spine. The final balance remains downstream, a fixed case is insufficient, and neither this producer nor RH is inhabited here."
