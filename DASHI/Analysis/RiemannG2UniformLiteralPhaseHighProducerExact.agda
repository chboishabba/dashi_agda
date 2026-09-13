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

------------------------------------------------------------------------
-- UNIFORM LITERAL-PHASE HIGH PRODUCER
--
-- The canonical arbitrary-high-zero theorem now targets the actual cluster
-- response directly.  Per high off-line zero, the ANALYTIC input is:
--
--   balance-free cluster-response context
--   + exact literal finite-near phase model
--   + literalNear + far + Gamma < ClusterResponse.
--
-- There is no intermediate quantitative M_cluster target and no final balance in
-- the analytic context.  The balance equality is a separate downstream
-- attachment used only after the strict theorem has been supplied.
------------------------------------------------------------------------

record LiteralPhaseHighOffLineCase : Set₁ where
  field
    offSurface : NearFar.OrderedAdditiveNearFarSurface
    offTransport : Transport.ExplicitCutoffNearFarAgdaTransport offSurface
    targets : Direct.DirectLiteralComplementTargets offSurface offTransport

    analyticContext :
      ClusterDirect.BalanceFreeClusterResponseContext targets

    literalNearModel :
      Literal.FinalPoleNearLiteralModel (Direct.offInput targets)

    phasePayment :
      Phase.LiteralPhaseDirectClusterPayment
        targets literalNearModel analyticContext

    finalBalance :
      ClusterDirect.DirectClusterResponseBalanceAttachment analyticContext

    caseReference : String

open LiteralPhaseHighOffLineCase public

literalPhaseCaseContradiction : LiteralPhaseHighOffLineCase -> ⊥
literalPhaseCaseContradiction c =
  Phase.literalPhaseDirectClusterContradiction
    (phasePayment c)
    (finalBalance c)

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

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record UniformLiteralPhaseHighBoundary : Set where
  constructor uniform-literal-phase-high-boundary
  field
    literalPhaseTheoremFamilyMatchesPrizeHighQuantifier : Bool
    literalPhaseTheoremFamilyMatchesPrizeHighQuantifierIsTrue :
      literalPhaseTheoremFamilyMatchesPrizeHighQuantifier ≡ true

    fixedLiteralPhaseCaseSuffices : Bool
    fixedLiteralPhaseCaseSufficesIsFalse :
      fixedLiteralPhaseCaseSuffices ≡ false

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
    "The prize-facing high theorem family now targets the literal final ClusterResponse directly. For every arbitrary high off-line nontrivial zero, prove literalNear+far+Gamma < ClusterResponse using only a balance-free context and the exact final-near model. No intermediate M_cluster or M_cluster<=ClusterResponse theorem is primitive. The final cluster=Off+Gamma equality is a separate downstream attachment, unavailable to the analytic payment. Payment plus balance compiles directly to contradiction. The family remains uninhabited and RH is not derived."
