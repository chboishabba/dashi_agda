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
import DASHI.Analysis.RiemannG2BalanceFreeComplementContextExact as Context
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as Literal
import DASHI.Analysis.RiemannG2LiteralPhaseJointMarginCompilerExact as Phase
import DASHI.Analysis.RiemannG2UniformIndependentComplementHighProducerExact as Existing

------------------------------------------------------------------------
-- UNIFORM LITERAL-PHASE HIGH PRODUCER
--
-- For each arbitrary high off-line zero, the ANALYTIC input is now:
--
--   balance-free final context
--   + exact literal finite-near phase model
--   + literal phase+far+Gamma strict margin.
--
-- The terminal equality `cluster = Off + Gamma` is carried separately as a
-- downstream attachment.  Thus the analytic payment cannot depend on the final
-- balance through its input type, while the full case still compiles to the
-- existing prize-facing contradiction.
------------------------------------------------------------------------

record LiteralPhaseHighOffLineCase : Set₁ where
  field
    offSurface : NearFar.OrderedAdditiveNearFarSurface
    offTransport : Transport.ExplicitCutoffNearFarAgdaTransport offSurface
    targets : Direct.DirectLiteralComplementTargets offSurface offTransport

    analyticContext : Context.BalanceFreeComplementContext targets
    literalNearModel :
      Literal.FinalPoleNearLiteralModel (Direct.offInput targets)

    phasePayment :
      Phase.LiteralPhaseJointMarginPayment
        targets literalNearModel analyticContext

    finalBalance :
      Context.FinalClusterBalanceAttachment analyticContext

    caseReference : String

open LiteralPhaseHighOffLineCase public

literalPhaseCaseContradiction : LiteralPhaseHighOffLineCase -> ⊥
literalPhaseCaseContradiction c =
  Phase.literalPhasePaymentAndBalanceContradiction
    (finalBalance c)
    (phasePayment c)

compileLiteralPhaseCaseToExistingCase :
  LiteralPhaseHighOffLineCase ->
  Existing.IndependentComplementHighOffLineCase
compileLiteralPhaseCaseToExistingCase c = record
  { Existing.offSurface = offSurface c
  ; Existing.offTransport = offTransport c
  ; Existing.targets = targets c
  ; Existing.finalInput =
      Phase.compileLiteralPhasePaymentToLegacyInput
        (finalBalance c)
        (phasePayment c)
  ; Existing.caseReference = caseReference c
  }

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

compileUniformLiteralPhaseProducer :
  forall {analytic High} ->
  UniformLiteralPhaseHighProducer analytic High ->
  Existing.UniformIndependentComplementHighProducer analytic High
compileUniformLiteralPhaseProducer producer = record
  { Existing.caseForOffLineHigh =
      λ rho high offLine ->
        compileLiteralPhaseCaseToExistingCase
          (literalCaseForOffLineHigh producer rho high offLine)
  }

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

    canonicalStrictMarginPresupposedPerCase : Bool
    canonicalStrictMarginPresupposedPerCaseIsFalse :
      canonicalStrictMarginPresupposedPerCase ≡ false

    analyticPaymentCanAccessFinalBalanceThroughContext : Bool
    analyticPaymentCanAccessFinalBalanceThroughContextIsFalse :
      analyticPaymentCanAccessFinalBalanceThroughContext ≡ false

    finalBalanceIsSeparateDownstreamCaseAttachment : Bool
    finalBalanceIsSeparateDownstreamCaseAttachmentIsTrue :
      finalBalanceIsSeparateDownstreamCaseAttachment ≡ true

    literalPhaseFamilyCompilesExistingHighProducer : Bool
    literalPhaseFamilyCompilesExistingHighProducerIsTrue :
      literalPhaseFamilyCompilesExistingHighProducer ≡ true

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
    true refl
    true refl
    true refl
    false refl
    false refl
    "The prize-facing high theorem family is now dependency-level balance-free. For every arbitrary high off-line nontrivial zero, prove the literal phase+far+Gamma strict margin using only BalanceFreeComplementContext and the exact final-near model. The final cluster=Off+Gamma theorem is a separate downstream case attachment and is unavailable to the analytic payment through its context type. Payment plus balance compiles mechanically to the existing high producer and contradiction. No fixed case or canonical margin is presupposed; the analytic family remains uninhabited and RH is not derived."
