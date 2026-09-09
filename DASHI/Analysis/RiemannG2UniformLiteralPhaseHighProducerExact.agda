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
import DASHI.Analysis.RiemannG2DirectComplementUnpaidContextExact as Context
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as Literal
import DASHI.Analysis.RiemannG2LiteralPhaseJointMarginCompilerExact as Phase
import DASHI.Analysis.RiemannG2UniformIndependentComplementHighProducerExact as Existing

------------------------------------------------------------------------
-- UNIFORM LITERAL-PHASE HIGH PRODUCER
--
-- The existing uniform producer is phrased in terms of a final combined input.
-- The introspective route now has a strictly lower theorem surface: for each
-- arbitrary high off-line zero, expose the exact literal finite-near phase model
-- and prove its joint phase+far+Gamma margin in the unpaid final context.
--
-- This module compiles that literal theorem family to the existing prize-facing
-- high producer.  No fixed-case certificate is promoted to the universal
-- quantifier and no canonical strict margin is assumed in the input case.
------------------------------------------------------------------------

record LiteralPhaseHighOffLineCase : Set₁ where
  field
    offSurface : NearFar.OrderedAdditiveNearFarSurface
    offTransport : Transport.ExplicitCutoffNearFarAgdaTransport offSurface
    targets : Direct.DirectLiteralComplementTargets offSurface offTransport

    context : Context.DirectComplementUnpaidContext targets
    literalNearModel :
      Literal.FinalPoleNearLiteralModel (Direct.offInput targets)

    phasePayment :
      Phase.LiteralPhaseJointMarginPayment
        targets literalNearModel context

    caseReference : String

open LiteralPhaseHighOffLineCase public

literalPhaseCaseContradiction : LiteralPhaseHighOffLineCase -> ⊥
literalPhaseCaseContradiction c =
  Phase.literalPhasePaymentContradiction (phasePayment c)

compileLiteralPhaseCaseToExistingCase :
  LiteralPhaseHighOffLineCase ->
  Existing.IndependentComplementHighOffLineCase
compileLiteralPhaseCaseToExistingCase c = record
  { Existing.offSurface = offSurface c
  ; Existing.offTransport = offTransport c
  ; Existing.targets = targets c
  ; Existing.finalInput =
      Phase.compileLiteralPhasePaymentToLegacyInput (phasePayment c)
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
    true refl
    true refl
    false refl
    false refl
    "The prize-facing high theorem can now be stated directly on the phase-visible carrier: for every arbitrary high off-line nontrivial zero, supply the same-object literal near model, the unpaid final context, and the independent literal phase+far+Gamma strict margin. That family compiles mechanically to the existing UniformIndependentComplementHighProducer and contradiction. No canonical margin is presupposed and no fixed case is generalized. The literal phase inequality family remains uninhabited here, so RH is not derived."
