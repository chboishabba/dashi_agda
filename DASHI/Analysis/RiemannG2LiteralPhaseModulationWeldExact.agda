module DASHI.Analysis.RiemannG2LiteralPhaseModulationWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as Literal
import DASHI.Analysis.RiemannG2ProofRelevantTargetTranslationModulationExact as Phase

------------------------------------------------------------------------
-- LITERAL PHASE / TRANSLATION-MODULATION WELD
--
-- The finite untangling witness established that count/envelope data lose a
-- phase coordinate.  Two existing RH owners then sharpened the missing data:
--
--   FinalPoleNearLiteralModel
--     owns delta_sigma = ordinate(sigma) - target as an equality and exposes
--     the literal cosine-bearing cell response;
--
--   ProofRelevantTargetTranslationModulation
--     owns proof-bearing target-translation, modulation and even-projection
--     laws, but does not itself inhabit the final pole-quotient carrier.
--
-- This owner identifies the exact weld needed between those two objects.  It
-- does not assume the carriers definitionally coincide: explicit maps into the
-- modulation carrier and back to the literal scalar are retained, together
-- with proof-bearing compatibility equalities.
------------------------------------------------------------------------

record LiteralPhaseModulationWeld
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport)
    (model : Literal.FinalPoleNearLiteralModel offInput)
    (H : Phase.ProofRelevantTargetTranslationModulation) : Set₁ where
  private
    Scalar = NearFar.Scalar S
  constructor literal-phase-modulation-weld
  field
    frequencyFromLiteralScalar : Scalar → Phase.Frequency H
    ordinateFromLiteralScalar : Scalar → Phase.Ordinate H
    phaseToLiteralScalar : Phase.Phase H → Scalar

    -- The literal target-relative gap is carried to the proof-relevant
    -- translation gap on the same selected zero/target data.
    targetGapCarrierWeld :
      (sigma : Literal.ZeroIndex model) →
      ordinateFromLiteralScalar (Literal.targetRelativeGap model sigma)
      ≡ Phase.subtract H
          (ordinateFromLiteralScalar (Literal.ordinate model sigma))
          (ordinateFromLiteralScalar (Literal.target model))

    -- The even projection of the proof-relevant modulation is exactly the
    -- cosine phase already appearing in the literal reflection-paired cell.
    evenProjectionIsLiteralCosine :
      (u : Scalar) →
      (sigma : Literal.ZeroIndex model) →
      phaseToLiteralScalar
        (Phase.evenProjection H
          (Phase.modulation H
            (frequencyFromLiteralScalar u)
            (ordinateFromLiteralScalar
              (Literal.targetRelativeGap model sigma))))
      ≡ Literal.cos model
          (Literal.mul model (Literal.targetRelativeGap model sigma) u)

open LiteralPhaseModulationWeld public

literalTargetGapTransportPaid :
  ∀ {S transport}
    {offInput : Direct.DirectLiteralOffTargetInput S transport}
    {model : Literal.FinalPoleNearLiteralModel offInput}
    {H : Phase.ProofRelevantTargetTranslationModulation} →
  (weld : LiteralPhaseModulationWeld offInput model H) →
  (sigma : Literal.ZeroIndex model) →
  ordinateFromLiteralScalar weld (Literal.targetRelativeGap model sigma)
  ≡ Phase.subtract H
      (ordinateFromLiteralScalar weld (Literal.ordinate model sigma))
      (ordinateFromLiteralScalar weld (Literal.target model))
literalTargetGapTransportPaid weld = targetGapCarrierWeld weld

literalEvenPhasePaid :
  ∀ {S transport}
    {offInput : Direct.DirectLiteralOffTargetInput S transport}
    {model : Literal.FinalPoleNearLiteralModel offInput}
    {H : Phase.ProofRelevantTargetTranslationModulation} →
  (weld : LiteralPhaseModulationWeld offInput model H) →
  (u : NearFar.Scalar S) →
  (sigma : Literal.ZeroIndex model) →
  phaseToLiteralScalar weld
    (Phase.evenProjection H
      (Phase.modulation H
        (frequencyFromLiteralScalar weld u)
        (ordinateFromLiteralScalar weld
          (Literal.targetRelativeGap model sigma))))
  ≡ Literal.cos model
      (Literal.mul model (Literal.targetRelativeGap model sigma) u)
literalEvenPhasePaid weld = evenProjectionIsLiteralCosine weld

------------------------------------------------------------------------
-- Frontier interpretation.
------------------------------------------------------------------------

phaseBoundary : Phase.ProofRelevantTranslationModulationBoundary
phaseBoundary = Phase.canonicalProofRelevantTranslationModulationBoundary

literalBoundary : Literal.FinalPoleNearObserverRefinementBoundary
literalBoundary = Literal.canonicalFinalPoleNearObserverRefinementBoundary

record LiteralPhaseModulationWeldBoundary : Set where
  constructor literal-phase-modulation-weld-boundary
  field
    finiteUntanglingIdentifiedPhaseAsMissingCoordinate : Bool
    literalTargetGapAlreadyProofRelevant : Bool
    genericTranslationModulationLawsAlreadyProofRelevant : Bool
    carrierWeldRequiresExplicitMaps : Bool
    literalCosineCompatibilityIsEqualityNotSetLabel : Bool
    completedWeldWouldExposePhaseToLiteralCellConsumer : Bool
    actualUniversalPoleQuotientWeldInhabitedHere : Bool
    completedWeldAutomaticallyPaysFiniteNearBudget : Bool
    completedWeldAutomaticallyPaysStrictJointMargin : Bool
    rhDerived : Bool
open LiteralPhaseModulationWeldBoundary public

canonicalLiteralPhaseModulationWeldBoundary : LiteralPhaseModulationWeldBoundary
canonicalLiteralPhaseModulationWeldBoundary =
  literal-phase-modulation-weld-boundary
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false

data LiteralPhaseModulationWeldResidual : Set where
  inhabitUniversalPoleQuotientCarrierWeld : LiteralPhaseModulationWeldResidual
  bindLiteralScalarFrequencyOrdinatePhaseMaps : LiteralPhaseModulationWeldResidual
  proveTargetGapCarrierWeldOnSelectedZeroFamily : LiteralPhaseModulationWeldResidual
  proveEvenProjectionEqualsLiteralCosineKernel : LiteralPhaseModulationWeldResidual
  pushWeldThroughLiteralCellResponse : LiteralPhaseModulationWeldResidual
  deriveFiniteNearConsumerBudget : LiteralPhaseModulationWeldResidual
  combineNearAndFarOnlyAfterBudgetPaid : LiteralPhaseModulationWeldResidual

firstLiteralPhaseModulationWeldResidual : LiteralPhaseModulationWeldResidual
firstLiteralPhaseModulationWeldResidual = inhabitUniversalPoleQuotientCarrierWeld

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data PhaseCoordinateMeansAnalyticWeld : Set where
data AnalyticWeldMeansNearBudget : Set where
data NearBudgetMeansRH : Set where

phaseCoordinateDoesNotCreateAnalyticWeld : PhaseCoordinateMeansAnalyticWeld → ⊥
phaseCoordinateDoesNotCreateAnalyticWeld ()

analyticWeldDoesNotCreateNearBudget : AnalyticWeldMeansNearBudget → ⊥
analyticWeldDoesNotCreateNearBudget ()

nearBudgetDoesNotCreateRH : NearBudgetMeansRH → ⊥
nearBudgetDoesNotCreateRH ()
