module DASHI.Analysis.RiemannG2PhaseResidualRealizationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerIndexedResidualLocalizationExact as Localization
import DASHI.Analysis.RiemannG2ConsumerIndexedUntanglingTowerExact as RH
import DASHI.Analysis.RiemannG2LiteralPhaseModulationWeldExact as Weld
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as Literal
import DASHI.Analysis.RiemannG2ProofRelevantTargetTranslationModulationExact as Phase
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct

------------------------------------------------------------------------
-- PHASE RESIDUAL: FINITE LOCALIZATION -> ANALYTIC REALIZATION INTERFACE
--
-- The finite RH collision already proves that count/envelope is too coarse and
-- that the retained signed phase separates the consumer witness.  The common
-- residual-localization kernel lets us state this as an explicit smaller
-- coordinate inside RelativeFine.
--
-- Separately, LiteralPhaseModulationWeld gives the proof-relevant analytic
-- realization we actually need: even modulation on the same selected carrier
-- must equal the literal cosine kernel in the final near cell.
--
-- This owner connects those two roles without pretending the finite sign class
-- itself proves the analytic weld.
------------------------------------------------------------------------

data TargetRelativePhaseClass : Set where
  positiveTargetRelativePhase : TargetRelativePhaseClass
  negativeTargetRelativePhase : TargetRelativePhaseClass

phaseClass : RH.SignedPhaseResidual -> TargetRelativePhaseClass
phaseClass RH.positiveSignedPhase = positiveTargetRelativePhase
phaseClass RH.negativeSignedPhase = negativeTargetRelativePhase

phaseClassSeparatesFiniteWitness :
  phaseClass RH.positiveSignedPhase
  ≡ phaseClass RH.negativeSignedPhase -> ⊥
phaseClassSeparatesFiniteWitness ()

finitePhaseResidualLocalization :
  Localization.LocalizedResidualWitness
    RH.rhCellUntanglingGeometry
    RH.signedResponseObserve
finitePhaseResidualLocalization =
  Localization.localized-residual-witness
    RH.rhCellFineSensitiveConsumer
    TargetRelativePhaseClass
    phaseClass
    phaseClassSeparatesFiniteWitness

localizedPhaseObserverSeparatesFiniteWitness :
  Localization.localizedObserver finitePhaseResidualLocalization RH.positivePhaseWorld
  ≡ Localization.localizedObserver finitePhaseResidualLocalization RH.negativePhaseWorld
  -> ⊥
localizedPhaseObserverSeparatesFiniteWitness =
  Localization.localizedObserverSeparatesWitness finitePhaseResidualLocalization

------------------------------------------------------------------------
-- Conditional analytic realization.
--
-- Once a same-object LiteralPhaseModulationWeld is inhabited, its proof-bearing
-- equality is exactly the map from phase-sensitive analytic structure to the
-- literal cosine consumed by the final near cell.  No finite sign witness is
-- used as authority for this equality.
------------------------------------------------------------------------

phaseResidualRealizesLiteralCosine :
  ∀ {S transport}
    {offInput : Direct.DirectLiteralOffTargetInput S transport}
    {model : Literal.FinalPoleNearLiteralModel offInput}
    {H : Phase.ProofRelevantTargetTranslationModulation} ->
  (weld : Weld.LiteralPhaseModulationWeld offInput model H) ->
  (u : NearFar.Scalar S) ->
  (sigma : Literal.ZeroIndex model) ->
  Weld.phaseToLiteralScalar weld
    (Phase.evenProjection H
      (Phase.modulation H
        (Weld.frequencyFromLiteralScalar weld u)
        (Weld.ordinateFromLiteralScalar weld
          (Literal.targetRelativeGap model sigma))))
  ≡ Literal.cos model
      (Literal.mul model (Literal.targetRelativeGap model sigma) u)
phaseResidualRealizesLiteralCosine = Weld.literalEvenPhasePaid

phaseResidualRealizesLiteralTargetGap :
  ∀ {S transport}
    {offInput : Direct.DirectLiteralOffTargetInput S transport}
    {model : Literal.FinalPoleNearLiteralModel offInput}
    {H : Phase.ProofRelevantTargetTranslationModulation} ->
  (weld : Weld.LiteralPhaseModulationWeld offInput model H) ->
  (sigma : Literal.ZeroIndex model) ->
  Weld.ordinateFromLiteralScalar weld (Literal.targetRelativeGap model sigma)
  ≡ Phase.subtract H
      (Weld.ordinateFromLiteralScalar weld (Literal.ordinate model sigma))
      (Weld.ordinateFromLiteralScalar weld (Literal.target model))
phaseResidualRealizesLiteralTargetGap = Weld.literalTargetGapTransportPaid

------------------------------------------------------------------------
-- Boundary / next residual.
------------------------------------------------------------------------

record PhaseResidualRealizationBoundary : Set where
  constructor phase-residual-realization-boundary
  field
    commonResidualLocalizationKernelReused : Bool
    finiteCountEnvelopeCollisionInherited : Bool
    finiteSignedPhaseLocalizedAsSmallerCoordinate : Bool
    localizedPhaseSeparatesFiniteSignedConsumer : Bool
    analyticRealizationRequiresSameObjectWeld : Bool
    completedWeldYieldsLiteralCosineEquality : Bool
    completedWeldYieldsLiteralTargetGapEquality : Bool
    finitePhaseClassItselfPaysAnalyticWeld : Bool
    actualUniversalPoleQuotientWeldInhabitedHere : Bool
    finiteNearBudgetPaidHere : Bool
    strictJointMarginPaidHere : Bool
    rhDerived : Bool
open PhaseResidualRealizationBoundary public

canonicalPhaseResidualRealizationBoundary : PhaseResidualRealizationBoundary
canonicalPhaseResidualRealizationBoundary =
  phase-residual-realization-boundary
    true
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
    false

data PhaseResidualRealizationResidual : Set where
  inhabitSameObjectUniversalPoleQuotientWeld : PhaseResidualRealizationResidual
  pushLiteralCosineEqualityThroughCellResponse : PhaseResidualRealizationResidual
  aggregateCellEqualitiesOverFiniteNearSum : PhaseResidualRealizationResidual
  derivePhaseSensitiveFiniteNearBudget : PhaseResidualRealizationResidual
  combineWithOwnedFarShellOnlyAfterNearBudget : PhaseResidualRealizationResidual

firstPhaseResidualRealizationResidual : PhaseResidualRealizationResidual
firstPhaseResidualRealizationResidual = inhabitSameObjectUniversalPoleQuotientWeld
