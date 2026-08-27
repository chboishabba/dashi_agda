module DASHI.Foundations.WetteFormalClaimTransportBridgeExact where

------------------------------------------------------------------------
-- WETTE / GENERIC FORMAL CLAIM TRANSPORT BRIDGE
--
-- This module instantiates the generic FormalClaimTransportGeometry with the
-- finite-calculus translation already developed for Wette.  The key point is
-- that a source rule does not merely have a target image: the one-step result
-- itself factors through the translated source term by the target rule.
--
-- Thus each generator gives an actual commuting square instance of the generic
-- claim-transport theorem.  Historical fidelity, contradiction preservation,
-- semantic soundness and metatheoretic reflection remain separate coordinates.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.FormalClaimTransportGeometryExact as Geometry
import DASHI.Foundations.WetteConstructiveAutomatonExact as W
import DASHI.Foundations.WetteFiniteCalculusTranslationExact as Translation

------------------------------------------------------------------------
-- One source rule is a claim consumer over source syntax:
--
--   claim(term) = mapTerm (sourceStep g term)
--
-- The retained representation is `mapTerm term`.  The target rule provides the
-- factor, and Translation.stepCommutes is exactly the transport law.
------------------------------------------------------------------------

sourceRuleImage :
  {sourceMachine targetMachine : W.WetteMachineSpec} →
  {source : W.WetteDeductionSimulation sourceMachine} →
  {target : W.WetteDeductionSimulation targetMachine} →
  (translation : Translation.FiniteCalculusTranslation source target) →
  W.Generator sourceMachine →
  W.Syntax source →
  W.Syntax target
sourceRuleImage {source = source} translation g term =
  Translation.mapTerm translation (W.syntaxStep source g term)

fixedRuleClaimTransport :
  {sourceMachine targetMachine : W.WetteMachineSpec} →
  {source : W.WetteDeductionSimulation sourceMachine} →
  {target : W.WetteDeductionSimulation targetMachine} →
  (translation : Translation.FiniteCalculusTranslation source target) →
  (g : W.Generator sourceMachine) →
  Geometry.ClaimTransport
    (Translation.mapTerm translation)
    (sourceRuleImage translation g)
fixedRuleClaimTransport {target = target} translation g =
  Geometry.claimTransport
    (W.syntaxStep target (Translation.mapGenerator translation g))
    (Translation.stepCommutes translation g)

------------------------------------------------------------------------
-- The same theorem can be exposed through the repository's existing
-- factorized-refinement / descent owner.  This is the shared abstraction behind
-- observer descent and proof-translation commutation.
------------------------------------------------------------------------

fixedRuleFactorsThroughTranslation :
  {sourceMachine targetMachine : W.WetteMachineSpec} →
  {source : W.WetteDeductionSimulation sourceMachine} →
  {target : W.WetteDeductionSimulation targetMachine} →
  (translation : Translation.FiniteCalculusTranslation source target) →
  (g : W.Generator sourceMachine) →
  Geometry.ClaimFactorsThrough
    (Translation.mapTerm translation)
    (sourceRuleImage translation g)
fixedRuleFactorsThroughTranslation translation g =
  Geometry.toFactorizedRefinement
    (fixedRuleClaimTransport translation g)

------------------------------------------------------------------------
-- A collision in the translated representation that changes the mapped rule
-- result would refute the claimed commuting square.  The generic non-descent
-- theorem supplies that obstruction directly.
------------------------------------------------------------------------

ruleCollisionRefutesTransport :
  {sourceMachine targetMachine : W.WetteMachineSpec} →
  {source : W.WetteDeductionSimulation sourceMachine} →
  {target : W.WetteDeductionSimulation targetMachine} →
  (translation : Translation.FiniteCalculusTranslation source target) →
  (g : W.Generator sourceMachine) →
  Geometry.ClaimNonTransportWitness
    (Translation.mapTerm translation)
    (sourceRuleImage translation g) →
  ⊥
ruleCollisionRefutesTransport translation g witness =
  Geometry.claimNonTransportWitnessBlocksTransport witness
    (fixedRuleClaimTransport translation g)

------------------------------------------------------------------------
-- Coordinate profile for the current Wette tranche.
--
-- This is deliberately proposition-valued rather than a score.  It witnesses
-- that rule-respecting proof translation is available as an interface while
-- stronger historical/semantic coordinates remain independent obligations.
------------------------------------------------------------------------

currentWetteComparisonProfile : Geometry.ComparisonStrengthProfile
currentWetteComparisonProfile =
  Geometry.comparisonStrengthProfile supports
  where
    supports : Geometry.ComparisonAxis → Set
    supports Geometry.proofTranslationStrength = ⊤
    supports Geometry.representationFidelity = ⊤
    supports Geometry.derivationalFidelity = ⊤
    supports Geometry.historicalFidelity = ⊥
    supports Geometry.contradictionPreservation = ⊥
    supports Geometry.interpretability = ⊥
    supports Geometry.conservativity = ⊥
    supports Geometry.relativeCompleteness = ⊥
    supports Geometry.semanticSoundness = ⊥
    supports Geometry.semanticCompleteness = ⊥
    supports Geometry.reflectionStrength = ⊥
    supports Geometry.metatheoreticConclusion = ⊥

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record WetteFormalClaimTransportBoundary : Set where
  constructor wetteFormalClaimTransportBoundary
  field
    ruleCommutationInstantiatesGenericClaimTransport : Bool
    ruleCommutationInstantiatesGenericClaimTransportIsTrue :
      ruleCommutationInstantiatesGenericClaimTransport ≡ true

    collisionCanRefuteClaimTransport : Bool
    collisionCanRefuteClaimTransportIsTrue :
      collisionCanRefuteClaimTransport ≡ true

    proofTranslationCoordinateImpliesSemanticSoundnessCoordinate : Bool
    proofTranslationCoordinateImpliesSemanticSoundnessCoordinateIsFalse :
      proofTranslationCoordinateImpliesSemanticSoundnessCoordinate ≡ false

    proofTranslationCoordinateImpliesHistoricalFidelityCoordinate : Bool
    proofTranslationCoordinateImpliesHistoricalFidelityCoordinateIsFalse :
      proofTranslationCoordinateImpliesHistoricalFidelityCoordinate ≡ false

    relativeCompletenessIsDefinitionallyNextLinearLevel : Bool
    relativeCompletenessIsDefinitionallyNextLinearLevelIsFalse :
      relativeCompletenessIsDefinitionallyNextLinearLevel ≡ false

canonicalWetteFormalClaimTransportBoundary : WetteFormalClaimTransportBoundary
canonicalWetteFormalClaimTransportBoundary =
  wetteFormalClaimTransportBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
