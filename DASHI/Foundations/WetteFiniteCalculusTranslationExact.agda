module DASHI.Foundations.WetteFiniteCalculusTranslationExact where

------------------------------------------------------------------------
-- FINITE CALCULUS TRANSLATION / EQUICONSISTENCY BOUNDARY
--
-- Motivation: contemporary criticism of Wette turns in part on whether the
-- formal system under discussion is actually related to ordinary arithmetic by
-- an adequate proof translation.  This module makes that obligation explicit.
--
-- It reuses WetteFiniteDeductionTraceExact as the proof carrier.  A translation
-- must map both syntax and generators and must commute with every one-step rule.
-- Only then are arbitrary finite derivations transported.
--
-- This is deliberately weaker than semantic equivalence, conservativity, or an
-- interpretation theorem for Wette's historical system.  Those require further
-- source-specific data.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.List using (map)

import DASHI.Foundations.WetteConstructiveAutomatonExact as W
import DASHI.Foundations.WetteFiniteDeductionTraceExact as Trace

------------------------------------------------------------------------
-- Rule-respecting translation between two finite calculi.
------------------------------------------------------------------------

record FiniteCalculusTranslation
  {sourceMachine targetMachine : W.WetteMachineSpec}
  (source : W.WetteDeductionSimulation sourceMachine)
  (target : W.WetteDeductionSimulation targetMachine) : Set₁ where
  field
    mapTerm : W.Syntax source → W.Syntax target
    mapGenerator : W.Generator sourceMachine → W.Generator targetMachine
    stepCommutes :
      (g : W.Generator sourceMachine) →
      (term : W.Syntax source) →
      mapTerm (W.syntaxStep source g term)
      ≡ W.syntaxStep target (mapGenerator g) (mapTerm term)

open FiniteCalculusTranslation public

mapTrace :
  {sourceMachine targetMachine : W.WetteMachineSpec}
  {source : W.WetteDeductionSimulation sourceMachine}
  {target : W.WetteDeductionSimulation targetMachine} →
  FiniteCalculusTranslation source target →
  List (W.Generator sourceMachine) →
  List (W.Generator targetMachine)
mapTrace translation = map (mapGenerator translation)

runSyntax-cong :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  (actions : List (W.Generator machine)) →
  {left right : W.Syntax simulation} →
  left ≡ right →
  Trace.runSyntax simulation actions left
  ≡ Trace.runSyntax simulation actions right
runSyntax-cong simulation [] refl = refl
runSyntax-cong simulation (action ∷ rest) equality =
  runSyntax-cong simulation rest
    (cong (W.syntaxStep simulation action) equality)

translationRunCommutes :
  {sourceMachine targetMachine : W.WetteMachineSpec} →
  {source : W.WetteDeductionSimulation sourceMachine} →
  {target : W.WetteDeductionSimulation targetMachine} →
  (translation : FiniteCalculusTranslation source target) →
  (actions : List (W.Generator sourceMachine)) →
  (term : W.Syntax source) →
  mapTerm translation (Trace.runSyntax source actions term)
  ≡
  Trace.runSyntax target (mapTrace translation actions)
    (mapTerm translation term)
translationRunCommutes translation [] term = refl
translationRunCommutes {source = source} {target = target}
  translation (action ∷ rest) term =
  trans
    (translationRunCommutes translation rest
      (W.syntaxStep source action term))
    (runSyntax-cong target (mapTrace translation rest)
      (stepCommutes translation action term))

translateFiniteDerivation :
  {sourceMachine targetMachine : W.WetteMachineSpec} →
  {source : W.WetteDeductionSimulation sourceMachine} →
  {target : W.WetteDeductionSimulation targetMachine} →
  (translation : FiniteCalculusTranslation source target) →
  {left right : W.Syntax source} →
  Trace.FiniteDerivationWitness source left right →
  Trace.FiniteDerivationWitness target
    (mapTerm translation left)
    (mapTerm translation right)
translateFiniteDerivation translation {left} derivation =
  Trace.finiteDerivationWitness
    (mapTrace translation (Trace.actions derivation))
    (trans
      (sym
        (translationRunCommutes translation
          (Trace.actions derivation) left))
      (cong (mapTerm translation) (Trace.reaches derivation)))

------------------------------------------------------------------------
-- Contradiction transport is a separate datum: translating arbitrary proofs
-- does not identify which formula is the designated contradiction.
------------------------------------------------------------------------

record ContradictionPreservingTranslation
  {sourceMachine targetMachine : W.WetteMachineSpec}
  (source : W.WetteDeductionSimulation sourceMachine)
  (target : W.WetteDeductionSimulation targetMachine) : Set₁ where
  field
    translation : FiniteCalculusTranslation source target
    sourceBase : W.Syntax source
    targetBase : W.Syntax target
    sourceContradiction : W.Syntax source
    targetContradiction : W.Syntax target

    basePreserved :
      mapTerm translation sourceBase ≡ targetBase
    contradictionPreserved :
      mapTerm translation sourceContradiction ≡ targetContradiction

open ContradictionPreservingTranslation public

sourceContradictionDerivationTransfers :
  {sourceMachine targetMachine : W.WetteMachineSpec} →
  {source : W.WetteDeductionSimulation sourceMachine} →
  {target : W.WetteDeductionSimulation targetMachine} →
  (bridge : ContradictionPreservingTranslation source target) →
  Trace.FiniteDerivationWitness source
    (sourceBase bridge) (sourceContradiction bridge) →
  Trace.FiniteDerivationWitness target
    (targetBase bridge) (targetContradiction bridge)
sourceContradictionDerivationTransfers bridge derivation
  rewrite sym (basePreserved bridge)
        | sym (contradictionPreserved bridge) =
  translateFiniteDerivation (translation bridge) derivation

------------------------------------------------------------------------
-- Finite proof-theoretic consistency and two-way contradiction preservation.
------------------------------------------------------------------------

FiniteConsistent :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  W.Syntax simulation → W.Syntax simulation → Set
FiniteConsistent simulation base contradiction =
  ¬ Trace.FiniteDerivationWitness simulation base contradiction

consistencyTransfersBackward :
  {sourceMachine targetMachine : W.WetteMachineSpec} →
  {source : W.WetteDeductionSimulation sourceMachine} →
  {target : W.WetteDeductionSimulation targetMachine} →
  (bridge : ContradictionPreservingTranslation source target) →
  FiniteConsistent target
    (targetBase bridge) (targetContradiction bridge) →
  FiniteConsistent source
    (sourceBase bridge) (sourceContradiction bridge)
consistencyTransfersBackward bridge targetConsistent sourceContradictionProof =
  targetConsistent
    (sourceContradictionDerivationTransfers bridge sourceContradictionProof)

record FiniteEquiconsistencyWitness
  {leftMachine rightMachine : W.WetteMachineSpec}
  (left : W.WetteDeductionSimulation leftMachine)
  (right : W.WetteDeductionSimulation rightMachine) : Set₁ where
  field
    leftToRight : ContradictionPreservingTranslation left right
    rightToLeft : ContradictionPreservingTranslation right left

open FiniteEquiconsistencyWitness public

leftConsistencyFromRight :
  {leftMachine rightMachine : W.WetteMachineSpec} →
  {left : W.WetteDeductionSimulation leftMachine} →
  {right : W.WetteDeductionSimulation rightMachine} →
  (witness : FiniteEquiconsistencyWitness left right) →
  FiniteConsistent right
    (targetBase (leftToRight witness))
    (targetContradiction (leftToRight witness)) →
  FiniteConsistent left
    (sourceBase (leftToRight witness))
    (sourceContradiction (leftToRight witness))
leftConsistencyFromRight witness =
  consistencyTransfersBackward (leftToRight witness)

rightConsistencyFromLeft :
  {leftMachine rightMachine : W.WetteMachineSpec} →
  {left : W.WetteDeductionSimulation leftMachine} →
  {right : W.WetteDeductionSimulation rightMachine} →
  (witness : FiniteEquiconsistencyWitness left right) →
  FiniteConsistent left
    (targetBase (rightToLeft witness))
    (targetContradiction (rightToLeft witness)) →
  FiniteConsistent right
    (sourceBase (rightToLeft witness))
    (sourceContradiction (rightToLeft witness))
rightConsistencyFromLeft witness =
  consistencyTransfersBackward (rightToLeft witness)

------------------------------------------------------------------------
-- Historical/claim boundary.
------------------------------------------------------------------------

record WetteTranslationBoundary : Set where
  constructor wetteTranslationBoundary
  field
    oneStepRuleRespectingTranslationLiftsToFiniteProofs : Bool
    oneStepRuleRespectingTranslationLiftsToFiniteProofsIsTrue :
      oneStepRuleRespectingTranslationLiftsToFiniteProofs ≡ true

    contradictionPreservationRequiredSeparately : Bool
    contradictionPreservationRequiredSeparatelyIsTrue :
      contradictionPreservationRequiredSeparately ≡ true

    twoWayContradictionTranslationYieldsFiniteEquiconsistency : Bool
    twoWayContradictionTranslationYieldsFiniteEquiconsistencyIsTrue :
      twoWayContradictionTranslationYieldsFiniteEquiconsistency ≡ true

    finiteEquiconsistencyIsSemanticEquivalence : Bool
    finiteEquiconsistencyIsSemanticEquivalenceIsFalse :
      finiteEquiconsistencyIsSemanticEquivalence ≡ false

    historicalWetteToOrdinaryArithmeticTranslationRecovered : Bool
    historicalWetteToOrdinaryArithmeticTranslationRecoveredIsFalse :
      historicalWetteToOrdinaryArithmeticTranslationRecovered ≡ false

canonicalWetteTranslationBoundary : WetteTranslationBoundary
canonicalWetteTranslationBoundary =
  wetteTranslationBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
