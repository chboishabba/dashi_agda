module DASHI.Foundations.WetteFiniteTraceConsistencyObstructionExact where

------------------------------------------------------------------------
-- FINITE TRACE CONSISTENCY OBSTRUCTION
--
-- Cross-pollinate the finite mixed-rule trace theorem with the Bernays/Wette
-- conditional reduction.  This is a small generic soundness pattern:
--
--   invariant true at the derivation base
--   + every rule preserves the invariant
--   + designated contradiction violates the invariant
--   -> no finite derivation of contradiction.
--
-- If a supplied Bernays-style reduction turns every finite proof of the
-- consistency sentence into a finite proof of contradiction, the same
-- invariant then rules out a finite proof of that consistency sentence.
--
-- This is not a proof that ordinary arithmetic is consistent.  The invariant,
-- base witness, contradiction exclusion, and reduction are all explicit inputs.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.WetteConstructiveAutomatonExact as W
import DASHI.Foundations.WetteFiniteDeductionTraceExact as Trace

------------------------------------------------------------------------
-- No finite contradiction trace under an explicit preserved invariant.
------------------------------------------------------------------------

noFiniteDerivationToInvariantExcludedTarget :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  (invariant : Trace.SyntaxInvariant simulation) →
  {source target : W.Syntax simulation} →
  Trace.Holds invariant source →
  (Trace.Holds invariant target → ⊥) →
  Trace.FiniteDerivationWitness simulation source target →
  ⊥
noFiniteDerivationToInvariantExcludedTarget simulation invariant
  {source} {target} sourceHolds targetExcluded derivation =
  targetExcluded
    (transportTarget
      (Trace.finiteDerivationPreservesInvariant simulation invariant
        (Trace.actions derivation) source sourceHolds))
  where
  transportTarget :
    Trace.Holds invariant
      (Trace.runSyntax simulation (Trace.actions derivation) source) →
    Trace.Holds invariant target
  transportTarget holds
    rewrite Trace.reaches derivation = holds

------------------------------------------------------------------------
-- Bernays-style consequence: if every finite proof of Con yields a finite
-- contradiction proof, then an invariant excluding contradiction also excludes
-- such a finite proof of Con.
------------------------------------------------------------------------

noFiniteConsistencyProofUnderInvariantAndReduction :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  (invariant : Trace.SyntaxInvariant simulation) →
  {axiomState consistencySentence contradictionSentence :
    W.Syntax simulation} →
  Trace.Holds invariant axiomState →
  (Trace.Holds invariant contradictionSentence → ⊥) →
  (Trace.FiniteDerivationWitness simulation axiomState consistencySentence →
   Trace.FiniteDerivationWitness simulation axiomState contradictionSentence) →
  Trace.FiniteDerivationWitness simulation axiomState consistencySentence →
  ⊥
noFiniteConsistencyProofUnderInvariantAndReduction simulation invariant
  {axiomState} {consistencySentence} {contradictionSentence}
  axiomHolds contradictionExcluded reduction consistencyProof =
  noFiniteDerivationToInvariantExcludedTarget simulation invariant
    axiomHolds contradictionExcluded (reduction consistencyProof)

------------------------------------------------------------------------
-- Package the exact obligations so a historical reconstruction can expose
-- which component is actually supplied by Wette and which belongs to an
-- external metatheory/model.
------------------------------------------------------------------------

record FiniteConsistencyObstructionData
  {machine : W.WetteMachineSpec}
  (simulation : W.WetteDeductionSimulation machine)
  (axiomState consistencySentence contradictionSentence :
    W.Syntax simulation) : Set₁ where
  field
    invariant : Trace.SyntaxInvariant simulation
    axiomHolds : Trace.Holds invariant axiomState
    contradictionExcluded :
      Trace.Holds invariant contradictionSentence → ⊥
    consistencyToContradiction :
      Trace.FiniteDerivationWitness simulation axiomState consistencySentence →
      Trace.FiniteDerivationWitness simulation axiomState contradictionSentence

open FiniteConsistencyObstructionData public

finiteConsistencyProofImpossible :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  (axiomState consistencySentence contradictionSentence :
    W.Syntax simulation) →
  FiniteConsistencyObstructionData
    simulation axiomState consistencySentence contradictionSentence →
  Trace.FiniteDerivationWitness simulation axiomState consistencySentence →
  ⊥
finiteConsistencyProofImpossible simulation axiomState consistencySentence
  contradictionSentence data =
  noFiniteConsistencyProofUnderInvariantAndReduction simulation
    (invariant data)
    (axiomHolds data)
    (contradictionExcluded data)
    (consistencyToContradiction data)

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record WetteFiniteConsistencyObstructionBoundary : Set where
  constructor wetteFiniteConsistencyObstructionBoundary
  field
    preservedInvariantCanExcludeFiniteContradiction : Bool
    preservedInvariantCanExcludeFiniteContradictionIsTrue :
      preservedInvariantCanExcludeFiniteContradiction ≡ true

    reductionThenExcludesFiniteConsistencyProof : Bool
    reductionThenExcludesFiniteConsistencyProofIsTrue :
      reductionThenExcludesFiniteConsistencyProof ≡ true

    invariantIsAutomaticallyArithmeticTruth : Bool
    invariantIsAutomaticallyArithmeticTruthIsFalse :
      invariantIsAutomaticallyArithmeticTruth ≡ false

    historicalWetteInvariantRecovered : Bool
    historicalWetteInvariantRecoveredIsFalse :
      historicalWetteInvariantRecovered ≡ false

    theoremProvesOrdinaryArithmeticConsistency : Bool
    theoremProvesOrdinaryArithmeticConsistencyIsFalse :
      theoremProvesOrdinaryArithmeticConsistency ≡ false

canonicalWetteFiniteConsistencyObstructionBoundary :
  WetteFiniteConsistencyObstructionBoundary
canonicalWetteFiniteConsistencyObstructionBoundary =
  wetteFiniteConsistencyObstructionBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
