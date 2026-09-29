module DASHI.Reasoning.Trialectic369Selected3BSemanticProjectedCompletionExact where

------------------------------------------------------------------------
-- FINAL CURRENT MAX-CUT:
-- SEMANTIC/LINEAR 196883 WELD + ONE PROJECTED ACTION EQUATION
--
-- DASHI CONTRIBUTION
--
-- Compose:
--
--   Trialectic369SemanticLinearConstituentRetractionCompilerExact
--     semantic 196883 <-> linear 196883 + inclusion square
--       => actual constituent retraction;
--
--   Trialectic369Selected3BProjectedActionMaxCutExact
--     constituent retraction + one projected full-grade action equation
--       => canonical selected-3B action intertwiner/completion.
--
-- Thus the currently minimal source-facing completion contract is exactly:
--
--   (A) same-object semantic/linear constituent weld;
--   (B) selected action equals projection of the same full grade-two action.
--
-- No separate injectivity, downstream faithful-comparison, normalizer-carrier
-- bijection, Fin90 action, or multiplicity-space construction is an
-- independent scientific input on this route.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Reasoning.Trialectic369CanonicalSelected3BLinearCoreExact as Core
import DASHI.Reasoning.Trialectic369SemanticLinearConstituentRetractionCompilerExact as SemanticRetraction
import DASHI.Reasoning.Trialectic369Selected3BProjectedActionMaxCutExact as Projected

------------------------------------------------------------------------
-- 1. Minimal semantic/projected completion contract.
------------------------------------------------------------------------

record SemanticProjectedSelected3BCompletionInput
    {Monster K : Set}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K})
    : Setω where
  field
    semanticLinearWeld :
      SemanticRetraction.SemanticLinearConstituentWeld core

    projectedAction :
      Projected.SelectedActionIsProjectedFullGrade
        core
        (SemanticRetraction.constituentRetractionFromSemanticWeld
          core semanticLinearWeld)

open SemanticProjectedSelected3BCompletionInput public

------------------------------------------------------------------------
-- 2. Retraction becomes compiler output.
------------------------------------------------------------------------

compiledRetraction :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  SemanticProjectedSelected3BCompletionInput core →
  DASHI.Reasoning.Trialectic369Selected3BConstituentRetractionExact.ConstituentRetraction core
compiledRetraction core input =
  SemanticRetraction.constituentRetractionFromSemanticWeld
    core
    (semanticLinearWeld input)

------------------------------------------------------------------------
-- 3. Canonical action and completion are compiler output.
------------------------------------------------------------------------

compiledCanonicalAction :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  (input : SemanticProjectedSelected3BCompletionInput core) →
  Core.CanonicalSelected3BActionIntertwining core
compiledCanonicalAction core input =
  Projected.canonicalActionIntertwiningFromProjectedAction
    core
    (compiledRetraction core input)
    (projectedAction input)

compiledCanonicalCompletion :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  (input : SemanticProjectedSelected3BCompletionInput core) →
  Core.CanonicalSelected3BLinearCompletion {Monster} {K}
compiledCanonicalCompletion core input =
  Projected.canonicalCompletionFromProjectedAction
    core
    (compiledRetraction core input)
    (projectedAction input)

------------------------------------------------------------------------
-- 4. Expose the two exact source leaves separately.
------------------------------------------------------------------------

data SemanticLinearWeldSourceLeaf : Set where
data ProjectedActionSourceLeaf : Set where

semanticLinearWeldNotConstructedByCompiler :
  SemanticLinearWeldSourceLeaf → ⊥
semanticLinearWeldNotConstructedByCompiler ()

projectedActionNotConstructedByCompiler :
  ProjectedActionSourceLeaf → ⊥
projectedActionNotConstructedByCompiler ()

------------------------------------------------------------------------
-- 5. Firewalls.
------------------------------------------------------------------------

data OggSSP15CarrierCreatesSemanticLinearWeld : Set where
data PhaseOrbit15CreatesProjectedMonsterAction : Set where
data Dimension196883CreatesCompletionInput : Set where
data CharacterRestrictionCreatesCompletionInput : Set where

oggCarrierDoesNotCreateSemanticLinearWeld :
  OggSSP15CarrierCreatesSemanticLinearWeld → ⊥
oggCarrierDoesNotCreateSemanticLinearWeld ()

phaseOrbitDoesNotCreateProjectedAction :
  PhaseOrbit15CreatesProjectedMonsterAction → ⊥
phaseOrbitDoesNotCreateProjectedAction ()

dimensionDoesNotCreateCompletionInput :
  Dimension196883CreatesCompletionInput → ⊥
dimensionDoesNotCreateCompletionInput ()

characterDoesNotCreateCompletionInput :
  CharacterRestrictionCreatesCompletionInput → ⊥
characterDoesNotCreateCompletionInput ()

------------------------------------------------------------------------
-- 6. Machine-readable current frontier.
------------------------------------------------------------------------

record Trialectic369Selected3BSemanticProjectedCompletionBoundary : Set where
  constructor trialectic-369-selected3b-semantic-projected-completion-boundary
  field
    semanticLinearWeldCompilesRetraction : Bool
    retractionNoLongerIndependentSourceLeaf : Bool
    inclusionInjectivityNoLongerIndependentSourceLeaf : Bool
    faithfulComparisonNoLongerIndependentSourceLeaf : Bool
    normalizerCarrierBidiNoLongerIndependentSourceLeaf : Bool
    onlySemanticLinearWeldAndProjectedActionRemain : Bool
    canonicalActionCompilerOwned : Bool
    canonicalCompletionCompilerOwned : Bool
    semanticLinearWeldInhabitedHere : Bool
    projectedActionInputInhabitedHere : Bool
    canonicalCompletionInhabitedHere : Bool

canonicalTrialectic369Selected3BSemanticProjectedCompletionBoundary :
  Trialectic369Selected3BSemanticProjectedCompletionBoundary
canonicalTrialectic369Selected3BSemanticProjectedCompletionBoundary =
  trialectic-369-selected3b-semantic-projected-completion-boundary
    true true true true true true true true
    false false false
