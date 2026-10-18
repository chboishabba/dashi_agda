module DASHI.Reasoning.Trialectic369Selected3BSemanticProjectedCompletionExact where

------------------------------------------------------------------------
-- CORRECTED CURRENT MAX-CUT:
-- LINEAR RETRACTION + ONE PROJECTED ACTION EQUATION
--
-- The semantic 196883 carrier is a finite coordinate/basis-label object, not
-- the full vector carrier.  Therefore the previous attempt to compile the
-- linear retraction from a semantic<->linear carrier equality is rejected.
--
-- Correct source-facing contract:
--
--   (A) actual linear ConstituentRetraction on the 196883 direct summand;
--   (B) selected action equals projection of the SAME full grade-two action.
--
-- An optional SemanticLinearConstituentBasisFrame may accompany (A), but it is
-- descriptive/basis data and does not replace the linear retraction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Reasoning.Trialectic369CanonicalSelected3BLinearCoreExact as Core
import DASHI.Reasoning.Trialectic369Selected3BConstituentRetractionExact as Retraction
import DASHI.Reasoning.Trialectic369Selected3BProjectedActionMaxCutExact as Projected
import DASHI.Reasoning.Trialectic369SemanticLinearConstituentRetractionCompilerExact as SemanticBasis

------------------------------------------------------------------------
-- 1. Correct minimal completion input.
------------------------------------------------------------------------

record ProjectedSelected3BCompletionInput
    {Monster K : Set}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K})
    : Setω where
  field
    linearRetraction :
      Retraction.ConstituentRetraction core

    projectedAction :
      Projected.SelectedActionIsProjectedFullGrade
        core linearRetraction

open ProjectedSelected3BCompletionInput public

------------------------------------------------------------------------
-- 2. Optional semantic coordinate/basis annotation.
------------------------------------------------------------------------

record ProjectedSelected3BCompletionWithBasis
    {Monster K : Set}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K})
    : Setω where
  field
    completionInput : ProjectedSelected3BCompletionInput core
    semanticBasisFrame :
      SemanticBasis.SemanticLinearConstituentBasisFrame core

open ProjectedSelected3BCompletionWithBasis public

------------------------------------------------------------------------
-- 3. Canonical action and completion are compiler output.
------------------------------------------------------------------------

compiledCanonicalAction :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  (input : ProjectedSelected3BCompletionInput core) →
  Core.CanonicalSelected3BActionIntertwining core
compiledCanonicalAction core input =
  Projected.canonicalActionIntertwiningFromProjectedAction
    core
    (linearRetraction input)
    (projectedAction input)

compiledCanonicalCompletion :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  (input : ProjectedSelected3BCompletionInput core) →
  Core.CanonicalSelected3BLinearCompletion {Monster} {K}
compiledCanonicalCompletion core input =
  Projected.canonicalCompletionFromProjectedAction
    core
    (linearRetraction input)
    (projectedAction input)

------------------------------------------------------------------------
-- 4. Exact two remaining source leaves.
------------------------------------------------------------------------

data LinearRetractionSourceLeaf : Set where
data ProjectedActionSourceLeaf : Set where

linearRetractionNotConstructedByCompiler :
  LinearRetractionSourceLeaf → ⊥
linearRetractionNotConstructedByCompiler ()

projectedActionNotConstructedByCompiler :
  ProjectedActionSourceLeaf → ⊥
projectedActionNotConstructedByCompiler ()

------------------------------------------------------------------------
-- 5. Firewalls.
------------------------------------------------------------------------

data SemanticBasisFrameCreatesRetraction : Set where
data OggSSP15CarrierCreatesLinearRetraction : Set where
data PhaseOrbit15CreatesProjectedMonsterAction : Set where
data Dimension196883CreatesCompletionInput : Set where

semanticBasisDoesNotCreateRetraction :
  SemanticBasisFrameCreatesRetraction → ⊥
semanticBasisDoesNotCreateRetraction ()

oggCarrierDoesNotCreateLinearRetraction :
  OggSSP15CarrierCreatesLinearRetraction → ⊥
oggCarrierDoesNotCreateLinearRetraction ()

phaseOrbitDoesNotCreateProjectedAction :
  PhaseOrbit15CreatesProjectedMonsterAction → ⊥
phaseOrbitDoesNotCreateProjectedAction ()

dimensionDoesNotCreateCompletionInput :
  Dimension196883CreatesCompletionInput → ⊥
dimensionDoesNotCreateCompletionInput ()

------------------------------------------------------------------------
-- 6. Machine-readable corrected frontier.
------------------------------------------------------------------------

record Trialectic369Selected3BSemanticProjectedCompletionBoundary : Set where
  constructor trialectic-369-selected3b-semantic-projected-completion-boundary
  field
    semanticBasisFrameIsOptionalNotCarrierEquality : Bool
    semanticBasisFrameDoesNotCompileRetraction : Bool
    actualLinearRetractionIsSourceLeaf : Bool
    projectedActionEquationIsSourceLeaf : Bool
    inclusionInjectivityNoLongerIndependentLeaf : Bool
    faithfulComparisonNoLongerIndependentLeaf : Bool
    onlyLinearRetractionAndProjectedActionRemain : Bool
    canonicalActionCompilerOwned : Bool
    canonicalCompletionCompilerOwned : Bool
    actualLinearRetractionInhabitedHere : Bool
    projectedActionInputInhabitedHere : Bool
    canonicalCompletionInhabitedHere : Bool

canonicalTrialectic369Selected3BSemanticProjectedCompletionBoundary :
  Trialectic369Selected3BSemanticProjectedCompletionBoundary
canonicalTrialectic369Selected3BSemanticProjectedCompletionBoundary =
  trialectic-369-selected3b-semantic-projected-completion-boundary
    true true true true true true true true true
    false false false
