module DASHI.Mathematics.Complexity.PNotEqualsNPInitialStateImageUnconstrainedExact where

------------------------------------------------------------------------
-- THE CURRENT CLAY CLOSURE HAS NO SPECIAL INITIAL-ROOT CONSTRUCTOR
--
-- The concrete finite-code closure accepts
--
--   initial : BoundedSelfReferenceState
--
-- directly.  No field constrains currentFormula initial to an image generated
-- from the candidate SAT decider or from the finite self-specializing code.
--
-- Consequently every Cook formula can be installed as the current formula of
-- some budget-fitting initial state.  The initial syntactic image is therefore
-- universal; any genuine special law must come from the MISSING coupling among
--
--   candidate/self-code,
--   Q1 progress,
--   successful direct-DP construction,
--   and opposite-SAT terminal semantics.
--
-- This owner makes that boundary exact.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2

------------------------------------------------------------------------
-- Canonical zero-overhead initial state for any Cook formula.
------------------------------------------------------------------------

initialStateForFormula :
  Cook.BooleanFormula →
  Q2.BoundedSelfReferenceState
initialStateForFormula formula =
  Q2.bounded-self-reference-state
    formula
    zero
    zero
    (Size.formulaNodeCount formula)
    fits
  where
    fits :
      Size.formulaNodeCount formula + (zero + zero)
      ≤
      Size.formulaNodeCount formula
    fits =
      NatP.≤-refl

initialStateForFormulaCurrentExact :
  (formula : Cook.BooleanFormula) →
  Q2.currentFormula
      (initialStateForFormula formula)
  ≡
  formula
initialStateForFormulaCurrentExact formula =
  Agda.Builtin.Equality.refl

initialStateForFormulaMeasureExact :
  (formula : Cook.BooleanFormula) →
  Q2.recursiveMeasure
      (initialStateForFormula formula)
  ≡
  Size.formulaNodeCount formula
initialStateForFormulaMeasureExact formula =
  Agda.Builtin.Equality.refl

initialStateForFormulaBudgetExact :
  (formula : Cook.BooleanFormula) →
  Q2.resourceBudget
      (initialStateForFormula formula)
  ≡
  Size.formulaNodeCount formula
initialStateForFormulaBudgetExact formula =
  Agda.Builtin.Equality.refl

------------------------------------------------------------------------
-- Universal syntactic image statement.
------------------------------------------------------------------------

record InitialStateRealization
    (formula : Cook.BooleanFormula) : Set where
  constructor initial-state-realization
  field
    state :
      Q2.BoundedSelfReferenceState

    currentFormulaExact :
      Q2.currentFormula state
      ≡
      formula

open InitialStateRealization public

everyCookFormulaOccursAsInitialCurrentFormula :
  (formula : Cook.BooleanFormula) →
  InitialStateRealization formula
everyCookFormulaOccursAsInitialCurrentFormula formula =
  initial-state-realization
    (initialStateForFormula formula)
    (initialStateForFormulaCurrentExact formula)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- There is no nontrivial theorem of the form
--
--   "every initial self-instantiation formula satisfies invariant I"
--
-- derivable from the current initial-state interface alone, unless I already
-- holds for every Cook Boolean formula.
--
-- In particular, block equality is not excluded by initial-state syntax.
--
-- Therefore the live P theorem cannot be "characterize the image of the
-- initial-root constructor": that constructor does not yet exist.
--
-- The missing theorem must instead construct a candidate-dependent initial
-- package and prove a progress/semantic coupling strong enough that the
-- direct-DP constructor is REQUIRED to succeed on the relevant live state.
------------------------------------------------------------------------
