module DASHI.Core.CounterexampleGuidedConsumerRefinementExact where

------------------------------------------------------------------------
-- COUNTEREXAMPLE-GUIDED CONSUMER REFINEMENT
--
-- Common pattern:
--   coarse claim -> distinguishing witness -> refine -> retest.
--
-- A witness repairs only the witnessed collision.  It does not promote the
-- refined observer to global future safety without a separate theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ReopenableConsumerInterventionKernelExact as Core

record Refinement
    {Fine Coarse Refined : Set}
    (coarse : Fine → Coarse)
    (refined : Fine → Refined) : Set₁ where
  constructor refinement
  field
    forget : Refined → Coarse
    factorises : ∀ state → coarse state ≡ forget (refined state)

open Refinement public

record WitnessSplit
    {Fine Coarse Refined Output : Set}
    {coarse : Fine → Coarse}
    {consume : Fine → Output}
    (defect : Core.ConsumerDescentDefect coarse consume)
    (refined : Fine → Refined) : Set where
  constructor witnessSplit
  field
    refinedDistinguishes :
      refined (Core.left defect) ≡ refined (Core.right defect) → ⊥

open WitnessSplit public

------------------------------------------------------------------------
-- If a refined observer itself factors through the old coarse observer, it
-- cannot split an old coarse collision.  Thus a genuine witness repair proves
-- strict information gain relative to that witness.
------------------------------------------------------------------------

refinementThatFactorsThroughCoarseCannotSplitDefect :
  ∀ {Fine Coarse Refined Output}
    {coarse : Fine → Coarse}
    {consume : Fine → Output}
    (defect : Core.ConsumerDescentDefect coarse consume)
    (refined : Fine → Refined)
    (fromCoarse : Coarse → Refined)
    (refinedFactors : ∀ state → refined state ≡ fromCoarse (coarse state)) →
  WitnessSplit defect refined →
  ⊥
refinementThatFactorsThroughCoarseCannotSplitDefect defect refined fromCoarse factors split =
  refinedDistinguishes split refinedEqual
  where
    refinedEqual : refined (Core.left defect) ≡ refined (Core.right defect)
    refinedEqual
      rewrite factors (Core.left defect)
            | factors (Core.right defect)
            | Core.sameProjection defect = refl

------------------------------------------------------------------------
-- Exact repair certificate for one witness.
------------------------------------------------------------------------

record CounterexampleGuidedRefinement
    {Fine Coarse Refined Output : Set}
    (coarse : Fine → Coarse)
    (consume : Fine → Output) : Set₁ where
  constructor counterexampleGuidedRefinement
  field
    defect : Core.ConsumerDescentDefect coarse consume
    refined : Fine → Refined
    split : WitnessSplit defect refined

open CounterexampleGuidedRefinement public

record CounterexampleRefinementBoundary : Set where
  constructor counterexampleRefinementBoundary
  field
    oneSplitDoesNotProveGlobalSeparation : Agda.Builtin.Bool.Bool
    oneSplitDoesNotProveFutureSafety : Agda.Builtin.Bool.Bool
    repeatedRefinementNeedsStoppingObligation : Agda.Builtin.Bool.Bool

canonicalCounterexampleRefinementBoundary : CounterexampleRefinementBoundary
canonicalCounterexampleRefinementBoundary =
  counterexampleRefinementBoundary
    Agda.Builtin.Bool.true Agda.Builtin.Bool.true Agda.Builtin.Bool.true
