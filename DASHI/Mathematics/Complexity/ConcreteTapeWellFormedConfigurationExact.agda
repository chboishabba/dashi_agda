module DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact where

------------------------------------------------------------------------
-- EXACTLY-ONE-HEAD CONFIGURATION INVARIANT
--
-- The raw TapeRow carrier permits arbitrary lists.  Cook--Levin reverse
-- reconstruction needs genuine machine configurations, hence exactly one
-- headed cell.  A well-formed rewrite additionally requires the common prefix
-- and suffix to contain only plain tape cells.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local

data PlainCells
    {State Symbol : Set} :
    List (Local.TapeCell State Symbol) → Set where
  plainNil :
    PlainCells []

  plainCons :
    ∀ {symbol rest} →
    PlainCells rest →
    PlainCells (Local.plain symbol ∷ rest)

data ExactlyOneHead
    {State Symbol : Set} :
    List (Local.TapeCell State Symbol) → Set where
  headHere :
    ∀ {state symbol rest} →
    PlainCells rest →
    ExactlyOneHead (Local.headed state symbol ∷ rest)

  plainBefore :
    ∀ {symbol rest} →
    ExactlyOneHead rest →
    ExactlyOneHead (Local.plain symbol ∷ rest)

prependPlain :
  ∀ {State Symbol : Set}
    {prefix rest : List (Local.TapeCell State Symbol)} →
  PlainCells prefix →
  ExactlyOneHead rest →
  ExactlyOneHead (Local.append prefix rest)
prependPlain plainNil unique = unique
prependPlain (plainCons prefixPlain) unique =
  plainBefore (prependPlain prefixPlain unique)

transportExactlyOneHead :
  ∀ {State Symbol : Set}
    {left right : List (Local.TapeCell State Symbol)} →
  left ≡ right →
  ExactlyOneHead left →
  ExactlyOneHead right
transportExactlyOneHead refl witness = witness

record WellFormedRewriteOccurrence
    (machine : Local.ConcreteTapeMachine)
    (before after : Local.TapeRow machine)
    (window : Local.SixCellWindow machine) : Set where
  field
    occurrence :
      Local.WindowRewriteOccurrence machine before after window

    prefixPlain :
      PlainCells (Local.prefix occurrence)

    suffixPlain :
      PlainCells (Local.suffix occurrence)

open WellFormedRewriteOccurrence public

record WellFormedMachineStep
    (machine : Local.ConcreteTapeMachine)
    (before after : Local.TapeRow machine) : Set₁ where
  field
    step : Local.MachineStep machine before after

    wellFormedOccurrence :
      WellFormedRewriteOccurrence
        machine before after (Local.window step)

open WellFormedMachineStep public

beforeExactlyOneHead :
  ∀ {machine before after} →
  (wellFormed : WellFormedMachineStep machine before after) →
  ExactlyOneHead (Local.cells before)
beforeExactlyOneHead wellFormed
    with Local.ruleIsConfigured (step wellFormed)
... | Local.realizes-left =
  transportExactlyOneHead
    (sym (Local.beforeShape occurrenceWitness))
    (prependPlain prefixWitness
      (plainBefore
        (headHere (plainCons suffixWitness))))
  where
    occurrenceWitness =
      occurrence (wellFormedOccurrence wellFormed)
    prefixWitness =
      prefixPlain (wellFormedOccurrence wellFormed)
    suffixWitness =
      suffixPlain (wellFormedOccurrence wellFormed)
... | Local.realizes-stay =
  transportExactlyOneHead
    (sym (Local.beforeShape occurrenceWitness))
    (prependPlain prefixWitness
      (plainBefore
        (headHere (plainCons suffixWitness))))
  where
    occurrenceWitness =
      occurrence (wellFormedOccurrence wellFormed)
    prefixWitness =
      prefixPlain (wellFormedOccurrence wellFormed)
    suffixWitness =
      suffixPlain (wellFormedOccurrence wellFormed)
... | Local.realizes-right =
  transportExactlyOneHead
    (sym (Local.beforeShape occurrenceWitness))
    (prependPlain prefixWitness
      (plainBefore
        (headHere (plainCons suffixWitness))))
  where
    occurrenceWitness =
      occurrence (wellFormedOccurrence wellFormed)
    prefixWitness =
      prefixPlain (wellFormedOccurrence wellFormed)
    suffixWitness =
      suffixPlain (wellFormedOccurrence wellFormed)

afterExactlyOneHead :
  ∀ {machine before after} →
  (wellFormed : WellFormedMachineStep machine before after) →
  ExactlyOneHead (Local.cells after)
afterExactlyOneHead wellFormed
    with Local.ruleIsConfigured (step wellFormed)
... | Local.realizes-left =
  transportExactlyOneHead
    (sym (Local.afterShape occurrenceWitness))
    (prependPlain prefixWitness
      (headHere
        (plainCons (plainCons suffixWitness))))
  where
    occurrenceWitness =
      occurrence (wellFormedOccurrence wellFormed)
    prefixWitness =
      prefixPlain (wellFormedOccurrence wellFormed)
    suffixWitness =
      suffixPlain (wellFormedOccurrence wellFormed)
... | Local.realizes-stay =
  transportExactlyOneHead
    (sym (Local.afterShape occurrenceWitness))
    (prependPlain prefixWitness
      (plainBefore
        (headHere (plainCons suffixWitness))))
  where
    occurrenceWitness =
      occurrence (wellFormedOccurrence wellFormed)
    prefixWitness =
      prefixPlain (wellFormedOccurrence wellFormed)
    suffixWitness =
      suffixPlain (wellFormedOccurrence wellFormed)
... | Local.realizes-right =
  transportExactlyOneHead
    (sym (Local.afterShape occurrenceWitness))
    (prependPlain prefixWitness
      (plainBefore
        (plainBefore
          (headHere suffixWitness))))
  where
    occurrenceWitness =
      occurrence (wellFormedOccurrence wellFormed)
    prefixWitness =
      prefixPlain (wellFormedOccurrence wellFormed)
    suffixWitness =
      suffixPlain (wellFormedOccurrence wellFormed)

record ConcreteTapeWellFormedBoundary : Set where
  constructor concrete-tape-well-formed-boundary
  field
    plainPrefixSuffixPredicatePaid : Bool
    uniqueHeadConfigurationInvariantPaid : Bool
    wellFormedStepPreservesUniqueHeadPaid : Bool
    wellFormedAllWindowForwardPaid : Bool
    wellFormedAllWindowReversePaid : Bool
    canonicalSATTableauWeldPaid : Bool
    pVsNPResolved : Bool

canonicalConcreteTapeWellFormedBoundary :
  ConcreteTapeWellFormedBoundary
canonicalConcreteTapeWellFormedBoundary =
  concrete-tape-well-formed-boundary
    true true true false false false false
