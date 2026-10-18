module DASHI.Mathematics.Complexity.ConcreteTapeStandardInfrastructureFreezeExact where

------------------------------------------------------------------------
-- FINITE-PRESENTATION MACHINE INFRASTRUCTURE FREEZE
--
-- This owner deliberately adds no new machine semantics.  It exposes the
-- already-proved exact guarded-input acceptance equivalence at the root of the
-- ordinary finite-presentation substrate.  Both implications use the same
-- literal input row, the same first-match rule table, and the same exact T.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_)

import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented

/-- Root infrastructure theorem.  For every literal finite presentation,
concrete guarded acceptance in exactly T steps and standard guarded acceptance
in exactly T steps are mutually reducible without any clock change. -/
finitePresentationExactAcceptanceEquivalence :
  ∀ (presentation : Presented.FinitePresentedStandardTM)
    (input : Input.InputWord
      (Presented.finitePresentedStandardToConcrete presentation))
    (steps : Nat) →
  (Language.GuardedConcreteAcceptsIn
      (Presented.finitePresentedStandardToConcrete presentation)
      input steps →
    Language.GuardedStandardAcceptsIn
      (Presented.finitePresentedStandardToConcrete presentation)
      input steps)
  ×
  (Language.GuardedStandardAcceptsIn
      (Presented.finitePresentedStandardToConcrete presentation)
      input steps →
    Language.GuardedConcreteAcceptsIn
      (Presented.finitePresentedStandardToConcrete presentation)
      input steps)
finitePresentationExactAcceptanceEquivalence =
  Language.finitePresentedGuardedAcceptanceIff

------------------------------------------------------------------------
-- MAX-CUT FREEZE
--
-- Once this owner and its dependencies are kernel-certified, the ordinary
-- representation substrate is frozen:
--
-- * concrete tape rows/windows and proof-producing steps;
-- * first-match finite rule dispatch;
-- * conventional finite single-tape presentation;
-- * exact forward and reverse T-step run transport;
-- * exact guarded-input acceptance equivalence;
-- * existing Cook--Levin operational/clock accounting downstream.
--
-- No additional interpreter, quotient, alternate tape representation, or
-- simulation clock is needed for the P lane.  The next substantive theorem
-- target is the repository's existing universal SAT decision-failure/lower-
-- bound producer, i.e. algorithm-independent lower-bound mathematics.
------------------------------------------------------------------------
