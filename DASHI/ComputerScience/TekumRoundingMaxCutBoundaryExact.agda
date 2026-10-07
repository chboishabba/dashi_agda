module DASHI.ComputerScience.TekumRoundingMaxCutBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (suc)
open import Data.Vec using (Vec)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumPrecisionCompositionExact as Precision
import DASHI.ComputerScience.TekumProposition5FiniteNearestNoGoExact as FiniteNoGo
import DASHI.ComputerScience.TekumProposition5NoGoExact as EndpointNoGo
import DASHI.ComputerScience.TekumTruncationRoundingExact as Truncate

------------------------------------------------------------------------
-- ROUNDING MAX-CUT AFTER THE TWO PROPOSITION-5 FALSIFIERS
--
-- There are now two independent source-level obstructions:
--
--   1. endpoint closure: ordinary 10-trit inputs can raw-truncate to reserved
--      NaR/infinity lower-width strings;
--   2. finite nearestness: even when raw truncation lands on an ordinary
--      finite 8-trit value, a different finite 8-trit value can be strictly
--      closer in the exact rational semantics.
--
-- Hence there is no honest domain repair of the form
--
--     "restrict merely to inputs whose raw target is finite"
--
-- that recovers Hunhold Proposition 5.  The old planned proof route from
-- structural truncation composition through Proposition 5 to *numerical*
-- no-double-rounding is therefore blocked as well.  What survives exactly is
-- the structural word identity `truncateTwoTwiceEqualsFour`.
------------------------------------------------------------------------

prop5EndpointClosureImpossible :
  ¬ EndpointNoGo.RawTruncationFiniteClosed
prop5EndpointClosureImpossible =
  EndpointNoGo.unrestrictedRawTruncationFiniteClosureImpossible

prop5FiniteNearestRepairImpossible :
  ¬ FiniteNoGo.RawTruncationNearestOnFiniteClosure
prop5FiniteNearestRepairImpossible =
  FiniteNoGo.finiteClosureDoesNotRepairProposition5

structuralNoDoubleTruncation :
  ∀ {n}
  (xs : Vec Trit.Trit (suc (suc (suc (suc n))))) →
  Truncate.truncateTwo (Truncate.truncateTwo xs)
  ≡ Precision.truncateFourDirect xs
structuralNoDoubleTruncation = Precision.truncateTwoTwiceEqualsFour

record Prop5DerivedNumericalNoDoubleRoundingRoute : Set where
  constructor prop5DerivedNumericalNoDoubleRoundingRoute
  field
    finiteCounterexampleMustStillBeNearest :
      FiniteNoGo.NearestAgainst
        FiniteNoGo.sourceValue
        FiniteNoGo.targetValue
        FiniteNoGo.competitorValue

    structuralCompositionAvailable :
      ∀ {n}
      (xs : Vec Trit.Trit (suc (suc (suc (suc n))))) →
      Truncate.truncateTwo (Truncate.truncateTwo xs)
      ≡ Precision.truncateFourDirect xs
open Prop5DerivedNumericalNoDoubleRoundingRoute public

prop5DerivedNumericalNoDoubleRoundingRouteImpossible :
  ¬ Prop5DerivedNumericalNoDoubleRoundingRoute
prop5DerivedNumericalNoDoubleRoundingRouteImpossible route =
  FiniteNoGo.rawTargetNotNearestAgainstFiniteCompetitor
    (finiteCounterexampleMustStillBeNearest route)

record TekumRoundingMaxCutBoundary : Set where
  constructor tekumRoundingMaxCutBoundary
  field
    unrestrictedProp5EndpointClosureRefuted : Bool
    finiteClosureNearestRepairRefuted : Bool
    structuralTwoStageTruncationCompositionPaid : Bool
    prop5DerivedNumericalNoDoubleRoundingRouteBlocked : Bool
    sourceProp5NearestRoundingPaid : Bool
    numericalNoDoubleRoundingPaid : Bool

canonicalTekumRoundingMaxCutBoundary : TekumRoundingMaxCutBoundary
canonicalTekumRoundingMaxCutBoundary =
  tekumRoundingMaxCutBoundary
    true true true true false false
