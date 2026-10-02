module DASHI.Moonshine.OggP31CompletionTenTwoSevenNineCrossPollinationExact where

------------------------------------------------------------------------
-- COMPLETION10 -> REGULAR C3 THIRTY -> POINTED 31 -> NONARY 279
--
-- This owner records a repo-native arithmetic/observer chain assembled from
-- already-owned typed structures:
--
--   Completion10                         : 10 = 9 + 1 = 5 x 2
--   regular C3 expansion                 : 3 x 10 = 30
--   SSP15 p31 pointed-full-permutation   : 1 + 30 = 31
--   nonary scale                         : 9 x 31 = 279
--
-- The important firewall is equally explicit:
--
-- * 276 is the actual weight-two A-copy Tate multiplicity in the Lean
--   Carnahan--Urano 4A(2B) lane (and independently also occurs as an
--   off-diagonal coordinate count in the FLM weight-two chart);
-- * 276 is NOT added to this 10 -> 30 -> 31 -> 279 chain;
-- * this file does not construct a same-object map from the 276-dimensional
--   2B Tate module to the p31 observer.
--
-- Thus 279 is promoted here as a typed composite observer scalar
--   nonary( pointed( regular-C3(Completion10) ) ),
-- not as a dimension of the 2B Tate module.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Completion
import DASHI.Biology.SSP15NineObserverAtlasExact as Atlas
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.MonsterReducedNonaryBoundaryExact as Nonary
import DASHI.Moonshine.OggSSP15CanonicalRankThreeByFiveExact as Rank
import DASHI.Moonshine.MoonshineOrbifoldWeightTwoDecompositionExact as Orbifold

------------------------------------------------------------------------
-- 1. Completion10 is the typed ten-state source.
------------------------------------------------------------------------

completionTen : Nat
completionTen = Completion.listCount Completion.canonicalDecimalCompletionStates

completionTenIsTen : completionTen ≡ 10
completionTenIsTen = Completion.decimalCompletionStateCountIsTen

completionTenIsFiveTimesTwo :
  completionTen ≡
    Completion.listCount Completion.canonicalComplementModes
      * Completion.listCount Completion.canonicalBinaryPhases
completionTenIsFiveTimesTwo = refl

------------------------------------------------------------------------
-- 2. Regular C3 expansion of the ten carrier gives thirty.
--
-- This is a product cardinality/regular-phase expansion.  It does not say the
-- actual 2B A-copy multiplicity is a C3 module.
------------------------------------------------------------------------

regularC3PhaseCount : Nat
regularC3PhaseCount = 3

regularizedCompletionCount : Nat
regularizedCompletionCount = regularC3PhaseCount * completionTen

regularizedCompletionCountIsThirty :
  regularizedCompletionCount ≡ 30
regularizedCompletionCountIsThirty = refl

------------------------------------------------------------------------
-- 3. The existing p31 observer is literally the pointed completion 1 + 30.
------------------------------------------------------------------------

p31Value : Nat
p31Value = Lane.monsterPrimeLaneToNat Lane.p31

p31ValueIsThirtyOne : p31Value ≡ 31
p31ValueIsThirtyOne = refl

pointedThirtyIsP31 :
  1 + regularizedCompletionCount ≡ p31Value
pointedThirtyIsP31 = refl

pointedThirtyAgreesWithExistingAtlas :
  1 + regularizedCompletionCount ≡ 31
pointedThirtyAgreesWithExistingAtlas =
  Atlas.pointedFullPermutationArithmetic

p31AtlasValueIsLane :
  Atlas.observedValue (Atlas.ssp15NineAtlas Lane.p31)
  ≡ p31Value
p31AtlasValueIsLane =
  Atlas.observedValueIsPrimeLane (Atlas.ssp15NineAtlas Lane.p31)

p31IsCanonicalRankTen :
  Rank.primeToRank Lane.p31 ≡ Rank.r10
p31IsCanonicalRankTen = refl

------------------------------------------------------------------------
-- 4. Nonary multiplication yields literal 279.
------------------------------------------------------------------------

nonaryScale : Nat
nonaryScale = Nonary.jCoarse

nonaryScaleIsNine : nonaryScale ≡ 9
nonaryScaleIsNine = Nonary.jCoarseIsNine

nonaryPointedP31 : Nat
nonaryPointedP31 = nonaryScale * p31Value

nonaryPointedP31Is279 : nonaryPointedP31 ≡ 279
nonaryPointedP31Is279 = refl

completionTenTo279Composite :
  9 * (1 + 3 * 10) ≡ 279
completionTenTo279Composite = refl

completionTenTo279TypedComposite :
  nonaryScale * (1 + regularC3PhaseCount * completionTen) ≡ 279
completionTenTo279TypedComposite = refl

------------------------------------------------------------------------
-- 5. A useful inverse arithmetic reading.
------------------------------------------------------------------------

twoSevenNineOverNonaryIsP31 :
  279 ≡ 9 * 31
twoSevenNineOverNonaryIsP31 = refl

p31UnpointsToRegularizedTen :
  31 ≡ 1 + 3 * 10
p31UnpointsToRegularizedTen = refl

------------------------------------------------------------------------
-- 6. 276 firewall.
--
-- Agda already owns an independent weight-two coordinate count 276 in the
-- FLM chart.  The Lean 2B lane owns another 276: the source-derived A-copy
-- Tate multiplicity.  Equal numerals do not identify those roles, and neither
-- 276 participates arithmetically in the 10 -> 30 -> 31 -> 279 composite.
------------------------------------------------------------------------

independentOrbifoldCoordinate276 : Nat
independentOrbifoldCoordinate276 = Orbifold.offDiagonalCoordinateCount

independentOrbifoldCoordinate276Is276 :
  independentOrbifoldCoordinate276 ≡ 276
independentOrbifoldCoordinate276Is276 = refl

data TwoBTate276IsOrbifoldCoordinate276 : Set where

twoDistinct276RolesNotIdentifiedHere :
  TwoBTate276IsOrbifoldCoordinate276 → ⊥
twoDistinct276RolesNotIdentifiedHere ()

data P31ObserverConstructsTwoBTateSubquotient : Set where

p31ObserverDoesNotConstructTwoBTateSubquotient :
  P31ObserverConstructsTwoBTateSubquotient → ⊥
p31ObserverDoesNotConstructTwoBTateSubquotient ()

------------------------------------------------------------------------
-- 7. Typed frontier.
------------------------------------------------------------------------

record CompletionTenP31TwoSevenNineBoundary : Set where
  constructor completion-ten-p31-two-seven-nine-boundary
  field
    completionTenTyped : Bool
    fiveTimesTwoTyped : Bool
    regularC3TimesTenIsThirty : Bool
    pointedThirtyIsP31 : Bool
    p31IsActualOggLane : Bool
    p31IsCanonicalSSP15RankTen : Bool
    nonaryTimesP31Is279 : Bool
    twoSevenNineUses276AsAddend : Bool
    equal276NumeralsIdentifySourceRoles : Bool
    p31ObserverAlreadySelectsActual2BTateQ : Bool

canonicalCompletionTenP31TwoSevenNineBoundary :
  CompletionTenP31TwoSevenNineBoundary
canonicalCompletionTenP31TwoSevenNineBoundary =
  completion-ten-p31-two-seven-nine-boundary
    true true true true true true true false false false
