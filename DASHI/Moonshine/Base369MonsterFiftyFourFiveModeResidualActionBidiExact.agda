module DASHI.Moonshine.Base369MonsterFiftyFourFiveModeResidualActionBidiExact where

------------------------------------------------------------------------
-- FIVE-MODE / DISTINGUISHED-SECTOR X-POLLINATION FOR THE 54 -> 1 + 53 CUT
--
-- The repository already owns two facts that must not be conflated:
--
--   * MonsterReducedNonaryBoundaryExact has the arithmetic
--       54 = 5 * 9 + 9
--       53 = 5 * 9 + 8;
--
--   * Base369FiveModePhaseQuotientExact has a genuinely typed five-mode
--     carrier D4IrreducibleType = {A1,A2,B1,B2,E} and a nine-state
--     ModePhaseQuotient9.
--
-- This owner cross-pollinates those shapes into a typed CANDIDATE skeleton:
-- five complete nonary sectors plus one distinguished nonary sector.  It does
-- not identify that skeleton with an actual Monster 54-dimensional module.
-- The promotion target below requires a two-sided recognition and, crucially,
-- requires the 53-action to be the literal restriction of the SAME actual
-- 54-action.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import DASHI.Foundations.Base369FiveModePhaseQuotientExact as Five
import DASHI.Moonshine.MonsterReducedNonaryBoundaryExact as Nonary
import DASHI.Biology.ReducedFiftyThreeFibreExact as Reduced

------------------------------------------------------------------------
-- 1. Factor 5 gets a typed candidate meaning, not Monster authority.
------------------------------------------------------------------------

FiveMode : Set
FiveMode = Five.D4IrreducibleType

NonaryState : Set
NonaryState = Five.ModePhaseQuotient9

data SecondarySector6 : Set where
  completeSector : FiveMode → SecondarySector6
  distinguishedSector : SecondarySector6

SecondaryCell54 : Set
SecondaryCell54 = SecondarySector6 × NonaryState

fiveCompleteSectorDimension : Nat
fiveCompleteSectorDimension = 5 * 9

distinguishedSectorDimension : Nat
distinguishedSectorDimension = 9

candidateFullDimension : Nat
candidateFullDimension = fiveCompleteSectorDimension + distinguishedSectorDimension

candidateFullDimensionIs54 : candidateFullDimension ≡ 54
candidateFullDimensionIs54 = Nonary.fiftyFourIsFiveTimesNinePlusNine

fiveCompleteSectorDimensionIs45 : fiveCompleteSectorDimension ≡ 45
fiveCompleteSectorDimensionIs45 = Nonary.fiveCompleteNonarySectorsIsFortyFive

------------------------------------------------------------------------
-- 2. Remove exactly the identity point of the distinguished nonary sector.
--    The other eight pointed-nonary quotient states remain explicit.
------------------------------------------------------------------------

data DistinguishedResidual8 : Set where
  residualA2negative residualA2positive
  residualB1negative residualB1positive
  residualB2negative residualB2positive
  residualEnegative residualEpositive
  : DistinguishedResidual8

residualNonaryState : DistinguishedResidual8 → NonaryState
residualNonaryState residualA2negative = Five.A2negative
residualNonaryState residualA2positive = Five.A2positive
residualNonaryState residualB1negative = Five.B1negative
residualNonaryState residualB1positive = Five.B1positive
residualNonaryState residualB2negative = Five.B2negative
residualNonaryState residualB2positive = Five.B2positive
residualNonaryState residualEnegative = Five.Enegative
residualNonaryState residualEpositive = Five.Epositive

ResidualCell53 : Set
ResidualCell53 = (FiveMode × NonaryState) ⊎ DistinguishedResidual8

includeResidual53 : ResidualCell53 → SecondaryCell54
includeResidual53 (inj₁ (mode , state)) = completeSector mode , state
includeResidual53 (inj₂ residual) = distinguishedSector , residualNonaryState residual

distinguishedInvariant54 : SecondaryCell54
distinguishedInvariant54 = distinguishedSector , Five.identityMode

data IsDistinguishedInvariant54 : SecondaryCell54 → Set where
  isDistinguishedInvariant :
    IsDistinguishedInvariant54 distinguishedInvariant54

residualImageIsNotInvariant :
  (state : ResidualCell53) →
  IsDistinguishedInvariant54 (includeResidual53 state) → ⊥
residualImageIsNotInvariant (inj₁ (mode , state)) ()
residualImageIsNotInvariant (inj₂ residualA2negative) ()
residualImageIsNotInvariant (inj₂ residualA2positive) ()
residualImageIsNotInvariant (inj₂ residualB1negative) ()
residualImageIsNotInvariant (inj₂ residualB1positive) ()
residualImageIsNotInvariant (inj₂ residualB2negative) ()
residualImageIsNotInvariant (inj₂ residualB2positive) ()
residualImageIsNotInvariant (inj₂ residualEnegative) ()
residualImageIsNotInvariant (inj₂ residualEpositive) ()

candidateResidualDimension : Nat
candidateResidualDimension = 5 * 9 + 8

candidateResidualDimensionIs53 : candidateResidualDimension ≡ 53
candidateResidualDimensionIs53 = Nonary.fiftyThreeIsFiveTimesNinePlusEight

candidateResidualAgreesWithCanonicalDimension :
  candidateResidualDimension ≡ Reduced.reducedDimension
candidateResidualAgreesWithCanonicalDimension =
  Nonary.localisedReductionAgreesWithExistingReducedDimension

------------------------------------------------------------------------
-- 3. Actual promotion contract.
--
-- A cardinal decomposition is insufficient.  A valid Monster-side promotion
-- must identify one actual 54-carrier with this skeleton, identify one actual
-- 53-carrier with the residual skeleton, and prove that the 53 action is the
-- restriction of the SAME 54 action through the actual inclusion.
------------------------------------------------------------------------

record ActualFiftyFourFiveModeResidualActionRecognition : Set₁ where
  constructor actual-fifty-four-five-mode-residual-action-recognition
  field
    Actor : Set
    Actual54 : Set
    Actual53 : Set

    act54 : Actor → Actual54 → Actual54
    act53 : Actor → Actual53 → Actual53

    toSkeleton54 : Actual54 → SecondaryCell54
    fromSkeleton54 : SecondaryCell54 → Actual54
    skeleton54AfterActual54 :
      (state : Actual54) → fromSkeleton54 (toSkeleton54 state) ≡ state
    actual54AfterSkeleton54 :
      (state : SecondaryCell54) → toSkeleton54 (fromSkeleton54 state) ≡ state

    toResidual53 : Actual53 → ResidualCell53
    fromResidual53 : ResidualCell53 → Actual53
    residual53AfterActual53 :
      (state : Actual53) → fromResidual53 (toResidual53 state) ≡ state
    actual53AfterResidual53 :
      (state : ResidualCell53) → toResidual53 (fromResidual53 state) ≡ state

    actualInvariant54 : Actual54
    actualInvariantMapsToDistinguished :
      toSkeleton54 actualInvariant54 ≡ distinguishedInvariant54
    actualInvariantFixed :
      (actor : Actor) → act54 actor actualInvariant54 ≡ actualInvariant54

    includeActual53 : Actual53 → Actual54
    inclusionMatchesSkeleton :
      (state : Actual53) →
      toSkeleton54 (includeActual53 state)
      ≡ includeResidual53 (toResidual53 state)

    sameActionRestrictsToResidual :
      (actor : Actor) →
      (state : Actual53) →
      includeActual53 (act53 actor state)
      ≡ act54 actor (includeActual53 state)

open ActualFiftyFourFiveModeResidualActionRecognition public

------------------------------------------------------------------------
-- 4. The recognition immediately gives the two required semantic facts:
--    the invariant point is fixed, and every residual action remains inside
--    the actual 53-carrier before inclusion back into the 54-carrier.
------------------------------------------------------------------------

actualInvariantIsFixed :
  (recognition : ActualFiftyFourFiveModeResidualActionRecognition) →
  (actor : Actor recognition) →
  act54 recognition actor (actualInvariant54 recognition)
  ≡ actualInvariant54 recognition
actualInvariantIsFixed recognition = actualInvariantFixed recognition

actualResidualActionAgreesAfterInclusion :
  (recognition : ActualFiftyFourFiveModeResidualActionRecognition) →
  (actor : Actor recognition) →
  (state : Actual53 recognition) →
  includeActual53 recognition (act53 recognition actor state)
  ≡ act54 recognition actor (includeActual53 recognition state)
actualResidualActionAgreesAfterInclusion recognition =
  sameActionRestrictsToResidual recognition

------------------------------------------------------------------------
-- 5. BIDI boundary.
------------------------------------------------------------------------

record FiftyFourFiveModeResidualBoundary : Set where
  constructor fifty-four-five-mode-residual-boundary
  field
    typedFiveModeCandidateCarrierExists : Bool
    fiveCompletePlusDistinguishedNonarySkeletonExists : Bool
    residualDeletesOnlyDistinguishedIdentityPoint : Bool
    residualDimensionIsCanonicalFiftyThree : Bool
    sameActualActionRestrictionRequiredForPromotion : Bool
    factorFiveIsAlreadyProvedActualMonsterFiveMode : Bool
    cardinalFiftyFourAloneCreatesActionRecognition : Bool
    actualFiftyFourResidualActionRecognitionInhabitedHere : Bool

canonicalFiftyFourFiveModeResidualBoundary :
  FiftyFourFiveModeResidualBoundary
canonicalFiftyFourFiveModeResidualBoundary =
  fifty-four-five-mode-residual-boundary
    true true true true true false false false
