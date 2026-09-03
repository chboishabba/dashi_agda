module DASHI.Foundations.Base369SharedNonaryIdentityTransportExact where

open import DASHI.Core.Prelude

import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Moonshine.MonsterReducedNonaryBoundaryExact as Monster
import DASHI.Foundations.Base369Completion54SituatedTriadBridgeExact as Completion

------------------------------------------------------------------------
-- SHARED NONARY IDENTITY TRANSPORT
--
-- The same theorem-owned coarse nonary identity j = 9 is used in two distinct
-- constructions already present in the repository:
--
--   local boundary :  j |-> 6 j = 54
--   global pointing:  j |-> (j + 1) * Fine(j) = 196830,
--
-- where the canonical fine carrier at j = 9 has size 19683 = 27 * 729.
--
-- This owner does not identify those constructions.  It proves that their
-- arithmetic is coordinated by the same nonary parameter and exposes stronger
-- common-factor / Base369 factorizations.
------------------------------------------------------------------------

sharedJ : Nat
sharedJ = Monster.jCoarse

sharedJIsNine : sharedJ ≡ 9
sharedJIsNine = refl

------------------------------------------------------------------------
-- 1. Local use of j: six situated channels over one nonary sheet.
------------------------------------------------------------------------

localBoundaryViaJ : Nat
localBoundaryViaJ = 6 * sharedJ

localBoundaryViaJIs54 : localBoundaryViaJ ≡ 54
localBoundaryViaJIs54 = refl

localBoundaryAgreesWithMonsterSixByNine :
  localBoundaryViaJ ≡ Monster.fullSixByNine
localBoundaryAgreesWithMonsterSixByNine = refl

localBoundaryAgreesWithSituatedCompletion :
  localBoundaryViaJ ≡ Completion.localCompletionCount
localBoundaryAgreesWithSituatedCompletion = refl

------------------------------------------------------------------------
-- 2. Fine carrier: the same nonary depth resolves into the existing 19683
-- Base369 fine fibre.  We record both the 27 x 729 and the explicit nonary
-- factorization 9 x 2187.
------------------------------------------------------------------------

fineAtSharedJ : Nat
fineAtSharedJ = Harmonic.fineFrequencyDimension

fineAtSharedJIs19683 : fineAtSharedJ ≡ 19683
fineAtSharedJIs19683 = refl

fineAtSharedJIs27Times729 : 27 * 729 ≡ fineAtSharedJ
fineAtSharedJIs27Times729 = refl

fineAtSharedJHasNonaryFactor : sharedJ * 2187 ≡ fineAtSharedJ
fineAtSharedJHasNonaryFactor = refl

------------------------------------------------------------------------
-- 3. Global pointed use of the same j.
------------------------------------------------------------------------

globalPointedViaJ : Nat
globalPointedViaJ = (sharedJ + 1) * fineAtSharedJ

globalPointedViaJIs196830 : globalPointedViaJ ≡ 196830
globalPointedViaJIs196830 = refl

globalPointedAgreesWithHarmonic :
  globalPointedViaJ ≡ Harmonic.elementaryHarmonicDimension
globalPointedAgreesWithHarmonic = refl

globalPointedAgreesWithMonster :
  globalPointedViaJ ≡ Monster.monsterBulk
globalPointedAgreesWithMonster = refl

------------------------------------------------------------------------
-- 4. Strong common-factor identity.
--
-- Because 54 = 2 * 27 and 19683 = 27 * 729,
--
--   196830 = 10 * 27 * 729
--          = 5 * 54 * 729.
--
-- Thus the full pointed bulk is exactly five 54-blocks, each carrying a
-- 729-state situated-appraisal fibre.  This is finite cardinal arithmetic;
-- it does not by itself identify a Monster subrepresentation.
------------------------------------------------------------------------

fiftyFourIsTwoTimesTwentySeven : 2 * 27 ≡ 54
fiftyFourIsTwoTimesTwentySeven = refl

monsterBulkIsTenTimesTwentySevenTimes729 :
  10 * 27 * 729 ≡ globalPointedViaJ
monsterBulkIsTenTimesTwentySevenTimes729 = refl

monsterBulkIsFiveTimes54Times729 :
  5 * 54 * 729 ≡ globalPointedViaJ
monsterBulkIsFiveTimes54Times729 = refl

fiveTimes729 : Nat
fiveTimes729 = 5 * 729

fiveTimes729Is3645 : fiveTimes729 ≡ 3645
fiveTimes729Is3645 = refl

fiftyFourTimes3645IsMonsterBulk :
  54 * fiveTimes729 ≡ globalPointedViaJ
fiftyFourTimes3645IsMonsterBulk = refl

------------------------------------------------------------------------
-- 5. The shared 9 can also be factored literally from both cardinalities.
------------------------------------------------------------------------

localAsNineTimesSix : sharedJ * 6 ≡ localBoundaryViaJ
localAsNineTimesSix = refl

globalAsNineTimes21870 : sharedJ * 21870 ≡ globalPointedViaJ
globalAsNineTimes21870 = refl

------------------------------------------------------------------------
-- 6. Same-identity receipt: j is passed to two different resolution operators.
------------------------------------------------------------------------

data ResolutionKind : Set where
  localSituatedBoundary
  globalPointedFineBulk
  : ResolutionKind

resolveJ : ResolutionKind → Nat
resolveJ localSituatedBoundary = 6 * sharedJ
resolveJ globalPointedFineBulk = (sharedJ + 1) * fineAtSharedJ

record SharedNonaryIdentityReceipt : Set where
  constructor shared-nonary-identity-receipt
  field
    identity : Nat
    identityIsNine : identity ≡ 9
    localResolution : resolveJ localSituatedBoundary ≡ 54
    globalResolution : resolveJ globalPointedFineBulk ≡ 196830
    localUsesSameIdentity : identity ≡ sharedJ
    globalUsesSameIdentity : identity ≡ sharedJ

canonicalSharedNonaryIdentityReceipt : SharedNonaryIdentityReceipt
canonicalSharedNonaryIdentityReceipt =
  shared-nonary-identity-receipt 9 refl refl refl refl refl

------------------------------------------------------------------------
-- 7. Boundaries.
------------------------------------------------------------------------

data Local54EqualsGlobal196830 : Set where
data SharedNineMeansSameSemanticObject : Set where
data Five54BlocksConstructMonsterRepresentation : Set where
data Fine19683IsJustNineStates : Set where
data LinearAndPointedResolutionAreSameMap : Set where

local54DoesNotEqualGlobal196830 : Local54EqualsGlobal196830 → ⊥
local54DoesNotEqualGlobal196830 ()

sharedNineDoesNotForceSemanticIdentity : SharedNineMeansSameSemanticObject → ⊥
sharedNineDoesNotForceSemanticIdentity ()

five54BlocksDoNotConstructMonsterRepresentation :
  Five54BlocksConstructMonsterRepresentation → ⊥
five54BlocksDoNotConstructMonsterRepresentation ()

fine19683IsNotJustNineStates : Fine19683IsJustNineStates → ⊥
fine19683IsNotJustNineStates ()

linearAndPointedResolutionAreNotSameMap :
  LinearAndPointedResolutionAreSameMap → ⊥
linearAndPointedResolutionAreNotSameMap ()

record Base369SharedNonaryIdentityBoundary : Set where
  constructor base369-shared-nonary-identity-boundary
  field
    sameJEqualsNineUsedLocally : Bool
    sameJEqualsNineUsedGlobally : Bool
    localResolutionIs54 : Bool
    globalResolutionIs196830 : Bool
    fiftyFourIsTwoBase27Cells : Bool
    fineFibreIs27Times729 : Bool
    monsterBulkIsFive54Times729 : Bool
    bothCardinalitiesHaveLiteralNineFactor : Bool
    localAndGlobalResolutionAreIdenticalMaps : Bool
    factorizationConstructsMonsterRepresentation : Bool

canonicalBase369SharedNonaryIdentityBoundary :
  Base369SharedNonaryIdentityBoundary
canonicalBase369SharedNonaryIdentityBoundary =
  base369-shared-nonary-identity-boundary
    true true true true true true true true false false
