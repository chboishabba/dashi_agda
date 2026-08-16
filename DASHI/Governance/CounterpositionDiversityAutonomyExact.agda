module DASHI.Governance.CounterpositionDiversityAutonomyExact where

------------------------------------------------------------------------
-- SOURCE / CROSS-POLLINATION CALIBRATION
--
-- Author: Chris Hanks.
-- Title: "Indoctrination and the space of reasons".
-- Venue: Educational Theory 58(2):193--212 (2008).
-- DOI: 10.1111/j.1741-5446.2008.00284.x.
--
-- Hanks supplies philosophical motivation for distinguishing initiation into a
-- space of reasons from autonomy-destroying closure.  The exact finite
-- counterposition algebra below is inherited from DASHI's older balanced-
-- ternary foundation and is not claimed as a theorem of Hanks.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT
import DASHI.Foundations.CounterpositionOrderedJoinExact as Counter
import DASHI.Governance.AutonomyReopeningCriterion as Reopening
import DASHI.Governance.DevelopmentalInfluenceSourceAtlas as Sources

record NonBinaryCounterpositionWitness : Set where
  constructor nonBinaryCounterpositionWitness
  field
    input : BT.TriadPattern
    alternative : BT.TriadPattern
    fullInverse : BT.TriadPattern
    alternativeExact :
      Counter.counterUnder Counter.rejectThird input ≡ alternative
    inverseExact :
      Counter.counterUnder Counter.invertAll input ≡ fullInverse
    alternativeNotInput : alternative ≡ input → ⊥
    alternativeNotInverse : alternative ≡ fullInverse → ⊥

open NonBinaryCounterpositionWitness public

canonicalNonBinaryCounterpositionWitness : NonBinaryCounterpositionWitness
canonicalNonBinaryCounterpositionWitness =
  nonBinaryCounterpositionWitness
    BT.allPositive
    BT.thirdCoordinateCounterposition
    BT.allNegative
    refl refl (λ ()) (λ ())

rejectFirstPositive : BT.TriadPattern
rejectFirstPositive = Counter.counterUnder Counter.rejectFirst BT.allPositive

rejectSecondPositive : BT.TriadPattern
rejectSecondPositive = Counter.counterUnder Counter.rejectSecond BT.allPositive

rejectThirdPositive : BT.TriadPattern
rejectThirdPositive = Counter.counterUnder Counter.rejectThird BT.allPositive

rejectFirstNotRejectSecond : rejectFirstPositive ≡ rejectSecondPositive → ⊥
rejectFirstNotRejectSecond ()

rejectFirstNotRejectThird : rejectFirstPositive ≡ rejectThirdPositive → ⊥
rejectFirstNotRejectThird ()

rejectSecondNotRejectThird : rejectSecondPositive ≡ rejectThirdPositive → ⊥
rejectSecondNotRejectThird ()

rejectThirdNotFullInverse :
  rejectThirdPositive
  ≡ Counter.counterUnder Counter.invertAll BT.allPositive
  → ⊥
rejectThirdNotFullInverse = Counter.partialCounterpositionIsNotFullInverse

record CounterpositionAccessSystem : Set₁ where
  constructor counterpositionAccessSystem
  field
    Claim : Set
    Context : Set
    inverse : Claim → Claim
    counter : Context → Claim → Claim

open CounterpositionAccessSystem public

record NonBinaryAlternativeAccess
  (S : CounterpositionAccessSystem) : Set₁ where
  constructor nonBinaryAlternativeAccess
  field
    accessClaim : Claim S
    accessContext : Context S
    accessAlternative : Claim S
    accessExact : counter S accessContext accessClaim ≡ accessAlternative
    accessNotClaim : accessAlternative ≡ accessClaim → ⊥
    accessNotInverse : accessAlternative ≡ inverse S accessClaim → ⊥

open NonBinaryAlternativeAccess public

record EpistemicOpennessWitness : Set₁ where
  constructor epistemicOpennessWitness
  field
    revisionWitness : Reopening.ReflexiveRevisionWitness
    counterpositionSystem : CounterpositionAccessSystem
    nonBinaryAlternative : NonBinaryAlternativeAccess counterpositionSystem

foundationCounterpositionSystem : CounterpositionAccessSystem
foundationCounterpositionSystem =
  counterpositionAccessSystem
    BT.TriadPattern Counter.CounterContext BT.strictInverse Counter.counterUnder

foundationNonBinaryAccess :
  NonBinaryAlternativeAccess foundationCounterpositionSystem
foundationNonBinaryAccess =
  nonBinaryAlternativeAccess
    BT.allPositive Counter.rejectThird BT.thirdCoordinateCounterposition
    refl (λ ()) (λ ())

record CounterpositionDiversityBoundary : Set where
  constructor counterpositionDiversityBoundary
  field
    oppositionMustEqualGlobalInverse : Bool
    epistemicOpennessIsRevisionOnly : Bool
    forcedBinaryChoiceExhaustsCounterpositionSpace : Bool
    nonBinaryAlternativesCanBeRepresented : Bool
    counterpositionDiversityAloneProvesAutonomy : Bool
    revisionAndAlternativeAccessAreSeparateCoordinates : Bool

canonicalCounterpositionDiversityBoundary : CounterpositionDiversityBoundary
canonicalCounterpositionDiversityBoundary =
  counterpositionDiversityBoundary false false false true false true

record CounterpositionDiversityReceipt : Set where
  constructor counterpositionDiversityReceipt
  field
    sources : List Sources.ScholarlySource
    boundary : CounterpositionDiversityBoundary

canonicalCounterpositionDiversityReceipt : CounterpositionDiversityReceipt
canonicalCounterpositionDiversityReceipt =
  counterpositionDiversityReceipt
    (Sources.indoctrinationSpaceReasons ∷ Sources.epistemicTrustReview ∷ [])
    canonicalCounterpositionDiversityBoundary
