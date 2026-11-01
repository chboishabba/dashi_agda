module DASHI.Computation.BMSSPPullPivotTemporalSameCarrierExact where

-- Same-carrier temporal weld for BMSSP.
-- The Pull full-state carrier is the literal carrier over which work and pivot
-- predicates are defined.  No separate RelevantVertex universe is introduced.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat using (_≤_)
open import Data.Sum using (_⊎_)

import DASHI.Computation.SSSPGeneralPullPrefixQuotientExact as Pull
import DASHI.Computation.PathfindingTemporalFibreEvolutionExact as Temporal

------------------------------------------------------------------------
-- 1. FindPivots obligations indexed directly by Pull.FullState F.
------------------------------------------------------------------------

record SameCarrierPivotLayer (F : Pull.PullPrefixFactorisation) : Set₁ where
  constructor sameCarrierPivotLayer
  field
    InCompletedWork : Pull.FullState F → Set
    VisitsCompletePivot : Pull.FullState F → Set
    coverage :
      (x : Pull.FullState F) →
      InCompletedWork x ⊎ VisitsCompletePivot x

    k workCount pivotCount : Nat
    pivotCompression : k * pivotCount ≤ workCount

open SameCarrierPivotLayer public

------------------------------------------------------------------------
-- 2. One temporal transition on the exact Pull carrier.
------------------------------------------------------------------------

record PullTemporalTransition (F : Pull.PullPrefixFactorisation) : Set₁ where
  constructor pullTemporalTransition
  field
    advance : Nat → Pull.FullState F → Pull.FullState F
    advancePrefix : Nat → Pull.Prefix F → Pull.Prefix F
    advanceTail : Nat → Pull.TailCode F → Pull.TailCode F

    prefixCommutes :
      (t : Nat) (x : Pull.FullState F) →
      Pull.encodePrefix F (advance t x) ≡
      advancePrefix t (Pull.encodePrefix F x)

    tailEvolution :
      (t : Nat) (x : Pull.FullState F) → Set

open PullTemporalTransition public

asTemporalPullFibre :
  (F : Pull.PullPrefixFactorisation) →
  PullTemporalTransition F →
  Temporal.TemporalPathfindingFibre
asTemporalPullFibre F T =
  Temporal.temporalPathfindingFibre
    Nat
    (λ t → Pull.FullState F)
    (λ t → Pull.Prefix F)
    (λ t → Pull.TailCode F)
    (λ t → Pull.encodePrefix F)
    (λ t → Pull.encodeTail F)
    suc
    (advance T)
    (advancePrefix T)
    (advanceTail T)
    (prefixCommutes T)

------------------------------------------------------------------------
-- 3. Time-indexed BMSSP layer: Pull, work, and pivots share one carrier.
------------------------------------------------------------------------

record BMSSPTemporalSameCarrier : Set₁ where
  constructor bmsspTemporalSameCarrier
  field
    pull : Pull.PullPrefixFactorisation
    tailSymmetry : Pull.TailSymmetryQuotient pull
    transition : PullTemporalTransition pull
    pivotLayer : Nat → SameCarrierPivotLayer pull

    recursiveState : Nat → Pull.FullState pull
    recursiveStateCommutes :
      (t : Nat) →
      recursiveState (suc t) ≡ advance transition t (recursiveState t)

open BMSSPTemporalSameCarrier public

currentPrefix :
  (B : BMSSPTemporalSameCarrier) →
  Nat → Pull.Prefix (pull B)
currentPrefix B t = Pull.encodePrefix (pull B) (recursiveState B t)

currentTail :
  (B : BMSSPTemporalSameCarrier) →
  Nat → Pull.TailCode (pull B)
currentTail B t = Pull.encodeTail (pull B) (recursiveState B t)

currentCoverage :
  (B : BMSSPTemporalSameCarrier) →
  (t : Nat) →
  let L = pivotLayer B t in
  (x : Pull.FullState (pull B)) →
  InCompletedWork L x ⊎ VisitsCompletePivot L x
currentCoverage B t = coverage (pivotLayer B t)

currentPivotCompression :
  (B : BMSSPTemporalSameCarrier) →
  (t : Nat) →
  let L = pivotLayer B t in
  k L * pivotCount L ≤ workCount L
currentPivotCompression B t = pivotCompression (pivotLayer B t)

------------------------------------------------------------------------
-- 4. Pull observation commutes with recursive time.
------------------------------------------------------------------------

pullCommutesWithRecursion :
  (B : BMSSPTemporalSameCarrier) →
  (t : Nat) →
  currentPrefix B (suc t) ≡
  advancePrefix (transition B) t (currentPrefix B t)
pullCommutesWithRecursion B t
  rewrite recursiveStateCommutes B t =
  prefixCommutes (transition B) t (recursiveState B t)

------------------------------------------------------------------------
-- 5. Tail symmetries remain consumer-invisible at each time slice.
------------------------------------------------------------------------

prefixInvariantUnderCurrentTailSymmetry :
  (B : BMSSPTemporalSameCarrier) →
  (t : Nat) →
  (g : Pull.Symmetry (tailSymmetry B)) →
  Pull.pullObservation (pull B)
    (Pull.actFull (tailSymmetry B) g (recursiveState B t))
  ≡ currentPrefix B t
prefixInvariantUnderCurrentTailSymmetry B t g =
  Pull.prefixPreservedByTailAction
    (tailSymmetry B) g (recursiveState B t)

------------------------------------------------------------------------
-- 6. Same-object and temporal boundaries.
------------------------------------------------------------------------

record BMSSPPullPivotTemporalBoundary : Set where
  constructor bmsspPullPivotTemporalBoundary
  field
    pullWorkPivotShareLiteralCarrier : Bool
    pullWorkPivotShareLiteralCarrierIsTrue :
      pullWorkPivotShareLiteralCarrier ≡ true

    recursiveTimeUsesSamePullFullState : Bool
    recursiveTimeUsesSamePullFullStateIsTrue :
      recursiveTimeUsesSamePullFullState ≡ true

    pivotLayerMayChangeWithTime : Bool
    pivotLayerMayChangeWithTimeIsTrue :
      pivotLayerMayChangeWithTime ≡ true

    residualTailNeedRemainEqualAcrossTime : Bool
    residualTailNeedRemainEqualAcrossTimeIsFalse :
      residualTailNeedRemainEqualAcrossTime ≡ false

    cardinalCompressionDefinesCarrierIdentity : Bool
    cardinalCompressionDefinesCarrierIdentityIsFalse :
      cardinalCompressionDefinesCarrierIdentity ≡ false

canonicalBMSSPPullPivotTemporalBoundary : BMSSPPullPivotTemporalBoundary
canonicalBMSSPPullPivotTemporalBoundary =
  bmsspPullPivotTemporalBoundary true refl true refl true refl false refl false refl
