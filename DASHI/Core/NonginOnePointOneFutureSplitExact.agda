module DASHI.Core.NonginOnePointOneFutureSplitExact where

------------------------------------------------------------------------
-- NONGIN 1.0 -> 1.1 CONCRETE FUTURE SPLIT
--
-- The raw nongin genealogy treats 1.1 as one additional frame/removal level.
-- NonginOnePointOneArmyRefinementExact already proves current consumer
-- non-descent through the 1.0 projection.
--
-- Here the dynamic state retains the hidden frame while carrying an explicit
-- visibility stance.  The single admissible action "surface frame" preserves
-- the underlying base/frame pair and changes only whether the frame-sensitive
-- response is exposed.
--
-- Two states with the same 1.0 observation therefore execute the same action
-- and become observably distinct.  This is a semantic/metacognitive fixture,
-- not an empirical claim of universal cognitive advantage or therapeutic law.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Core.NonginOnePointOneArmyRefinementExact as Nongin
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.FutureObservationalRefinement as Future
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.FutureSafeCoarseFibreCapacityExact as Capacity
import DASHI.Core.GeneralResidualFibreCardinalityExact as Cardinality

------------------------------------------------------------------------
-- 1. Dynamic carrier: hidden frame plus observation stance.
------------------------------------------------------------------------

data FrameVisibility : Set where
  onePointZeroHidden : FrameVisibility
  onePointOneSurfaced : FrameVisibility

NonginDynamicState : Set
NonginDynamicState =
  FrameVisibility × Nongin.OnePointOneCarrier Nongin.Base1 Nongin.Frame2

data NonginAction : Set where
  surfaceFrame : NonginAction

data NonginObservation : Set where
  commonOnePointZeroView : NonginObservation
  immersedFrameView : NonginObservation
  observingFrameView : NonginObservation

observeNongin : NonginDynamicState -> NonginObservation
observeNongin (onePointZeroHidden , state) =
  commonOnePointZeroView
observeNongin
  (onePointOneSurfaced , Nongin.sharedSituation , Nongin.immersed) =
  immersedFrameView
observeNongin
  (onePointOneSurfaced , Nongin.sharedSituation , Nongin.frameAware) =
  observingFrameView

Precondition : NonginDynamicState -> NonginAction -> Set
Precondition (onePointZeroHidden , state) surfaceFrame = ⊤
Precondition (onePointOneSurfaced , state) surfaceFrame = ⊥

data Postcondition :
    NonginDynamicState -> NonginAction -> NonginDynamicState -> Set where
  surfaceImmersed :
    Postcondition
      (onePointZeroHidden , Nongin.sharedSituation , Nongin.immersed)
      surfaceFrame
      (onePointOneSurfaced , Nongin.sharedSituation , Nongin.immersed)

  surfaceAware :
    Postcondition
      (onePointZeroHidden , Nongin.sharedSituation , Nongin.frameAware)
      surfaceFrame
      (onePointOneSurfaced , Nongin.sharedSituation , Nongin.frameAware)

nonginFrameActionSystem :
  Dependency.DependentActionSystem NonginDynamicState NonginAction
nonginFrameActionSystem =
  record
    { Precondition = Precondition
    ; Postcondition = Postcondition
    ; actionLabel = λ { surfaceFrame -> "surface retained frame coordinate" }
    }

immersedBefore : NonginDynamicState
immersedBefore =
  onePointZeroHidden , Nongin.sharedSituation , Nongin.immersed

awareBefore : NonginDynamicState
awareBefore =
  onePointZeroHidden , Nongin.sharedSituation , Nongin.frameAware

immersedAfter : NonginDynamicState
immersedAfter =
  onePointOneSurfaced , Nongin.sharedSituation , Nongin.immersed

awareAfter : NonginDynamicState
awareAfter =
  onePointOneSurfaced , Nongin.sharedSituation , Nongin.frameAware

sameOnePointZeroObservation :
  observeNongin immersedBefore ≡ observeNongin awareBefore
sameOnePointZeroObservation = refl

immersedSurfaceAction :
  Dependency.AdmissibleAction
    nonginFrameActionSystem
    immersedBefore
    surfaceFrame
immersedSurfaceAction =
  record
    { precondition = tt
    ; after = immersedAfter
    ; postcondition = surfaceImmersed
    ; dependencyReceipt =
        "retain the same base/frame state; expose the frame coordinate to the declared observer"
    }

awareSurfaceAction :
  Dependency.AdmissibleAction
    nonginFrameActionSystem
    awareBefore
    surfaceFrame
awareSurfaceAction =
  record
    { precondition = tt
    ; after = awareAfter
    ; postcondition = surfaceAware
    ; dependencyReceipt =
        "retain the same base/frame state; expose the frame coordinate to the declared observer"
    }

immersedSurfaceExecution :
  Reachability.Executes
    nonginFrameActionSystem
    (surfaceFrame ∷ [])
    immersedBefore
    immersedAfter
immersedSurfaceExecution =
  Reachability.executesCons immersedSurfaceAction Reachability.executesNil

awareSurfaceExecution :
  Reachability.Executes
    nonginFrameActionSystem
    (surfaceFrame ∷ [])
    awareBefore
    awareAfter
awareSurfaceExecution =
  Reachability.executesCons awareSurfaceAction Reachability.executesNil

surfacedObservationsDiffer :
  observeNongin immersedAfter ≡ observeNongin awareAfter -> ⊥
surfacedObservationsDiffer ()

------------------------------------------------------------------------
-- 2. Exact dynamic defect and FutureEquivalent refutation.
------------------------------------------------------------------------

nonginTerminalisationDefect :
  Dynamic.TerminalisationDefect
    nonginFrameActionSystem
    observeNongin
nonginTerminalisationDefect =
  Dynamic.terminalisationDefect
    (surfaceFrame ∷ [])
    immersedBefore
    awareBefore
    immersedAfter
    awareAfter
    sameOnePointZeroObservation
    immersedSurfaceExecution
    awareSurfaceExecution
    surfacedObservationsDiffer

onePointZeroObserverNotDynamicallySafe :
  Dynamic.DynamicConsumerSafety
    nonginFrameActionSystem
    observeNongin ->
  ⊥
onePointZeroObserverNotDynamicallySafe safety =
  Dynamic.terminalisationDefectContradictsSafety
    safety
    nonginTerminalisationDefect

immersedAndAwareNotFutureEquivalent :
  Future.FutureEquivalent
    nonginFrameActionSystem
    observeNongin
    immersedBefore
    awareBefore ->
  ⊥
immersedAndAwareNotFutureEquivalent future =
  surfacedObservationsDiffer
    (future immersedSurfaceExecution awareSurfaceExecution)

awareAndImmersedNotFutureEquivalent :
  Future.FutureEquivalent
    nonginFrameActionSystem
    observeNongin
    awareBefore
    immersedBefore ->
  ⊥
awareAndImmersedNotFutureEquivalent future =
  surfacedObservationsDiffer
    (sym (future awareSurfaceExecution immersedSurfaceExecution))

------------------------------------------------------------------------
-- 3. Two-class future fibre and capacity consequence.
------------------------------------------------------------------------

twoFrameRepresentative : Fin 2 -> NonginDynamicState
twoFrameRepresentative zero = immersedBefore
twoFrameRepresentative (suc zero) = awareBefore

twoFrameFutureEquivalentIndicesEqual :
  {left right : Fin 2} ->
  Future.FutureEquivalent
    nonginFrameActionSystem
    observeNongin
    (twoFrameRepresentative left)
    (twoFrameRepresentative right) ->
  left ≡ right
twoFrameFutureEquivalentIndicesEqual {zero} {zero} future = refl
twoFrameFutureEquivalentIndicesEqual {zero} {suc zero} future =
  ⊥-elim (immersedAndAwareNotFutureEquivalent future)
twoFrameFutureEquivalentIndicesEqual {suc zero} {zero} future =
  ⊥-elim (awareAndImmersedNotFutureEquivalent future)
twoFrameFutureEquivalentIndicesEqual {suc zero} {suc zero} future = refl

canonicalTwoFrameFutureDistinctFibre :
  Capacity.CanonicalFiniteFutureDistinctFibre
    2
    nonginFrameActionSystem
    observeNongin
canonicalTwoFrameFutureDistinctFibre =
  Cardinality.finiteFutureDistinctFibre
    twoFrameRepresentative
    commonOnePointZeroView
    (λ { zero -> refl ; (suc zero) -> refl })
    twoFrameFutureEquivalentIndicesEqual

twoFrameClassesForceResidualInjection :
  {Residual : Set} ->
  {residual : NonginDynamicState -> Residual} ->
  Capacity.FutureSafeResidual
    nonginFrameActionSystem
    observeNongin
    residual ->
  Cardinality.Injective
    (λ index -> residual (twoFrameRepresentative index))
twoFrameClassesForceResidualInjection safe =
  Capacity.futureSafeResidualInjectsCanonicalFutureClasses
    safe
    canonicalTwoFrameFutureDistinctFibre

twoFrameClassesForceBitCapacity :
  {bits : Nat} ->
  {residual : NonginDynamicState -> Cardinality.BitWords bits} ->
  Capacity.FutureSafeResidual
    nonginFrameActionSystem
    observeNongin
    residual ->
  2 ≤ Cardinality.pow2 bits
twoFrameClassesForceBitCapacity safe =
  Capacity.futureSafeBitResidualCapacityBound
    safe
    canonicalTwoFrameFutureDistinctFibre

------------------------------------------------------------------------
-- 4. Promotion boundary.
------------------------------------------------------------------------

record NonginOnePointOneFutureSplitBoundary : Set where
  constructor nongin-one-point-one-future-split-boundary
  field
    proofBearingFrameActionConstructed : Bool
    onePointZeroCollisionConstructed : Bool
    commonSurfaceActionConstructed : Bool
    surfacedFrameSplitConstructed : Bool
    futureEquivalenceRefuted : Bool
    twoClassCapacityBoundInstantiated : Bool
    literalTenPercentPerformanceLaw : Bool
    literalTenPercentPerformanceLawIsFalse :
      literalTenPercentPerformanceLaw ≡ false
    universalCognitiveSuperiorityClaimed : Bool
    universalCognitiveSuperiorityClaimedIsFalse :
      universalCognitiveSuperiorityClaimed ≡ false

canonicalNonginOnePointOneFutureSplitBoundary :
  NonginOnePointOneFutureSplitBoundary
canonicalNonginOnePointOneFutureSplitBoundary =
  nongin-one-point-one-future-split-boundary
    true true true true true true
    false refl
    false refl
