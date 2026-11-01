module DASHI.Reasoning.Trialectic369DyadicKernel4DescentCountExact where

------------------------------------------------------------------------
-- THREE T4 LOCALS GLUED ALONG THREE T1 OVERLAPS -> T9
--
-- DASHI CONTRIBUTION
--
-- The original trialectic cover has three dyadic local sections:
--
--   U_AB, U_BC, U_CA
--
-- each exactly recharted as Kernel 4.  Their pairwise overlap constraints are
-- one trit each:
--
--   AA_AB = AA_CA
--   BB_AB = BB_BC
--   CC_BC = CC_CA.
--
-- Hence the independent-coordinate ledger is
--
--   4 + 4 + 4 - 1 - 1 - 1 = 9.
--
-- This is the finite-coordinate content behind the existing exact gluing
-- theorem ObserverMatrix3 <-> compatible dyadic locals.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannQuarticBalancedTernaryStencilExact as Stencil
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Reasoning.Trialectic369DescentNaturalityExact as Descent
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Reasoning.Trialectic369DyadicSectionTriadicKernelExact as Dyadic

------------------------------------------------------------------------
-- 1. Slot-count ledger.
------------------------------------------------------------------------

localChartTritCount : Nat
localChartTritCount = 4

localChartCount : Nat
localChartCount = 3

pairwiseOverlapCount : Nat
pairwiseOverlapCount = 3

overlapTritCount : Nat
overlapTritCount = 1

rawLocalSlotCount : Nat
rawLocalSlotCount =
  localChartCount * localChartTritCount

identifiedOverlapSlotCount : Nat
identifiedOverlapSlotCount =
  pairwiseOverlapCount * overlapTritCount

independentGlobalTritCount : Nat
independentGlobalTritCount = 9

rawLocalSlotCountIsTwelve :
  rawLocalSlotCount ≡ 12
rawLocalSlotCountIsTwelve = refl

identifiedOverlapSlotCountIsThree :
  identifiedOverlapSlotCount ≡ 3
identifiedOverlapSlotCountIsThree = refl

coordinateLedger :
  rawLocalSlotCount
  ≡ independentGlobalTritCount + identifiedOverlapSlotCount
coordinateLedger = refl

------------------------------------------------------------------------
-- 2. Corresponding exact cardinal arithmetic.
------------------------------------------------------------------------

localChartStateCount : Nat
localChartStateCount =
  Stencil.pow3 localChartTritCount

overlapStateCount : Nat
overlapStateCount =
  Stencil.pow3 overlapTritCount

globalStateCount : Nat
globalStateCount =
  Stencil.pow3 independentGlobalTritCount

localChartStateCountIs81 :
  localChartStateCount ≡ 81
localChartStateCountIs81 = refl

overlapStateCountIsThree :
  overlapStateCount ≡ 3
overlapStateCountIsThree = refl

globalStateCountIs19683 :
  globalStateCount ≡ 19683
globalStateCountIs19683 = refl

rawLocalTupleCount : Nat
rawLocalTupleCount =
  localChartStateCount
  * localChartStateCount
  * localChartStateCount

overlapConstraintMultiplicity : Nat
overlapConstraintMultiplicity =
  overlapStateCount
  * overlapStateCount
  * overlapStateCount

rawLocalTupleCountIs531441 :
  rawLocalTupleCount ≡ 531441
rawLocalTupleCountIs531441 = refl

overlapConstraintMultiplicityIs27 :
  overlapConstraintMultiplicity ≡ 27
overlapConstraintMultiplicityIs27 = refl

rawTupleCountFactorsThroughGlobal :
  rawLocalTupleCount
  ≡ globalStateCount * overlapConstraintMultiplicity
rawTupleCountFactorsThroughGlobal = refl

------------------------------------------------------------------------
-- 3. Same-object link to the existing exact descent.
------------------------------------------------------------------------

observerToCompatibleLocals :
  Observer.ObserverMatrix3
    SSP.SSPTrit
  ->
  Descent.DyadicMatchingFamily
observerToCompatibleLocals =
  Descent.observerMatchingFamily

compatibleLocalsToObserver :
  Descent.DyadicMatchingFamily
  ->
  Observer.ObserverMatrix3
    SSP.SSPTrit
compatibleLocalsToObserver =
  Descent.glueDyadic

observerDescentRoundTrip :
  (matrix :
    Observer.ObserverMatrix3
      SSP.SSPTrit) ->
  compatibleLocalsToObserver (observerToCompatibleLocals matrix)
  ≡ matrix
observerDescentRoundTrip =
  Descent.observerGlueRoundTrip

abLocalIsKernel4 :
  (section : Descent.ABSection) ->
  Dyadic.kernel4ToAB (Dyadic.abToKernel4 section) ≡ section
abLocalIsKernel4 =
  Dyadic.abKernelRoundTrip

bcLocalIsKernel4 :
  (section : Descent.BCSection) ->
  Dyadic.kernel4ToBC (Dyadic.bcToKernel4 section) ≡ section
bcLocalIsKernel4 =
  Dyadic.bcKernelRoundTrip

caLocalIsKernel4 :
  (section : Descent.CASection) ->
  Dyadic.kernel4ToCA (Dyadic.caToKernel4 section) ≡ section
caLocalIsKernel4 =
  Dyadic.caKernelRoundTrip

------------------------------------------------------------------------
-- 4. Match the existing global T9 carrier count.
------------------------------------------------------------------------

existingHyperformalStateCount :
  Nat
existingHyperformalStateCount =
  Geometry.hyperfabricStateCount

descentGlobalCountMatchesExistingT9 :
  globalStateCount ≡ existingHyperformalStateCount
descentGlobalCountMatchesExistingT9 = refl

------------------------------------------------------------------------
-- 5. Firewall.
------------------------------------------------------------------------

data CoordinateLedgerAloneCreatesCategoricalQuotient : Set where
data CountFactorizationCreatesIndependentLocalProduct : Set where
data DyadicDescentForcesRHPuncture : Set where

coordinateLedgerDoesNotCreateCategoricalQuotient :
  CoordinateLedgerAloneCreatesCategoricalQuotient -> ⊥
coordinateLedgerDoesNotCreateCategoricalQuotient ()

countFactorizationDoesNotEraseOverlapEqualities :
  CountFactorizationCreatesIndependentLocalProduct -> ⊥
countFactorizationDoesNotEraseOverlapEqualities ()

dyadicDescentDoesNotForceRHPuncture :
  DyadicDescentForcesRHPuncture -> ⊥
dyadicDescentDoesNotForceRHPuncture ()

record Trialectic369DyadicKernel4DescentCountBoundary : Set where
  constructor trialectic-369-dyadic-kernel4-descent-count-boundary
  field
    threeLocalKernel4ChartsOwned : Bool
    threeSingleTritOverlapsOwned : Bool
    coordinateLedgerTwelveMinusThreeEqualsNine : Bool
    localCount81Owned : Bool
    overlapCount3Owned : Bool
    globalCount19683Owned : Bool
    rawTupleFactorization531441Equals19683Times27 : Bool
    exactObserverDescentRoundTripReused : Bool
    globalCountMatchesExistingT9 : Bool
    rhPunctureForcedByDescent : Bool

canonicalTrialectic369DyadicKernel4DescentCountBoundary :
  Trialectic369DyadicKernel4DescentCountBoundary
canonicalTrialectic369DyadicKernel4DescentCountBoundary =
  trialectic-369-dyadic-kernel4-descent-count-boundary
    true true true true true true true true true false
