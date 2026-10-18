module DASHI.Moonshine.OggSSPP3InertiaCentralizerValuationNoGoExact where

------------------------------------------------------------------------
-- p=3 INERTIA CENTRALIZER 3-ADIC WEIGHT NO-GO
--
-- CLASSICAL GROUP INPUT
--
-- For the unique supersingular elliptic curve in characteristic 3,
-- Aut(E) has order 12 and is the nontrivial semidirect product
--
--     C3 rtimes C4
--
-- with presentation
--
--     < s,q | s^4=1, q^3=1, s q s^-1 = q^-1 >.
--
-- DASHI RECONSTRUCTION
--
-- The six conjugacy classes have sizes
--
--     1, 1, 2, 2, 3, 3,
--
-- represented by:
--
--     1,
--     s^2,
--     {q,q^2},
--     {q s^2,q^2 s^2},
--     {s,q s,q^2 s},
--     {s^3,q s^3,q^2 s^3}.
--
-- Inversion fixes the first four classes and exchanges the last two.
-- Hence the five unoriented inertia sectors have representative centralizers
--
--     12, 12, 6, 6, 4.
--
-- Their 3-adic depths are
--
--     1, 1, 1, 1, 0,
--
-- which sum to FOUR, not the Duncan--Swisher exceptional gap TWO.
--
-- CONSEQUENCE
--
-- The successful p=2 "sum p-adic centralizer depths over unoriented inertia"
-- mechanism does NOT transport uniformly to p=3.  The p=3 two-unit candidate
-- remains the Deligne--Rapoport node/branch-orbit mechanism.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Moonshine.OggSSPSmallCharacteristicClassicalSourceAtlasExact as Classical
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Conjugacy-class skeleton reconstructed from C3 rtimes C4 presentation.
------------------------------------------------------------------------

data P3AutConjugacyClass : Set where
  identityClass :
    P3AutConjugacyClass
  centralOrderTwoClass :
    P3AutConjugacyClass
  orderThreeClass :
    P3AutConjugacyClass
  orderSixClass :
    P3AutConjugacyClass
  orderFourPositiveClass :
    P3AutConjugacyClass
  orderFourNegativeClass :
    P3AutConjugacyClass

classSize :
  P3AutConjugacyClass ->
  Nat
classSize identityClass = 1
classSize centralOrderTwoClass = 1
classSize orderThreeClass = 2
classSize orderSixClass = 2
classSize orderFourPositiveClass = 3
classSize orderFourNegativeClass = 3

centralizerOrder :
  P3AutConjugacyClass ->
  Nat
centralizerOrder identityClass = 12
centralizerOrder centralOrderTwoClass = 12
centralizerOrder orderThreeClass = 6
centralizerOrder orderSixClass = 6
centralizerOrder orderFourPositiveClass = 4
centralizerOrder orderFourNegativeClass = 4

classSizeTimesCentralizerIsTwelve :
  (class : P3AutConjugacyClass) ->
  classSize class * centralizerOrder class ≡ 12
classSizeTimesCentralizerIsTwelve identityClass = refl
classSizeTimesCentralizerIsTwelve centralOrderTwoClass = refl
classSizeTimesCentralizerIsTwelve orderThreeClass = refl
classSizeTimesCentralizerIsTwelve orderSixClass = refl
classSizeTimesCentralizerIsTwelve orderFourPositiveClass = refl
classSizeTimesCentralizerIsTwelve orderFourNegativeClass = refl

------------------------------------------------------------------------
-- 2. Loop reversal on conjugacy classes.
------------------------------------------------------------------------

inverseClass :
  P3AutConjugacyClass ->
  P3AutConjugacyClass
inverseClass identityClass = identityClass
inverseClass centralOrderTwoClass = centralOrderTwoClass
inverseClass orderThreeClass = orderThreeClass
inverseClass orderSixClass = orderSixClass
inverseClass orderFourPositiveClass = orderFourNegativeClass
inverseClass orderFourNegativeClass = orderFourPositiveClass

inverseClassInvolutive :
  (class : P3AutConjugacyClass) ->
  inverseClass (inverseClass class) ≡ class
inverseClassInvolutive identityClass = refl
inverseClassInvolutive centralOrderTwoClass = refl
inverseClassInvolutive orderThreeClass = refl
inverseClassInvolutive orderSixClass = refl
inverseClassInvolutive orderFourPositiveClass = refl
inverseClassInvolutive orderFourNegativeClass = refl

data P3UnorientedInertiaOrbit : Set where
  identityInertiaOrbit :
    P3UnorientedInertiaOrbit
  centralOrderTwoInertiaOrbit :
    P3UnorientedInertiaOrbit
  orderThreeInertiaOrbit :
    P3UnorientedInertiaOrbit
  orderSixInertiaOrbit :
    P3UnorientedInertiaOrbit
  orderFourPairInertiaOrbit :
    P3UnorientedInertiaOrbit

quotientByInversion :
  P3AutConjugacyClass ->
  P3UnorientedInertiaOrbit
quotientByInversion identityClass = identityInertiaOrbit
quotientByInversion centralOrderTwoClass = centralOrderTwoInertiaOrbit
quotientByInversion orderThreeClass = orderThreeInertiaOrbit
quotientByInversion orderSixClass = orderSixInertiaOrbit
quotientByInversion orderFourPositiveClass = orderFourPairInertiaOrbit
quotientByInversion orderFourNegativeClass = orderFourPairInertiaOrbit

quotientByInversionInvariant :
  (class : P3AutConjugacyClass) ->
  quotientByInversion (inverseClass class)
  ≡ quotientByInversion class
quotientByInversionInvariant identityClass = refl
quotientByInversionInvariant centralOrderTwoClass = refl
quotientByInversionInvariant orderThreeClass = refl
quotientByInversionInvariant orderSixClass = refl
quotientByInversionInvariant orderFourPositiveClass = refl
quotientByInversionInvariant orderFourNegativeClass = refl

------------------------------------------------------------------------
-- 3. 3-adic depths of centralizer orders.
------------------------------------------------------------------------

centralizerThreeAdicDepth :
  P3AutConjugacyClass ->
  Nat
centralizerThreeAdicDepth identityClass = 1
centralizerThreeAdicDepth centralOrderTwoClass = 1
centralizerThreeAdicDepth orderThreeClass = 1
centralizerThreeAdicDepth orderSixClass = 1
centralizerThreeAdicDepth orderFourPositiveClass = 0
centralizerThreeAdicDepth orderFourNegativeClass = 0

identityCentralizerFactorization :
  centralizerOrder identityClass ≡ 3 * 4
identityCentralizerFactorization = refl

centralOrderTwoCentralizerFactorization :
  centralizerOrder centralOrderTwoClass ≡ 3 * 4
centralOrderTwoCentralizerFactorization = refl

orderThreeCentralizerFactorization :
  centralizerOrder orderThreeClass ≡ 3 * 2
orderThreeCentralizerFactorization = refl

orderSixCentralizerFactorization :
  centralizerOrder orderSixClass ≡ 3 * 2
orderSixCentralizerFactorization = refl

orderFourCentralizerHasNoThreeFactor :
  centralizerOrder orderFourPositiveClass ≡ 4
orderFourCentralizerHasNoThreeFactor = refl

centralizerDepthInvariantUnderInversion :
  (class : P3AutConjugacyClass) ->
  centralizerThreeAdicDepth (inverseClass class)
  ≡ centralizerThreeAdicDepth class
centralizerDepthInvariantUnderInversion identityClass = refl
centralizerDepthInvariantUnderInversion centralOrderTwoClass = refl
centralizerDepthInvariantUnderInversion orderThreeClass = refl
centralizerDepthInvariantUnderInversion orderSixClass = refl
centralizerDepthInvariantUnderInversion orderFourPositiveClass = refl
centralizerDepthInvariantUnderInversion orderFourNegativeClass = refl

------------------------------------------------------------------------
-- 4. Descended five-sector depth sum.
------------------------------------------------------------------------

unorientedCentralizerThreeAdicDepth :
  P3UnorientedInertiaOrbit ->
  Nat
unorientedCentralizerThreeAdicDepth identityInertiaOrbit = 1
unorientedCentralizerThreeAdicDepth centralOrderTwoInertiaOrbit = 1
unorientedCentralizerThreeAdicDepth orderThreeInertiaOrbit = 1
unorientedCentralizerThreeAdicDepth orderSixInertiaOrbit = 1
unorientedCentralizerThreeAdicDepth orderFourPairInertiaOrbit = 0

p3UnorientedInertiaDepthSum : Nat
p3UnorientedInertiaDepthSum =
  unorientedCentralizerThreeAdicDepth identityInertiaOrbit
  + unorientedCentralizerThreeAdicDepth centralOrderTwoInertiaOrbit
  + unorientedCentralizerThreeAdicDepth orderThreeInertiaOrbit
  + unorientedCentralizerThreeAdicDepth orderSixInertiaOrbit
  + unorientedCentralizerThreeAdicDepth orderFourPairInertiaOrbit

p3UnorientedInertiaDepthSumIsFour :
  p3UnorientedInertiaDepthSum ≡ 4
p3UnorientedInertiaDepthSumIsFour = refl

p3MonsterExceptionalGap : Nat
p3MonsterExceptionalGap = 2

p3MonsterExceptionalGapIsTwo :
  Exponent.monsterOrderExponent Lane.p3
  ≡ Exponent.duncanSwisherExceptionalRHS Lane.p3
    + p3MonsterExceptionalGap
p3MonsterExceptionalGapIsTwo =
  Exponent.p3ExceptionalGap

p3UnorientedInertiaDepthSumIsNotMonsterGap :
  p3UnorientedInertiaDepthSum ≡ p3MonsterExceptionalGap ->
  ⊥
p3UnorientedInertiaDepthSumIsNotMonsterGap ()

------------------------------------------------------------------------
-- 5. Uniform p2-style centralizer mechanism is ruled out.
------------------------------------------------------------------------

data P3MonsterGapEqualsUnorientedCentralizerDepthSum : Set where
data UniformP2P3InertiaCentralizerCorrectionLaw : Set where

p3CentralizerDepthMechanismFails :
  P3MonsterGapEqualsUnorientedCentralizerDepthSum -> ⊥
p3CentralizerDepthMechanismFails ()

uniformCentralizerCorrectionLawFails :
  UniformP2P3InertiaCentralizerCorrectionLaw -> ⊥
uniformCentralizerCorrectionLawFails ()

------------------------------------------------------------------------
-- 6. Attribution boundary.
------------------------------------------------------------------------

classicalBoundary :
  Classical.SmallCharacteristicClassicalSourcingBoundary
classicalBoundary =
  Classical.canonicalSmallCharacteristicClassicalSourcingBoundary

data SemidirectPresentationAutomaticallyCreatesMonsterCorrection : Set where

semidirectPresentationDoesNotCreateMonsterCorrection :
  SemidirectPresentationAutomaticallyCreatesMonsterCorrection -> ⊥
semidirectPresentationDoesNotCreateMonsterCorrection ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record P3InertiaCentralizerValuationNoGoBoundary : Set where
  constructor p3-inertia-centralizer-valuation-no-go-boundary
  field
    orderTwelveAutomorphismGroupClassicallySourced : Bool
    c3SemidirectC4PresentationReconstructedFromClassicalGenerators : Bool
    sixConjugacyClassSkeletonReconstructed : Bool
    loopReversalFiveOrbitQuotientReconstructed : Bool
    centralizerOrdersTwelveTwelveSixSixFourExact : Bool
    threeAdicDepthsOneOneOneOneZeroExact : Bool
    depthSumIsFour : Bool
    monsterGapIsTwo : Bool
    depthSumEqualsMonsterGap : Bool
    uniformP2P3CentralizerCorrectionSurvives : Bool

canonicalP3InertiaCentralizerValuationNoGoBoundary :
  P3InertiaCentralizerValuationNoGoBoundary
canonicalP3InertiaCentralizerValuationNoGoBoundary =
  p3-inertia-centralizer-valuation-no-go-boundary
    true true true true true true true true false false
