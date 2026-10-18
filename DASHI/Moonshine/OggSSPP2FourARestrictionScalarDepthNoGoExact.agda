module DASHI.Moonshine.OggSSPP2FourARestrictionScalarDepthNoGoExact where

------------------------------------------------------------------------
-- p=2 4A-RESTRICTION SCALAR-DEPTH NO-GO
--
-- EXTERNAL SOURCE INPUT
--
-- Carnahan--Urano determine the actual 4A integral indecomposable families
-- and their restriction to the square subgroup <g^2> in class 2B.  Combined
-- with the sourced 2B Tate split, the live repository has exactly four
-- source-native 4A/parity/Tate-support patterns:
--
--   even A      : one nonzero Tate simple-factor type
--   even D      : Tate acyclic
--   odd D       : Tate acyclic
--   odd C^A     : one nonzero Tate simple-factor type
--
-- DASHI RESULT
--
-- If one observes ONLY that coarse restricted Tate support, its scalar proxy is
-- 1/0/0/1.  It cannot pay the reduced p=2 source-depth profile
--
--   3,3,2,1,1.
--
-- Therefore the missing p=2 scalar authority requires an additional integral
-- extension/filtration/multiplicity-depth coordinate.  4A label + parity +
-- binary Tate support alone is formally insufficient.
--
-- ATTRIBUTION
--
-- Carnahan--Urano own the 4A decomposition/restriction facts.  DASHI owns only
-- this nonfactorability/no-go comparison against the independently defined
-- scalar consumer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSP4A2BTateRefinementFiveSectorNoGoExact as FourA
import DASHI.Moonshine.OggSSPP2InertiaDepthQuotientExact as Scalar
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Coarse source-native Tate-support length proxy.
--
-- This is deliberately only the number of nonzero simple Tate-support units
-- visible at the 4A-label/parity support level.  It is NOT Urano finite-DVR
-- composition length for a localized p=2 source piece.
------------------------------------------------------------------------

coarseTateSupportLength :
  FourA.FourATateRefinedPattern ->
  Nat
coarseTateSupportLength FourA.evenAH1 = 1
coarseTateSupportLength FourA.evenDAcyclic = 0
coarseTateSupportLength FourA.oddDAcyclic = 0
coarseTateSupportLength FourA.oddCAH0 = 1

coarseTateSupportLengthAtMostOne :
  (pattern : FourA.FourATateRefinedPattern) ->
  coarseTateSupportLength pattern ≡ 0
  ⊎
  coarseTateSupportLength pattern ≡ 1
coarseTateSupportLengthAtMostOne FourA.evenAH1 =
  inj₂ refl
coarseTateSupportLengthAtMostOne FourA.evenDAcyclic =
  inj₁ refl
coarseTateSupportLengthAtMostOne FourA.oddDAcyclic =
  inj₁ refl
coarseTateSupportLengthAtMostOne FourA.oddCAH0 =
  inj₂ refl

------------------------------------------------------------------------
-- 2. Exact attempted scalar-depth payment.
------------------------------------------------------------------------

record FourATatePatternPaysP2ScalarDepth : Set where
  field
    sourcePattern :
      Scalar.P2ScalarSlot ->
      FourA.FourATateRefinedPattern

    preservesScalarDepth :
      (slot : Scalar.P2ScalarSlot) ->
      coarseTateSupportLength (sourcePattern slot)
      ≡
      Scalar.slotLength slot

open FourATatePatternPaysP2ScalarDepth public

------------------------------------------------------------------------
-- 3. High-slot contradiction: desired length 3 cannot come from 0/1 support.
------------------------------------------------------------------------

noFourATatePatternPaysHighSlot :
  (pattern : FourA.FourATateRefinedPattern) ->
  coarseTateSupportLength pattern
  ≡ Scalar.slotLength Scalar.highSlotA
  ->
  ⊥
noFourATatePatternPaysHighSlot FourA.evenAH1 ()
noFourATatePatternPaysHighSlot FourA.evenDAcyclic ()
noFourATatePatternPaysHighSlot FourA.oddDAcyclic ()
noFourATatePatternPaysHighSlot FourA.oddCAH0 ()

noFourATatePatternPaysP2ScalarDepth :
  FourATatePatternPaysP2ScalarDepth ->
  ⊥
noFourATatePatternPaysP2ScalarDepth payment =
  noFourATatePatternPaysHighSlot
    (sourcePattern payment Scalar.highSlotA)
    (preservesScalarDepth payment Scalar.highSlotA)

------------------------------------------------------------------------
-- 4. The missing coordinate must be extension/filtration sensitive.
------------------------------------------------------------------------

data BinaryTateSupportAlonePaysThreeThreeTwoOneOne : Set where
data FourALabelParitySupportContainsLengthThree : Set where
data FourALabelParitySupportContainsLengthTwo : Set where
data NeedAdditionalIntegralDepthCoordinate : Set where
  additionalIntegralDepthCoordinateRequired :
    NeedAdditionalIntegralDepthCoordinate

binaryTateSupportAloneDoesNotPayProfile :
  BinaryTateSupportAlonePaysThreeThreeTwoOneOne -> ⊥
binaryTateSupportAloneDoesNotPayProfile ()

coarseSupportDoesNotContainLengthThree :
  FourALabelParitySupportContainsLengthThree -> ⊥
coarseSupportDoesNotContainLengthThree ()

coarseSupportDoesNotContainLengthTwo :
  FourALabelParitySupportContainsLengthTwo -> ⊥
coarseSupportDoesNotContainLengthTwo ()

p2NeedsAdditionalIntegralDepthCoordinate :
  NeedAdditionalIntegralDepthCoordinate
p2NeedsAdditionalIntegralDepthCoordinate =
  additionalIntegralDepthCoordinateRequired

------------------------------------------------------------------------
-- 5. What kind of refinement is now admissible.
--
-- We do not manufacture its values.  A future source-backed refinement must
-- retain a depth coordinate beyond coarse support and prove that coordinate is
-- computed from the actual integral 2B/4A-restricted source object.
------------------------------------------------------------------------

record P2IntegralDepthRefinement : Set₁ where
  field
    SourcePiece :
      Set

    coarseFourATatePattern :
      SourcePiece ->
      FourA.FourATateRefinedPattern

    integralExtensionDepth :
      SourcePiece ->
      Nat

    depthComesFromIntegralSourceFiltration :
      SourcePiece ->
      Bool

    depthComesFromIntegralSourceFiltrationIsTrue :
      (piece : SourcePiece) ->
      depthComesFromIntegralSourceFiltration piece ≡ true

    depthNotDefinedFromMonsterResidual :
      Bool
    depthNotDefinedFromMonsterResidualIsTrue :
      depthNotDefinedFromMonsterResidual ≡ true

    depthNotDefinedFromBase369 :
      Bool
    depthNotDefinedFromBase369IsTrue :
      depthNotDefinedFromBase369 ≡ true

open P2IntegralDepthRefinement public

data P2IntegralDepthRefinementInhabited : Set where

p2IntegralDepthRefinementStillOpen :
  P2IntegralDepthRefinementInhabited -> ⊥
p2IntegralDepthRefinementStillOpen ()

------------------------------------------------------------------------
-- 6. Attribution boundary.
------------------------------------------------------------------------

data CarnahanUranoCreditedWithThreeThreeTwoOneOne : Set where
data CarnahanUranoCreditedWithIntegralDepthRefinement : Set where

carnahanUranoNotCreditedWithTargetDepthProfile :
  CarnahanUranoCreditedWithThreeThreeTwoOneOne -> ⊥
carnahanUranoNotCreditedWithTargetDepthProfile ()

carnahanUranoNotCreditedWithMissingRefinement :
  CarnahanUranoCreditedWithIntegralDepthRefinement -> ⊥
carnahanUranoNotCreditedWithMissingRefinement ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record P2FourARestrictionScalarDepthNoGoBoundary : Set where
  constructor p2-four-a-restriction-scalar-depth-no-go-boundary
  field
    fourATateSupportPatternsExternallySourced : Bool
    coarseSupportProxyOnlyZeroOrOne : Bool
    p2ScalarProfileThreeThreeTwoOneOneOwned : Bool
    exactCoarseSupportPaymentBlocked : Bool
    lengthThreeUnavailableAtCoarseSupportLevel : Bool
    lengthTwoUnavailableAtCoarseSupportLevel : Bool
    additionalIntegralDepthCoordinateRequired : Bool
    additionalIntegralDepthCoordinateSpecified : Bool
    additionalIntegralDepthCoordinateInhabited : Bool
    targetProfileAttributedToCarnahanUrano : Bool
    missingDepthRefinementAttributedToCarnahanUrano : Bool
    monsterResidualUsedToDefineMissingDepth : Bool
    base369UsedToDefineMissingDepth : Bool
    attributionFirewallPreserved : Bool

canonicalP2FourARestrictionScalarDepthNoGoBoundary :
  P2FourARestrictionScalarDepthNoGoBoundary
canonicalP2FourARestrictionScalarDepthNoGoBoundary =
  p2-four-a-restriction-scalar-depth-no-go-boundary
    true true true true true true true true false
    false false false false true
