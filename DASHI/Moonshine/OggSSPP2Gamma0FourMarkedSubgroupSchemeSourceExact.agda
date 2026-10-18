module DASHI.Moonshine.OggSSPP2Gamma0FourMarkedSubgroupSchemeSourceExact where

------------------------------------------------------------------------
-- p=2 GAMMA_0(4) MARKED FINITE-FLAT SUBGROUP-SCHEME SOURCE SOCKET
--
-- EXTERNAL SOURCE CONTEXT
--
-- Katz--Mazur integral models distinguish bad-prime level structures from
-- naive etale point sets.  For Gamma_0(4), the relevant datum is cyclic
-- finite-flat subgroup / isogeny data of order 4, with its canonical order-2
-- subflag, not a choice of one ordinary E[4] point.
--
-- DASHI CONTRIBUTION
--
-- Package exactly the source-side data still missing from the p=2 lane:
--
--   supersingular elliptic object in characteristic 2
--   finite-flat cyclic order-4 subgroup C4
--   canonical order-2 subflag C2 <= C4
--   Frobenius transport on the marked object
--   coarse projection to the three F4/F2 Frobenius strata
--   dependent marking over those strata
--   comparison with the paid target normal form
--
--       Unit, Unit, punctured T^2.
--
-- This module does not construct any of these arithmetic objects.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Core.DependentRecoverableProjectionExact as Dependent
import DASHI.Moonshine.OggSSPP2F4FrobeniusCandidateNoGoExact as F4
import DASHI.Moonshine.OggSSPP2F4DependentMarkedCoverExact as TargetMark
import DASHI.Moonshine.OggSSPP2BalancedTernaryPuncturedPlaneExact as Plane
import DASHI.Moonshine.OggSSPP2BadPrimeLevelStructureBoundaryExact as BadPrime
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Abstract finite-flat Gamma_0(4) arithmetic carrier.
------------------------------------------------------------------------

record Gamma0FourFiniteFlatDatum : Set₁ where
  field
    EllipticObject : Set
    OrderFourSubgroup : Set
    OrderTwoSubgroup : Set

    selectedEllipticObject : EllipticObject
    selectedOrderFourSubgroup : OrderFourSubgroup
    selectedOrderTwoSubgroup : OrderTwoSubgroup

    orderFourRank : Nat
    orderFourRankIsFour :
      orderFourRank ≡ 4

    orderTwoRank : Nat
    orderTwoRankIsTwo :
      orderTwoRank ≡ 2

    orderTwoSubflagOfOrderFour : Bool
    orderTwoSubflagOfOrderFourIsTrue :
      orderTwoSubflagOfOrderFour ≡ true

    finiteFlatAtCharacteristicTwo : Bool
    finiteFlatAtCharacteristicTwoIsTrue :
      finiteFlatAtCharacteristicTwo ≡ true

    gammaZeroLevelFourSemantics : Bool
    gammaZeroLevelFourSemanticsIsTrue :
      gammaZeroLevelFourSemantics ≡ true

    sourceReference : String

open Gamma0FourFiniteFlatDatum public

------------------------------------------------------------------------
-- 2. Marked arithmetic state and Frobenius transport.
------------------------------------------------------------------------

record Gamma0FourMarkedArithmeticSource : Set₁ where
  field
    datum : Gamma0FourFiniteFlatDatum

    MarkedState : Set

    frobenius :
      MarkedState -> MarkedState

    frobeniusInvolutive :
      (state : MarkedState) ->
      frobenius (frobenius state) ≡ state

    coarseF4Orbit :
      MarkedState ->
      F4.F4FrobeniusOrbit

    coarseF4OrbitInvariant :
      (state : MarkedState) ->
      coarseF4Orbit (frobenius state)
      ≡ coarseF4Orbit state

open Gamma0FourMarkedArithmeticSource public

------------------------------------------------------------------------
-- 3. Required dependent marking comparison.
--
-- A lawful source must expose a recoverable projection over the three F4
-- strata and identify each arithmetic mark fibre with the already-paid target
-- fibre.  This is stronger than count equality.
------------------------------------------------------------------------

record Gamma0FourOneOneEightRecognition
  (source : Gamma0FourMarkedArithmeticSource) : Set₁ where
  field
    ArithmeticMark :
      F4.F4FrobeniusOrbit -> Set

    projection :
      Dependent.DependentExactRecoverableProjection
        (MarkedState source)
        F4.F4FrobeniusOrbit

    projectionUsesArithmeticMark :
      (orbit : F4.F4FrobeniusOrbit) ->
      Dependent.Residual projection orbit
      ≡ ArithmeticMark orbit

    zeroFixedMarkToTarget :
      ArithmeticMark F4.zeroFixedOrbit ->
      TargetMark.F4OrbitMark F4.zeroFixedOrbit

    zeroFixedMarkFromTarget :
      TargetMark.F4OrbitMark F4.zeroFixedOrbit ->
      ArithmeticMark F4.zeroFixedOrbit

    zeroFixedRoundTripSource :
      (mark : ArithmeticMark F4.zeroFixedOrbit) ->
      zeroFixedMarkFromTarget (zeroFixedMarkToTarget mark)
      ≡ mark

    zeroFixedRoundTripTarget :
      (mark : TargetMark.F4OrbitMark F4.zeroFixedOrbit) ->
      zeroFixedMarkToTarget (zeroFixedMarkFromTarget mark)
      ≡ mark

    oneFixedMarkToTarget :
      ArithmeticMark F4.oneFixedOrbit ->
      TargetMark.F4OrbitMark F4.oneFixedOrbit

    oneFixedMarkFromTarget :
      TargetMark.F4OrbitMark F4.oneFixedOrbit ->
      ArithmeticMark F4.oneFixedOrbit

    oneFixedRoundTripSource :
      (mark : ArithmeticMark F4.oneFixedOrbit) ->
      oneFixedMarkFromTarget (oneFixedMarkToTarget mark)
      ≡ mark

    oneFixedRoundTripTarget :
      (mark : TargetMark.F4OrbitMark F4.oneFixedOrbit) ->
      oneFixedMarkToTarget (oneFixedMarkFromTarget mark)
      ≡ mark

    conjugateMarkToPuncturedPlane :
      ArithmeticMark F4.conjugatePairOrbit ->
      Plane.PuncturedNineSheet

    puncturedPlaneToConjugateMark :
      Plane.PuncturedNineSheet ->
      ArithmeticMark F4.conjugatePairOrbit

    conjugateRoundTripSource :
      (mark : ArithmeticMark F4.conjugatePairOrbit) ->
      puncturedPlaneToConjugateMark
        (conjugateMarkToPuncturedPlane mark)
      ≡ mark

    conjugateRoundTripTarget :
      (point : Plane.PuncturedNineSheet) ->
      conjugateMarkToPuncturedPlane
        (puncturedPlaneToConjugateMark point)
      ≡ point

    frobeniusCompatibility : Bool
    frobeniusCompatibilityIsTrue :
      frobeniusCompatibility ≡ true

open Gamma0FourOneOneEightRecognition public

------------------------------------------------------------------------
-- 4. The exact target cardinal profile follows from the stronger fibre data.
------------------------------------------------------------------------

targetZeroFixedMarkCount : Nat
targetZeroFixedMarkCount = 1

targetOneFixedMarkCount : Nat
targetOneFixedMarkCount = 1

targetConjugateMarkCount : Nat
targetConjugateMarkCount = Plane.puncturedNineSheetCount

targetConjugateMarkCountIsEight :
  targetConjugateMarkCount ≡ 8
targetConjugateMarkCountIsEight =
  Plane.puncturedNineSheetCountIsThreeSquaredMinusOne

targetTotalMarkCount : Nat
targetTotalMarkCount =
  targetZeroFixedMarkCount
  + targetOneFixedMarkCount
  + targetConjugateMarkCount

targetTotalMarkCountIsTen :
  targetTotalMarkCount ≡ 10
targetTotalMarkCountIsTen = refl

------------------------------------------------------------------------
-- 5. Wrong-source firewalls.
------------------------------------------------------------------------

data FullDrinfeldBasisIsGamma0FourDatum : Set where
data Gamma1PointIsGamma0FourDatum : Set where
data NaiveE4PointSetIsGamma0FourDatum : Set where
data OneOneEightCountCreatesArithmeticRecognition : Set where

fullDrinfeldBasisDoesNotBecomeGamma0FourDatum :
  FullDrinfeldBasisIsGamma0FourDatum -> ⊥
fullDrinfeldBasisDoesNotBecomeGamma0FourDatum ()

gamma1PointDoesNotBecomeGamma0FourDatum :
  Gamma1PointIsGamma0FourDatum -> ⊥
gamma1PointDoesNotBecomeGamma0FourDatum ()

naiveE4PointSetDoesNotBecomeGamma0FourDatum :
  NaiveE4PointSetIsGamma0FourDatum -> ⊥
naiveE4PointSetDoesNotBecomeGamma0FourDatum ()

oneOneEightCountDoesNotCreateArithmeticRecognition :
  OneOneEightCountCreatesArithmeticRecognition -> ⊥
oneOneEightCountDoesNotCreateArithmeticRecognition ()

------------------------------------------------------------------------
-- 6. Frontier.
------------------------------------------------------------------------

data Gamma0FourSourceResidual : Set where
  missingConcreteFiniteFlatCanonicalFlagRealization :
    Gamma0FourSourceResidual
  missingArithmeticFrobeniusTransport :
    Gamma0FourSourceResidual
  missingArithmeticOneOneEightFibreEquivalence :
    Gamma0FourSourceResidual
  missingActionOrbitStabilizerRecognition :
    Gamma0FourSourceResidual

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryNewExtension

record Gamma0FourMarkedSubgroupSchemeSourceBoundary : Set where
  constructor gamma0-four-marked-subgroup-scheme-source-boundary
  field
    badPrimeModuliBoundaryConsumed : Bool
    gamma0TypedAsSubgroupSchemeDatum : Bool
    canonicalRawKerFFlagOwned : Bool
    orderTwoSubflagRequired : Bool
    fullDrinfeldBasisRejectedAsAutomaticSubstitute : Bool
    gamma1PointRejectedAsAutomaticSubstitute : Bool
    naiveE4PointSetRejectedAsAutomaticSubstitute : Bool
    oneOneEightTargetFibreTyped : Bool
    arithmeticGamma0FourSourceConstructed : Bool
    arithmeticFibreEquivalenceConstructed : Bool
    fullRecognitionConstructed : Bool
    firstResidual : Gamma0FourSourceResidual

canonicalGamma0FourMarkedSubgroupSchemeSourceBoundary :
  Gamma0FourMarkedSubgroupSchemeSourceBoundary
canonicalGamma0FourMarkedSubgroupSchemeSourceBoundary =
  gamma0-four-marked-subgroup-scheme-source-boundary
    true true true true true true true true
    false false false
    missingConcreteFiniteFlatCanonicalFlagRealization
