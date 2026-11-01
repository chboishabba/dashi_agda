{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116PhysicalDistanceLowerRound390Exact where

------------------------------------------------------------------------
-- ROUND390 / MATURE HALF-RATIO ROUTE NEEDS ONLY time <= physicalDistance
--
-- R346's finite upper is already obtained on the ACTUAL selected physical
-- support distance:
--
--   covariance <= A_H * (1/2)^d_phys.
--
-- It then asks for the exact identity d_phys = time.  That equality is stronger
-- than the decreasing geometric consumer observes.  This file proves the
-- elementary antitonicity of `halfPower` in its Nat exponent and exports the
-- least-privilege transport
--
--   time <= d_phys
--   -------------------------------
--   A_H 2^(-d_phys) <= A_H 2^(-time).
--
-- Thus the source/application geometry may prove only a one-sided separation
-- lower bound.  No new YM decay estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base as Nat using (_≤_; z≤n; s≤s)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

halfBelowOne : Geo.half ≤ 1ℚ
halfBelowOne = toWitness {a? = Geo.half ≤? 1ℚ} _

halfPowerAtMostOne : ∀ depth → Geo.halfPower depth ≤ 1ℚ
halfPowerAtMostOne zero = ℚP.≤-refl
halfPowerAtMostOne (suc depth) =
  let
    productBelowOne :
      Geo.half * Geo.halfPower depth ≤ 1ℚ * 1ℚ
    productBelowOne =
      ℚP.*-mono-≤
        Geo.halfNonnegative
        halfBelowOne
        (Geo.halfPowerNonnegative depth)
        (halfPowerAtMostOne depth)
  in
  subst
    (λ upper → Geo.halfPower (suc depth) ≤ upper)
    (ℚP.*-identityˡ 1ℚ)
    productBelowOne

halfPowerAntitone : ∀ {near far : Nat} →
  near Nat.≤ far → Geo.halfPower far ≤ Geo.halfPower near
halfPowerAntitone {zero} {far} z≤n = halfPowerAtMostOne far
halfPowerAntitone {suc near} {suc far} (s≤s proof) =
  Norm.scaleNonnegative
    Geo.half
    Geo.halfNonnegative
    (halfPowerAntitone proof)

record PhysicalDistanceLowerGeometricData : Set₁ where
  field
    response amplitude : ℚ
    time physicalDistance : Nat

    amplitudeNonnegative : 0ℚ ≤ amplitude

    responseBelowPhysicalDistance :
      response ≤ amplitude * Geo.halfPower physicalDistance

    timeBelowPhysicalDistance : time Nat.≤ physicalDistance

open PhysicalDistanceLowerGeometricData public

responseBelowTimeGeometric :
  (dataSet : PhysicalDistanceLowerGeometricData) →
  response dataSet ≤ amplitude dataSet * Geo.halfPower (time dataSet)
responseBelowTimeGeometric dataSet =
  ℚP.≤-trans
    (responseBelowPhysicalDistance dataSet)
    (Norm.scaleNonnegative
      (amplitude dataSet)
      (amplitudeNonnegative dataSet)
      (halfPowerAntitone (timeBelowPhysicalDistance dataSet)))

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round390HalfPowerAntitoneLevel : ProofLevel
round390HalfPowerAntitoneLevel = machineChecked

round390DistanceLowerCompilerLevel : ProofLevel
round390DistanceLowerCompilerLevel = machineChecked

selectedPhysicalDistanceEqualsTimeMandatory : Bool
selectedPhysicalDistanceEqualsTimeMandatory = false

selectedPhysicalDistanceEqualsTimeMandatoryIsFalse :
  selectedPhysicalDistanceEqualsTimeMandatory ≡ false
selectedPhysicalDistanceEqualsTimeMandatoryIsFalse = refl

selectedTimeBelowPhysicalDistanceStillProofBearing : Bool
selectedTimeBelowPhysicalDistanceStillProofBearing = true

selectedTimeBelowPhysicalDistanceStillProofBearingIsTrue :
  selectedTimeBelowPhysicalDistanceStillProofBearing ≡ true
selectedTimeBelowPhysicalDistanceStillProofBearingIsTrue = refl

fixedHalfRouteStillSufficient : Bool
fixedHalfRouteStillSufficient = true

fixedHalfRouteStillSufficientIsTrue :
  fixedHalfRouteStillSufficient ≡ true
fixedHalfRouteStillSufficientIsTrue = refl

record Round390Boundary : Set where
  constructor round390-boundary
  field
    exactDistanceTimeEqualityPruned : Bool
    exactDistanceTimeEqualityPrunedIsTrue :
      exactDistanceTimeEqualityPruned ≡ true

    oneSidedSupportSeparationSuffices : Bool
    oneSidedSupportSeparationSufficesIsTrue :
      oneSidedSupportSeparationSuffices ≡ true

    literalSelectedLocalizationStillProofBearing : Bool
    literalSelectedLocalizationStillProofBearingIsTrue :
      literalSelectedLocalizationStillProofBearing ≡ true

canonicalRound390Boundary : Round390Boundary
canonicalRound390Boundary =
  round390-boundary true refl true refl true refl

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
