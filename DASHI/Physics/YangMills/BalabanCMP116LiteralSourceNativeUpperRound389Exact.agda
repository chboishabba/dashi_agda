{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116LiteralSourceNativeUpperRound389Exact where

------------------------------------------------------------------------
-- ROUND389 / LITERAL SELECTED CMP116 UPPER, WITHOUT POST-HOC SOURCE WELDS
--
-- Historical R309 application packaged three exact identities:
--   source magnitude = selected response,
--   source root      = selected connecting root,
--   source distance  = selected physical distance.
--
-- R342/R343 already removed the first equality from the terminal consumer.
-- R388 shows a decreasing geometric envelope needs only time <= sourceDistance,
-- not either distance equality.  And once the source theorem is stated directly
-- on the literal selected response, the root identity is not observed by the
-- spectral consumer either.
--
-- The least-privilege source-native finite theorem is therefore exactly:
--
--   |selected mixed J response| <= A * q^(sourceDistance)
--   time <= sourceDistance.
--
-- Everything below is transport/compiler work.  The two displayed statements
-- remain theorem-bearing source/application geometry; they are not fabricated.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as Nat
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanSourceNativeDistanceLowerRound388Exact as R388

record LiteralSelectedCMP116SourceNativeUpper : Set₁ where
  field
    selectedResponse : ℚ
    fastAmplitude fastRatio : ℚ
    sourceDistance time : Nat

    fastAmplitudeNonnegative : 0ℚ ℚ.≤ fastAmplitude

    -- Actual source/application theorem on the literal selected response.
    literalSelectedLocalization :
      selectedResponse ℚ.≤
        fastAmplitude * Power.rationalPower fastRatio sourceDistance

    -- Consumer-sufficient geometry; equality is intentionally not required.
    selectedTimeBelowSourceDistance : time Nat.≤ sourceDistance

open LiteralSelectedCMP116SourceNativeUpper public

asRound388DistanceLower :
  LiteralSelectedCMP116SourceNativeUpper → R388.SourceNativeDistanceLowerData
asRound388DistanceLower source = record
  { R388.SourceNativeDistanceLowerData.ratio = fastRatio source
  ; R388.SourceNativeDistanceLowerData.amplitude = fastAmplitude source
  ; R388.SourceNativeDistanceLowerData.response = selectedResponse source
  ; R388.SourceNativeDistanceLowerData.time = time source
  ; R388.SourceNativeDistanceLowerData.sourceDistance = sourceDistance source
  ; R388.SourceNativeDistanceLowerData.amplitudeNonnegative =
      fastAmplitudeNonnegative source
  ; R388.SourceNativeDistanceLowerData.responseBelowSourceDistance =
      literalSelectedLocalization source
  ; R388.SourceNativeDistanceLowerData.timeBelowSourceDistance =
      selectedTimeBelowSourceDistance source
  }

literalSelectedResponseBelowPhysicalTimeGeometric :
  (source : LiteralSelectedCMP116SourceNativeUpper) →
  R388.RationalPowerDistanceAntitone (fastRatio source) →
  selectedResponse source ℚ.≤
    fastAmplitude source * Power.rationalPower (fastRatio source) (time source)
literalSelectedResponseBelowPhysicalTimeGeometric source authority =
  R388.responseBelowPhysicalTimeGeometric
    (asRound388DistanceLower source) authority

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round389LiteralSourceNativeCompilerLevel : ProofLevel
round389LiteralSourceNativeCompilerLevel = machineChecked

postHocSourceMagnitudeEqualityMandatory : Bool
postHocSourceMagnitudeEqualityMandatory = false

postHocSourceMagnitudeEqualityMandatoryIsFalse :
  postHocSourceMagnitudeEqualityMandatory ≡ false
postHocSourceMagnitudeEqualityMandatoryIsFalse = refl

sourceRootIdentityMandatory : Bool
sourceRootIdentityMandatory = false

sourceRootIdentityMandatoryIsFalse :
  sourceRootIdentityMandatory ≡ false
sourceRootIdentityMandatoryIsFalse = refl

sourceDistanceEqualityMandatory : Bool
sourceDistanceEqualityMandatory = false

sourceDistanceEqualityMandatoryIsFalse :
  sourceDistanceEqualityMandatory ≡ false
sourceDistanceEqualityMandatoryIsFalse = refl

literalAbsoluteLocalizationStillProofBearing : Bool
literalAbsoluteLocalizationStillProofBearing = true

literalAbsoluteLocalizationStillProofBearingIsTrue :
  literalAbsoluteLocalizationStillProofBearing ≡ true
literalAbsoluteLocalizationStillProofBearingIsTrue = refl

selectedTimeLowerGeometryStillProofBearing : Bool
selectedTimeLowerGeometryStillProofBearing = true

selectedTimeLowerGeometryStillProofBearingIsTrue :
  selectedTimeLowerGeometryStillProofBearing ≡ true
selectedTimeLowerGeometryStillProofBearingIsTrue = refl

record Round389Boundary : Set where
  constructor round389-boundary
  field
    selectedResponseIsLiteralByConstruction : Bool
    selectedResponseIsLiteralByConstructionIsTrue :
      selectedResponseIsLiteralByConstruction ≡ true

    exactRootAndDistanceWeldsPruned : Bool
    exactRootAndDistanceWeldsPrunedIsTrue :
      exactRootAndDistanceWeldsPruned ≡ true

    sourceReplayStillRequired : Bool
    sourceReplayStillRequiredIsTrue : sourceReplayStillRequired ≡ true

canonicalRound389Boundary : Round389Boundary
canonicalRound389Boundary = round389-boundary true refl true refl true refl

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
