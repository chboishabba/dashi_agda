{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSourceNativeDistanceLowerRound388Exact where

------------------------------------------------------------------------
-- ROUND388 / DISTANCE EQUALITY IS STRONGER THAN DECAY NEEDS
--
-- Historical selected-T5 source application asks for exact same-object welds
--
--   d_source = d_physical
--   d_physical = time.
--
-- A source-native geometric decay consumer does not observe either equality.
-- For 0 <= q < 1 it needs only
--
--   time <= d_source,
--
-- because q^d_source <= q^time.  This owner isolates that weaker geometry ABI.
-- It does not manufacture the physical comparison `time <= d_source`; that is
-- still a proof-bearing same-object/support-geometry payment on the selected
-- CMP116 pair.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as Nat
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

------------------------------------------------------------------------
-- Source-independent order authority for geometric powers.
------------------------------------------------------------------------

record RationalPowerDistanceAntitone (ratio : ℚ) : Set₁ where
  field
    ratioNonnegative : 0ℚ ℚ.≤ ratio
    powerAntitone : ∀ {near far : Nat} →
      near Nat.≤ far →
      Power.rationalPower ratio far ℚ.≤ Power.rationalPower ratio near

open RationalPowerDistanceAntitone public

------------------------------------------------------------------------
-- Least-privilege selected geometric transport.
------------------------------------------------------------------------

record SourceNativeDistanceLowerData : Set₁ where
  field
    ratio amplitude response : ℚ
    time sourceDistance : Nat

    amplitudeNonnegative : 0ℚ ℚ.≤ amplitude

    -- Literal/source-localization payment before physical-time transport.
    responseBelowSourceDistance :
      response ℚ.≤ amplitude * Power.rationalPower ratio sourceDistance

    -- The only geometric information seen by the decaying consumer.
    timeBelowSourceDistance : time Nat.≤ sourceDistance

open SourceNativeDistanceLowerData public

responseBelowPhysicalTimeGeometric :
  (dataSet : SourceNativeDistanceLowerData) →
  RationalPowerDistanceAntitone (ratio dataSet) →
  response dataSet
    ℚ.≤ amplitude dataSet * Power.rationalPower (ratio dataSet) (time dataSet)
responseBelowPhysicalTimeGeometric dataSet authority =
  ℚP.≤-trans
    (responseBelowSourceDistance dataSet)
    (Norm.scaleNonnegative
      (amplitude dataSet)
      (amplitudeNonnegative dataSet)
      (powerAntitone authority (timeBelowSourceDistance dataSet)))

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round388DistanceTransportCompilerLevel : ProofLevel
round388DistanceTransportCompilerLevel = machineChecked

round388RationalPowerDistanceAntitoneLevel : ProofLevel
round388RationalPowerDistanceAntitoneLevel = standardImported

sourceDistanceEqualsPhysicalDistanceMandatory : Bool
sourceDistanceEqualsPhysicalDistanceMandatory = false

sourceDistanceEqualsPhysicalDistanceMandatoryIsFalse :
  sourceDistanceEqualsPhysicalDistanceMandatory ≡ false
sourceDistanceEqualsPhysicalDistanceMandatoryIsFalse = refl

physicalDistanceEqualsTimeMandatory : Bool
physicalDistanceEqualsTimeMandatory = false

physicalDistanceEqualsTimeMandatoryIsFalse :
  physicalDistanceEqualsTimeMandatory ≡ false
physicalDistanceEqualsTimeMandatoryIsFalse = refl

timeBelowSourceDistanceStillProofBearing : Bool
timeBelowSourceDistanceStillProofBearing = true

timeBelowSourceDistanceStillProofBearingIsTrue :
  timeBelowSourceDistanceStillProofBearing ≡ true
timeBelowSourceDistanceStillProofBearingIsTrue = refl

record Round388Boundary : Set where
  constructor round388-boundary
  field
    decayConsumerUsesOrientedDistanceOnly : Bool
    decayConsumerUsesOrientedDistanceOnlyIsTrue :
      decayConsumerUsesOrientedDistanceOnly ≡ true

    historicalExactWeldsRemainSufficient : Bool
    historicalExactWeldsRemainSufficientIsTrue :
      historicalExactWeldsRemainSufficient ≡ true

    selectedSupportGeometryStillPhysical : Bool
    selectedSupportGeometryStillPhysicalIsTrue :
      selectedSupportGeometryStillPhysical ≡ true

canonicalRound388Boundary : Round388Boundary
canonicalRound388Boundary =
  round388-boundary true refl true refl true refl

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
