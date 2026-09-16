{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R281SelectedSourceUpperRound343ValidationExact where

------------------------------------------------------------------------
-- RED / R343 Pareto contract
--
-- The mass-gap consumer does not need equality between an abstract CMP116
-- response magnitude and the selected finite response.  It only needs the
-- selected response to lie below the source-native CMP116 envelope, followed by
-- the already-separate source-envelope -> spectral-envelope calibration.
--
-- This validation root intentionally imports a production owner that does not
-- exist at the RED commit.  The production tranche must expose:
--
--   * SelectedResponseSourceUpperApplication;
--   * old R341 application -> weaker R343 application;
--   * R343 application -> the same subgap clustering upper;
--   * strict boundary booleans recording that B1 equality is not primitive;
--   * no fresh YM decay estimate and no Clay promotion.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116R281SelectedSourceUpperRound343Exact as R343

r343CompilerOwned : ProofLevel
r343CompilerOwned = R343.round343CompilerLevel

selectedResponseSourceUpperStillPhysical : ProofLevel
selectedResponseSourceUpperStillPhysical = R343.round343SelectedResponseSourceUpperLevel

sourceEnvelopeCalibrationStillPhysical : ProofLevel
sourceEnvelopeCalibrationStillPhysical = R343.round343EnvelopeCalibrationLevel

b1EqualityNotPrimitive :
  R343.sourceMagnitudeEqualityPrimitiveForMassGapConsumer ≡ false
b1EqualityNotPrimitive = refl

oldR341CompilesToWeakerR343 :
  R343.oldR341ApplicationCompilesToR343 ≡ true
oldR341CompilesToWeakerR343 = refl

r343StrictlyWeakerConsumerSurface :
  R343.r343DoesNotRecoverSourceMagnitudeEquality ≡ true
r343StrictlyWeakerConsumerSurface = refl

freshDecayEstimateNotIntroduced :
  R343.freshYMDecayEstimateIntroduced ≡ false
freshDecayEstimateNotIntroduced = refl

clayPromotionStillFalse : R343.clayPromotion ≡ false
clayPromotionStillFalse = refl
