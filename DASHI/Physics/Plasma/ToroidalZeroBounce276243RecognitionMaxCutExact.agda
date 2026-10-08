module DASHI.Physics.Plasma.ToroidalZeroBounce276243RecognitionMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ToroidalZeroBounceM24DuadRecognitionExact as Duad
import DASHI.Physics.Plasma.ToroidalZeroBouncePhaseResolvedSupportExact as Phase
import DASHI.Moonshine.OggSSP2B3BFirstUpCoefficientNoGoExact as MT
import DASHI.Moonshine.OggSSP2BM22RuntimeMaxCutReceiptExact as M22

------------------------------------------------------------------------
-- 276 / 243 RECOGNITION MAX-CUT
--
-- Repo archaeology exposes three genuinely distinct facts:
--
-- (1) magnet sparse-pair search: C(24,2)=276;
-- (2) M24 p276 is literally the Pair24/duad carrier;
-- (3) the 3B McKay--Thompson one-step coefficient magnitude is 243=3^5.
--
-- The first two share the exact combinatorial functor Pair24 after a selected
-- 24-coordinate enumeration.  The third does not thereby become a subcarrier.
-- The natural fixed-duad rank-three relation partition is 1+44+231, and the
-- true C3 phase does not preserve raw real-axis supports.
------------------------------------------------------------------------

magnetPairCount : Nat
magnetPairCount = Duad.magnetDuadCount

m24PairCount : Nat
m24PairCount = Duad.repoM24DuadCount

repoThreeB243Magnitude : Nat
repoThreeB243Magnitude = MT.p3FirstUpPositiveCoefficientMagnitude

magnetPairCountIs276 : magnetPairCount ≡ 276
magnetPairCountIs276 = refl

m24PairCountIs276 : m24PairCount ≡ 276
m24PairCountIs276 = refl

repoThreeB243MagnitudeIs243 : repoThreeB243Magnitude ≡ 243
repoThreeB243MagnitudeIs243 = refl

arithmetic243_27_6 : 243 + 27 + 6 ≡ magnetPairCount
arithmetic243_27_6 = refl

naturalDuadRankThree :
  Duad.fixedDuadSameCount +
  Duad.fixedDuadIntersectOneCount +
  Duad.fixedDuadDisjointCount ≡
  magnetPairCount
naturalDuadRankThree = Duad.rankThreeDuadPartitionCloses

------------------------------------------------------------------------
-- A second independently existing 276 decomposition comes from the runtime
-- M24-duad restriction to M22 over F2:
--
--   1^10 + 10a^5 + 10b^5 + 34^2 + 98 = 276.
--
-- It is representation-theoretic, not a magnet decomposition, and is retained
-- here specifically to prevent one favored arithmetic split from masquerading
-- as canonical merely because its terms add to 276.
------------------------------------------------------------------------

m22RestrictedDimensionStill276 :
  M22.weightedDimension M22.trivialOne
  + M22.weightedDimension M22.tenA
  + M22.weightedDimension M22.tenB
  + M22.weightedDimension M22.thirtyFour
  + M22.weightedDimension M22.ninetyEight
  ≡ 276
m22RestrictedDimensionStill276 = M22.runtimeRestrictedDimensionCloses276

record Candidate243_27_6ActionRecognition : Set₁ where
  constructor candidate-243-27-6-action-recognition
  field
    PairCarrier : Set
    Core243 Boundary27 Orientation6 : Set
    exhaustiveDisjointPartitionReceipt : Set
    physicalC3ActionReceipt : Set
    inversePhaseActionReceipt : Set
    partitionInvariantUnderActionReceipt : Set
    sameObjectRecoveryReceipt : Set
    pairIncidenceKernelCompatibilityReceipt : Set
    recognitionReference : String

open Candidate243_27_6ActionRecognition public

record RecognitionMaxCutBoundary : Set where
  constructor recognition-max-cut-boundary
  field
    pair24CarrierShapePaid : Bool
    pair24CarrierShapePaidIsTrue :
      pair24CarrierShapePaid ≡ true

    physicalM24ActionOnMagnetCoordinatesPaid : Bool
    physicalM24ActionOnMagnetCoordinatesPaidIsFalse :
      physicalM24ActionOnMagnetCoordinatesPaid ≡ false

    rawRealAxis276IsC3Stable : Bool
    rawRealAxis276IsC3StableIsFalse :
      rawRealAxis276IsC3Stable ≡ false

    phaseResolvedSupportCarrierAvailable : Bool
    phaseResolvedSupportCarrierAvailableIsTrue :
      phaseResolvedSupportCarrierAvailable ≡ true

    canonical243_27_6PartitionPaid : Bool
    canonical243_27_6PartitionPaidIsFalse :
      canonical243_27_6PartitionPaid ≡ false

    arithmeticCoincidencePromotesMoonshineOrMonsterSemantics : Bool
    arithmeticCoincidencePromotesMoonshineOrMonsterSemanticsIsFalse :
      arithmeticCoincidencePromotesMoonshineOrMonsterSemantics ≡ false

canonicalRecognitionMaxCutBoundary : RecognitionMaxCutBoundary
canonicalRecognitionMaxCutBoundary =
  recognition-max-cut-boundary
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl

nextRecognitionTarget : String
nextRecognitionTarget =
  "Search on phase-stable harmonic subspaces / projective phase lines, not raw real-axis supports; promote 243+27+6 only after an exhaustive action-invariant partition and pair-kernel intertwiner are constructed."
