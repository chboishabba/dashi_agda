module DASHI.Moonshine.JInvariant369CodecReconciliationFrontierExact where

------------------------------------------------------------------------
-- J-INVARIANT 369 CODEC RECONCILIATION FRONTIER
--
-- Current branch owns a total fixed-width codec for all nine two-trit states.
-- Newer repository work (on master) owns a denser 3-bit <-> 2-trit codec on
-- the eight NON-CENTRE states, with the ternary centre deliberately unused.
--
-- This adapter does not duplicate that newer codec.  It classifies exactly
-- which j-observer nine-sheet states are eligible for that subcodec once the
-- branch is reconciled, and keeps the centre as an explicit escape/residual.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_,_)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Moonshine.JInvariant369CodecBidiExact as Total

------------------------------------------------------------------------
-- 1. Exact centre/non-centre classifier on the existing nine-sheet carrier.
------------------------------------------------------------------------

centreNine : Triadic.NineSheet
centreNine = Triadic.zeroTrit , Triadic.zeroTrit

data AntipodalSubcodecEligibility : Set where
  centreRequiresEscape : AntipodalSubcodecEligibility
  nonCentreEligible : AntipodalSubcodecEligibility

threeBitEligibility : Triadic.NineSheet → AntipodalSubcodecEligibility
threeBitEligibility (Triadic.zeroTrit , Triadic.zeroTrit) = centreRequiresEscape
threeBitEligibility _ = nonCentreEligible

centreIsNotThreeBitPayload :
  threeBitEligibility centreNine ≡ centreRequiresEscape
centreIsNotThreeBitPayload = refl

negativeNegativeEligible :
  threeBitEligibility (Triadic.negativeTrit , Triadic.negativeTrit)
  ≡ nonCentreEligible
negativeNegativeEligible = refl

positivePositiveEligible :
  threeBitEligibility (Triadic.positiveTrit , Triadic.positiveTrit)
  ≡ nonCentreEligible
positivePositiveEligible = refl

------------------------------------------------------------------------
-- 2. Total baseline remains total for the centre.
------------------------------------------------------------------------

centreTotalCode : Total.NineCode
centreTotalCode = Total.encodeNine centreNine

centreTotalRoundtrip :
  Total.decodeNine centreTotalCode ≡ just centreNine
centreTotalRoundtrip = Total.decodeEncodeNine centreNine

------------------------------------------------------------------------
-- 3. 27-state third coordinate is available, but its semantics are not free.
--
-- Newer CS work uses a third trit as an explicit framing/residual coordinate.
-- The j observer also has three coordinates.  Cardinality alone does not allow
-- us to identify Fabric.z with that framing coordinate.
------------------------------------------------------------------------

thirdCoordinate : Fabric.Ternary27Point → SSP.SSPTrit
thirdCoordinate = Fabric.z

data NeutralThirdCoordinate : Fabric.Ternary27Point → Set where
  neutral-third :
    {x y : SSP.SSPTrit} →
    NeutralThirdCoordinate
      (Fabric.ternary27Point x y SSP.sspZero)

originHasNeutralThirdCoordinate :
  NeutralThirdCoordinate Fabric.origin
originHasNeutralThirdCoordinate = neutral-third

record J27FrameSemanticBridge : Set₁ where
  field
    FrameMeaning : Set
    frameOfObserver : Fabric.Ternary27Point → FrameMeaning
    neutralFrameMeaning : FrameMeaning
    neutralThirdImpliesNeutralFrame :
      (p : Fabric.Ternary27Point) →
      NeutralThirdCoordinate p →
      frameOfObserver p ≡ neutralFrameMeaning

------------------------------------------------------------------------
-- 4. Reconciliation boundary.
------------------------------------------------------------------------

record JInvariant369CodecReconciliationBoundary : Set where
  constructor j-invariant-369-codec-reconciliation-boundary
  field
    currentNineCodecTotal : Bool
    threeBitCodecCanCoverAllNineWithoutEscape : Bool
    centreRequiresSeparateRepresentation : Bool
    nonCentreAntipodalSubcodecIsPromising : Bool
    twentySevenThirdCoordinateAvailable : Bool
    thirdCoordinateAutomaticallyMeansCSFrame : Bool
    branchReconciliationRequiredForNewerCodecOwner : Bool
    analyticJPayloadStillOutsideFiniteCodec : Bool

canonicalJInvariant369CodecReconciliationBoundary :
  JInvariant369CodecReconciliationBoundary
canonicalJInvariant369CodecReconciliationBoundary =
  j-invariant-369-codec-reconciliation-boundary
    true false true true true false true true
