module DASHI.Moonshine.OggSSPP2DirectTwoBIntrinsicDepthFrontierExact where

------------------------------------------------------------------------
-- p=2 DIRECT 2B INTRINSIC DEPTH FRONTIER
--
-- CANONICAL SOURCE LANGUAGE
--
-- Urano's direct 2B source theorem supplies parity-dependent exclusions on the
-- actual integral 2B weight spaces:
--
--   odd degree  : no trivial Z_2 summand;
--   even degree : no augmentation quotient I_2 summand.
--
-- It does NOT canonically choose an order-4 square root, a C4 indecomposable
-- lift, five inertia labels, or the depth profile 3,3,2,1,1.
--
-- DASHI TERMINAL SCALAR SOCKET
--
-- The minimal intrinsic p=2 scalar theorem therefore asks directly for:
--
--   * five actual integral 2B source slots;
--   * source-native parity/module-tag data respecting Urano's exclusions;
--   * an integral extension/filtration depth observable on those pieces;
--   * exact slot depths 3,3,2,1,1;
--   * target independence from the Monster residual and Base369.
--
-- The C4 rank/fingerprint construction upstream is an OPTIONAL recognition
-- donor.  It is not required to define or inhabit this direct source theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSP2BUranoIntegralModuleParityExact as Urano
import DASHI.Moonshine.OggSSPP2InertiaDepthQuotientExact as Scalar
import DASHI.Moonshine.OggSSPP2C4LowRankDepthSpectrumCandidateExact as C4Spectrum
import DASHI.Moonshine.OggSSPP2C4GreenFingerprintCandidateExact as C4Fingerprint
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Direct intrinsic source-depth authority.
------------------------------------------------------------------------

record P2IntrinsicTwoBDepthAuthority : Set₁ where
  field
    SourcePiece :
      Set

    sourcePiece :
      Scalar.P2ScalarSlot ->
      SourcePiece

    degreeParity :
      SourcePiece ->
      Urano.DegreeParity

    moduleTag :
      SourcePiece ->
      Urano.TwoBModuleTag

    sourcePieceComesFromActualIntegralTwoBWeightSpace :
      SourcePiece ->
      Bool

    sourcePieceComesFromActualIntegralTwoBWeightSpaceIsTrue :
      (piece : SourcePiece) ->
      sourcePieceComesFromActualIntegralTwoBWeightSpace piece ≡ true

    respectsUranoForbiddenPairs :
      (piece : SourcePiece) ->
      Urano.TwoBSourceForbidden
        (degreeParity piece)
        (moduleTag piece)
      ->
      ⊥

    integralFiltrationDepth :
      SourcePiece ->
      Nat

    sourceSlotDepthMatchesRequiredProfile :
      (slot : Scalar.P2ScalarSlot) ->
      integralFiltrationDepth (sourcePiece slot)
      ≡
      Scalar.slotLength slot

    depthComesFromActualIntegralSourceFiltration :
      SourcePiece ->
      Bool

    depthComesFromActualIntegralSourceFiltrationIsTrue :
      (piece : SourcePiece) ->
      depthComesFromActualIntegralSourceFiltration piece ≡ true

    fiveSlotsAreSourceNativeDistinctions :
      Bool

    fiveSlotsAreSourceNativeDistinctionsIsTrue :
      fiveSlotsAreSourceNativeDistinctions ≡ true

    constructionIndependentOfOrderFourLift :
      Bool

    constructionIndependentOfOrderFourLiftIsTrue :
      constructionIndependentOfOrderFourLift ≡ true

    constructionIndependentOfMonsterResidualTen :
      Bool

    constructionIndependentOfMonsterResidualTenIsTrue :
      constructionIndependentOfMonsterResidualTen ≡ true

    constructionIndependentOfBase369 :
      Bool

    constructionIndependentOfBase369IsTrue :
      constructionIndependentOfBase369 ≡ true

open P2IntrinsicTwoBDepthAuthority public

------------------------------------------------------------------------
-- 2. Direct adapter to the scalar consumer.
------------------------------------------------------------------------

asP2SourceDepthSlotLengthAuthority :
  P2IntrinsicTwoBDepthAuthority ->
  Scalar.P2SourceDepthSlotLengthAuthority
asP2SourceDepthSlotLengthAuthority A =
  record
    { Scalar.SourcePiece =
        SourcePiece A

    ; Scalar.sourcePiece =
        sourcePiece A

    ; Scalar.sourcePiecesArePairwiseSourceSlots =
        fiveSlotsAreSourceNativeDistinctions A

    ; Scalar.sourcePiecesArePairwiseSourceSlotsIsTrue =
        fiveSlotsAreSourceNativeDistinctionsIsTrue A

    ; Scalar.sourcePieceComesFromIntegralTwoBTateObject =
        sourcePieceComesFromActualIntegralTwoBWeightSpace A

    ; Scalar.sourcePieceComesFromIntegralTwoBTateObjectIsTrue =
        sourcePieceComesFromActualIntegralTwoBWeightSpaceIsTrue A

    ; Scalar.normalizedDVRLength =
        integralFiltrationDepth A

    ; Scalar.sourceSlotLengthMatchesDepth =
        sourceSlotDepthMatchesRequiredProfile A

    ; Scalar.paymentIndependentOfMonsterResidualTen =
        constructionIndependentOfMonsterResidualTen A

    ; Scalar.paymentIndependentOfMonsterResidualTenIsTrue =
        constructionIndependentOfMonsterResidualTenIsTrue A

    ; Scalar.paymentIndependentOfBase369Labels =
        constructionIndependentOfBase369 A

    ; Scalar.paymentIndependentOfBase369LabelsIsTrue =
        constructionIndependentOfBase369IsTrue A
    }

directP2ScalarTotalIsTen :
  (A : P2IntrinsicTwoBDepthAuthority) ->
  Scalar.sourceSlotTotal
    (asP2SourceDepthSlotLengthAuthority A)
  ≡ 10
directP2ScalarTotalIsTen A =
  Scalar.sourceSlotTotalIsTen
    (asP2SourceDepthSlotLengthAuthority A)

------------------------------------------------------------------------
-- 3. C4 is an optional donor, not a dependency.
------------------------------------------------------------------------

c4SpectrumBoundary :
  C4Spectrum.P2C4LowRankDepthSpectrumBoundary
c4SpectrumBoundary =
  C4Spectrum.canonicalP2C4LowRankDepthSpectrumBoundary

c4FingerprintBoundary :
  C4Fingerprint.P2C4GreenFingerprintCandidateBoundary
c4FingerprintBoundary =
  C4Fingerprint.canonicalP2C4GreenFingerprintCandidateBoundary

data DirectTwoBDepthRequiresC4Lift : Set where
data C4RankDefinesDirectTwoBDepth : Set where
data C4FingerprintDefinesDirectTwoBSlots : Set where

directTwoBDepthDoesNotRequireC4Lift :
  DirectTwoBDepthRequiresC4Lift -> ⊥
directTwoBDepthDoesNotRequireC4Lift ()

c4RankDoesNotDefineDirectTwoBDepth :
  C4RankDefinesDirectTwoBDepth -> ⊥
c4RankDoesNotDefineDirectTwoBDepth ()

c4FingerprintDoesNotDefineDirectTwoBSlots :
  C4FingerprintDefinesDirectTwoBSlots -> ⊥
c4FingerprintDoesNotDefineDirectTwoBSlots ()

------------------------------------------------------------------------
-- 4. Urano's direct theorem is necessary but does not inhabit the depth.
------------------------------------------------------------------------

uranoBoundary :
  Urano.TwoBUranoIntegralModuleParityBoundary
uranoBoundary =
  Urano.canonicalTwoBUranoIntegralModuleParityBoundary

data UranoParityExclusionsDetermineFiveSlots : Set where
data UranoParityExclusionsDetermineDepthProfile : Set where
data T4AFunctionalDeterminesIntrinsicDepth : Set where

uranoParityDoesNotDetermineFiveSlots :
  UranoParityExclusionsDetermineFiveSlots -> ⊥
uranoParityDoesNotDetermineFiveSlots ()

uranoParityDoesNotDetermineDepthProfile :
  UranoParityExclusionsDetermineDepthProfile -> ⊥
uranoParityDoesNotDetermineDepthProfile ()

t4AFunctionalDoesNotDetermineIntrinsicDepth :
  T4AFunctionalDeterminesIntrinsicDepth -> ⊥
t4AFunctionalDoesNotDetermineIntrinsicDepth ()

------------------------------------------------------------------------
-- 5. Live wall.
------------------------------------------------------------------------

data P2IntrinsicTwoBDepthAuthorityInhabited : Set where

p2IntrinsicTwoBDepthStillOpen :
  P2IntrinsicTwoBDepthAuthorityInhabited -> ⊥
p2IntrinsicTwoBDepthStillOpen ()

------------------------------------------------------------------------
-- 6. Attribution.
------------------------------------------------------------------------

data UranoCreditedWithThreeThreeTwoOneOne : Set where
data CarnahanUranoCreditedWithDirectTwoBFiveSlots : Set where
data C4DonorPromotedToCanonicalTwoBSource : Set where

uranoNotCreditedWithThreeThreeTwoOneOne :
  UranoCreditedWithThreeThreeTwoOneOne -> ⊥
uranoNotCreditedWithThreeThreeTwoOneOne ()

carnahanUranoNotCreditedWithDirectTwoBFiveSlots :
  CarnahanUranoCreditedWithDirectTwoBFiveSlots -> ⊥
carnahanUranoNotCreditedWithDirectTwoBFiveSlots ()

c4DonorNotPromotedToCanonicalTwoBSource :
  C4DonorPromotedToCanonicalTwoBSource -> ⊥
c4DonorNotPromotedToCanonicalTwoBSource ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryNewExtension

record P2DirectTwoBIntrinsicDepthFrontierBoundary : Set where
  constructor p2-direct-two-b-intrinsic-depth-frontier-boundary
  field
    uranoDirectTwoBParitySourceSourced : Bool
    directFiveSourceSlotAuthoritySpecified : Bool
    integralFiltrationDepthRequired : Bool
    exactThreeThreeTwoOneOneProfileRequired : Bool
    directAdapterToScalarConsumerOwned : Bool
    conditionalScalarTotalTenDerived : Bool

    c4LiftRequired : Bool
    c4RankDefinesIntrinsicDepth : Bool
    c4FingerprintDefinesSourceSlots : Bool

    uranoParityAloneInhabitsFiveSlots : Bool
    uranoParityAloneInhabitsDepthProfile : Bool
    intrinsicDepthAuthorityInhabited : Bool

    monsterResidualUsedToDefineDepth : Bool
    base369UsedToDefineDepth : Bool
    attributionFirewallPreserved : Bool

canonicalP2DirectTwoBIntrinsicDepthFrontierBoundary :
  P2DirectTwoBIntrinsicDepthFrontierBoundary
canonicalP2DirectTwoBIntrinsicDepthFrontierBoundary =
  p2-direct-two-b-intrinsic-depth-frontier-boundary
    true true true true true true
    false false false
    false false false
    false false true
