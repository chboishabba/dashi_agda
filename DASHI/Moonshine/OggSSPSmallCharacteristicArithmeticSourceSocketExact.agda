module DASHI.Moonshine.OggSSPSmallCharacteristicArithmeticSourceSocketExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC ARITHMETIC SOURCE SOCKETS
--
-- After the coarse-j no-go, the missing arithmetic source must be a marked or
-- enriched cover over the unique supersingular j-class.
--
-- p=3 calibration:
--   existing receipt records F9/F3 with Frobenius group Z/2 (order two).
--   This module therefore asks for an ACTUAL involutive marked-state action,
--   not merely the string/number receipt.
--
-- p=2 calibration:
--   existing source surface records the unique coarse supersingular j-class
--   and a j=1728 / Gaussian-CM context.  The source socket again asks for an
--   actual marked state carrier and action.
--
-- No socket is inhabited here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Core.ResidualSymmetryCollisionFibreExact as Action
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit
import DASHI.Foundations.BalancedTernaryOrbitStabilizerResidualBridgeExact as C2
import DASHI.Physics.Moonshine.SupersingularPrimeLaneBridge as SSPAuthority
import DASHI.Physics.Closure.IsospinSplittingFromP3LaneReceipt as P3Receipt
import DASHI.Physics.Closure.P2LaneInnerProductProof as P2Receipt
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Source
import DASHI.Moonshine.OggSSPP3F9FrobeniusCandidateNoGoExact as F9NoGo
import DASHI.Moonshine.OggSSPP2F4FrobeniusCandidateNoGoExact as F4NoGo
import DASHI.Moonshine.OggSSPSmallCharacteristicCodecIndexedRecognitionExact as LaneCodec

------------------------------------------------------------------------
-- 1. Source calibration inherited from existing authority/receipt owners.
------------------------------------------------------------------------

p2UniqueCoarseSupersingularJ :
  SSPAuthority.supersingularJInvariantCountBound SSPAuthority.p2 ≡ 1
p2UniqueCoarseSupersingularJ =
  SSPAuthority.p2UniqueSupersingularCurve

p3UniqueCoarseSupersingularJ :
  SSPAuthority.supersingularJInvariantCountBound SSPAuthority.p3 ≡ 1
p3UniqueCoarseSupersingularJ =
  SSPAuthority.p3UniqueSupersingularCurve

p3ReceiptFrobeniusOrderTwo :
  P3Receipt.frobeniusOrder
    P3Receipt.canonicalIsospinSplittingFromP3LaneReceipt
  ≡ 2
p3ReceiptFrobeniusOrderTwo =
  P3Receipt.frobeniusOrderIsZ2
    P3Receipt.canonicalIsospinSplittingFromP3LaneReceipt

p2ExactLaneKey : LaneCodec.ExactOggLaneKey
p2ExactLaneKey = LaneCodec.p2LaneKey

p3ExactLaneKey : LaneCodec.ExactOggLaneKey
p3ExactLaneKey = LaneCodec.p3LaneKey

sourceSocketClaimOrigin : Source.ClaimOrigin
sourceSocketClaimOrigin = Source.repositoryNewExtension

------------------------------------------------------------------------
-- 2. p=3 marked Frobenius source socket.
--
-- We deliberately use the repo's canonical C2 carrier only as the required
-- action SHAPE.  An inhabitant must still prove that its flip is the actual
-- arithmetic Frobenius action on its marked states.
------------------------------------------------------------------------

record P3MarkedFrobeniusSource : Set₁ where
  field
    MarkedState : Set

    action :
      Action.InvertibleSymmetryAction MarkedState C2.C2

    candidateOrbits :
      Orbit.OrbitPresentation action

    coarseJ :
      MarkedState → ⊤

    coarseJConstant :
      (state : MarkedState) →
      coarseJ state ≡ tt

    markedWitness : MarkedState

    frobeniusMovesMarkedWitness :
      Action.act action C2.flip markedWitness ≡ markedWitness → ⊥

    flipIsArithmeticFrobenius : Bool
    flipIsArithmeticFrobeniusIsTrue :
      flipIsArithmeticFrobenius ≡ true

open P3MarkedFrobeniusSource public

------------------------------------------------------------------------
-- 3. p=2 marked source socket.
--
-- We do not assume the arithmetic symmetry is C2.  The recognition functor is
-- responsible for mapping whatever source symmetry is actually justified into
-- the retained-orientation target.
------------------------------------------------------------------------

record P2MarkedArithmeticSource : Set₁ where
  field
    MarkedState : Set
    Symmetry : Set

    action :
      Action.InvertibleSymmetryAction MarkedState Symmetry

    orbits :
      Orbit.OrbitPresentation action

    coarseJ :
      MarkedState → ⊤

    coarseJConstant :
      (state : MarkedState) →
      coarseJ state ≡ tt

    markedResidualStructurePresent : Bool
    markedResidualStructurePresentIsTrue :
      markedResidualStructurePresent ≡ true

open P2MarkedArithmeticSource public

------------------------------------------------------------------------
-- 3b. Sharpened p=2 marked Gaussian-CM / level-4 source socket.
--
-- The existing p=2 receipt supplies calibration only:
--   F4/F2, Frobenius C2, j=1728, End(E)=Z[i], conductor/level 4.
--
-- A theorem-bearing arithmetic source must additionally provide an actual
-- marked state carrier, action and orbit presentation, and must retain the CM
-- level/provenance rather than reconstructing it from a coarse state label.
------------------------------------------------------------------------

data P2CMProvenance : Set where
  gaussianCMJ1728LevelFour : P2CMProvenance

record P2MarkedLevelCMSource : Set₁ where
  field
    baseSource :
      P2MarkedArithmeticSource

    cmProvenance :
      P2MarkedArithmeticSource.MarkedState baseSource ->
      P2CMProvenance

    cmProvenanceConstant :
      (state : P2MarkedArithmeticSource.MarkedState baseSource) ->
      cmProvenance state ≡ gaussianCMJ1728LevelFour

    receiptF4F2Calibration :
      P2Receipt.extensionFieldCardinality
        P2Receipt.canonicalP2LaneInnerProductProofReceipt
      ≡ 4

    receiptFrobeniusC2Calibration :
      P2Receipt.galF4F2IdentifiedWithC2
        P2Receipt.canonicalP2LaneInnerProductProofReceipt
      ≡ true

    receiptGaussianCMLevelFourCalibration :
      P2Receipt.cmConductorLevel
        P2Receipt.canonicalP2LaneInnerProductProofReceipt
      ≡ 4

    actualMarkedLevelCMCarrierSupplied : Bool
    actualMarkedLevelCMCarrierSuppliedIsTrue :
      actualMarkedLevelCMCarrierSupplied ≡ true

open P2MarkedLevelCMSource public

data P2ReceiptLabelsConstructMarkedLevelCMSource : Set where

p2ReceiptLabelsDoNotConstructMarkedLevelCMSource :
  P2ReceiptLabelsConstructMarkedLevelCMSource -> ⊥
p2ReceiptLabelsDoNotConstructMarkedLevelCMSource ()

------------------------------------------------------------------------
-- 4. Receipt firewall.
------------------------------------------------------------------------

data P3OrderTwoReceiptConstructsMarkedFrobeniusAction : Set where
data UniqueCoarseJConstructsMarkedResidualCover : Set where

p3OrderTwoReceiptDoesNotConstructMarkedAction :
  P3OrderTwoReceiptConstructsMarkedFrobeniusAction → ⊥
p3OrderTwoReceiptDoesNotConstructMarkedAction ()

uniqueCoarseJDoesNotConstructMarkedResidualCover :
  UniqueCoarseJConstructsMarkedResidualCover → ⊥
uniqueCoarseJDoesNotConstructMarkedResidualCover ()

------------------------------------------------------------------------
-- 5. Frontier.
------------------------------------------------------------------------

data SmallCharacteristicArithmeticSourceResidual : Set where
  missingP2MarkedArithmeticSource :
    SmallCharacteristicArithmeticSourceResidual
  missingP3MarkedFrobeniusQuotientOrSubcarrier :
    SmallCharacteristicArithmeticSourceResidual

record SmallCharacteristicArithmeticSourceBoundary : Set where
  constructor small-characteristic-arithmetic-source-boundary
  field
    p2UniqueCoarseJConsumed : Bool
    p3UniqueCoarseJConsumed : Bool
    p3FrobeniusOrderTwoReceiptConsumed : Bool
    p2ExactLaneKeyOwned : Bool
    p3ExactLaneKeyOwned : Bool
    p3MarkedActionSocketOwned : Bool
    p2MarkedActionSocketOwned : Bool
    wholeF9FrobeniusCarrierRejected : Bool
    p3MarkedQuotientOrSubcarrierRequired : Bool
    rawF4FrobeniusCarrierHasThreeOrbitDiagnostic : Bool
    rawF4InsufficientForTenComponentRetainedTarget : Bool
    p2MarkedLevelCMCoverRequired : Bool
    p2MarkedLevelCMSourceSocketOwned : Bool
    receiptMetadataPromotedToAction : Bool
    p2SourceInhabited : Bool
    p3SourceInhabited : Bool
    firstResidual : SmallCharacteristicArithmeticSourceResidual

canonicalSmallCharacteristicArithmeticSourceBoundary :
  SmallCharacteristicArithmeticSourceBoundary
canonicalSmallCharacteristicArithmeticSourceBoundary =
  small-characteristic-arithmetic-source-boundary
    true true true true true true true
    true true
    true true true true
    false false false
    missingP2MarkedArithmeticSource
