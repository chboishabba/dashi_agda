module DASHI.Physics.Plasma.ToroidalZeroBounceM24DuadRecognitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.OggSSP2BM24DuadPair24AuthorityExact as M24Duad

------------------------------------------------------------------------
-- MAGNET SUPPORT PAIRS AS A 24-POINT DUAD CARRIER
--
-- The current Ternary-27 search chart pins three constant/gauge coordinates,
-- leaving 24 free real coordinates.  Its unordered two-coordinate support
-- carrier therefore has C(24,2)=276 states.
--
-- Independently, the repository already owns the source-backed theorem that
-- the ATLAS degree-276 M24 carrier is the natural duad / unordered two-subset
-- action on 24 points.  This pays a canonical COMBINATORIAL carrier shape for
-- the magnet pair search after a selected 24-coordinate enumeration.
--
-- It does not give the magnet coordinates an M24 physical action.  Action-level
-- recognition requires an explicit coordinate-action intertwiner.
------------------------------------------------------------------------

magnetFreeCoordinateCount : Nat
magnetFreeCoordinateCount = 24

magnetDuadCount : Nat
magnetDuadCount = 276

orderedDistinctCoordinatePairCount : Nat
orderedDistinctCoordinatePairCount = 24 * 23

orderedPairsAreTwiceMagnetDuads :
  orderedDistinctCoordinatePairCount ≡ 2 * magnetDuadCount
orderedPairsAreTwiceMagnetDuads = refl

repoM24DuadCount : Nat
repoM24DuadCount = M24Duad.duadCount

repoM24DuadCountMatchesMagnetPairCount :
  repoM24DuadCount ≡ magnetDuadCount
repoM24DuadCountMatchesMagnetPairCount = refl

------------------------------------------------------------------------
-- Rank-three relation classes around one fixed duad.
--
-- In the natural 24-point two-subset action a fixed duad sees:
--   1   identical duad,
--   44  duads meeting it in one point = 2*22,
--   231 disjoint duads = C(22,2).
-- This is the natural rank-three relation partition; it is not 243+27+6.
------------------------------------------------------------------------

fixedDuadSameCount : Nat
fixedDuadSameCount = 1

fixedDuadIntersectOneCount : Nat
fixedDuadIntersectOneCount = 44

fixedDuadDisjointCount : Nat
fixedDuadDisjointCount = 231

rankThreeDuadPartitionCloses :
  fixedDuadSameCount + fixedDuadIntersectOneCount + fixedDuadDisjointCount ≡
  magnetDuadCount
rankThreeDuadPartitionCloses = refl

candidate243Count candidate27Count candidate6Count : Nat
candidate243Count = 243
candidate27Count = 27
candidate6Count = 6

candidate243_27_6ArithmeticCloses :
  candidate243Count + candidate27Count + candidate6Count ≡ magnetDuadCount
candidate243_27_6ArithmeticCloses = refl

record SelectedMagnetToM24DuadCarrierChart : Set₁ where
  constructor selected-magnet-to-m24-duad-carrier-chart
  field
    MagnetCoordinate24 : Set
    M24Point24 : Set
    magnetToM24Point : MagnetCoordinate24 → M24Point24
    m24PointToMagnet : M24Point24 → MagnetCoordinate24
    recoverMagnetPoint :
      ∀ x → m24PointToMagnet (magnetToM24Point x) ≡ x
    recoverM24Point :
      ∀ x → magnetToM24Point (m24PointToMagnet x) ≡ x
    selectedEnumerationReceipt : Set
    unorderedPairLiftReceipt : Set
    chartReference : String

open SelectedMagnetToM24DuadCarrierChart public

record MagnetM24ActionRecognition
    (chart : SelectedMagnetToM24DuadCarrierChart) : Set₁ where
  constructor magnet-m24-action-recognition
  field
    MagnetSymmetry : Set
    M24Symmetry : Set
    mapSymmetry : MagnetSymmetry → M24Symmetry
    coordinateActionIntertwiningReceipt : Set
    duadActionIntertwiningReceipt : Set
    orbitRecoveryReceipt : Set
    stabilizerRecoveryReceipt : Set
    recognitionReference : String

open MagnetM24ActionRecognition public

record M24DuadRecognitionBoundary : Set where
  constructor m24-duad-recognition-boundary
  field
    pair24CombinatorialCarrierAvailable : Bool
    pair24CombinatorialCarrierAvailableIsTrue :
      pair24CombinatorialCarrierAvailable ≡ true

    sameCardinalityAloneCreatesM24Action : Bool
    sameCardinalityAloneCreatesM24ActionIsFalse :
      sameCardinalityAloneCreatesM24Action ≡ false

    selectedPair24ChartCreatesPhysicalM24Symmetry : Bool
    selectedPair24ChartCreatesPhysicalM24SymmetryIsFalse :
      selectedPair24ChartCreatesPhysicalM24Symmetry ≡ false

    naturalRankThreePartitionIs243_27_6 : Bool
    naturalRankThreePartitionIs243_27_6IsFalse :
      naturalRankThreePartitionIs243_27_6 ≡ false

    actionIntertwinerStillRequired : Bool
    actionIntertwinerStillRequiredIsTrue :
      actionIntertwinerStillRequired ≡ true

canonicalM24DuadRecognitionBoundary : M24DuadRecognitionBoundary
canonicalM24DuadRecognitionBoundary =
  m24-duad-recognition-boundary
    true refl
    false refl
    false refl
    false refl
    true refl

pythonReplayReference : String
pythonReplayReference =
  "scripts/magnet_duad_recognition_probe.py::duads/rank3_orbit_sizes; repository authority: OggSSP2BM24DuadPair24AuthorityExact."
