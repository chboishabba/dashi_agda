module DASHI.Geometry.MobiusOrientationGate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Mobius orientation gate.
--
-- This module is a candidate-only receipt surface for local-vs-global
-- orientation transport on a Mobius band.  It records the order-2 flip
-- target after one loop, the orientability=false gate, and the fact that
-- no promotion is manufactured here.

data MobiusOrientationGateStatus : Set where
  mobiusOrientationTargetsOnlyNoPromotion :
    MobiusOrientationGateStatus

data MobiusOrientationGateOpenObligation : Set where
  missingLocalOrientationCarrier :
    MobiusOrientationGateOpenObligation

  missingGlobalOrientationCarrier :
    MobiusOrientationGateOpenObligation

  missingOneLoopFlipTransportCertificate :
    MobiusOrientationGateOpenObligation

  missingTwoLoopReturnCertificate :
    MobiusOrientationGateOpenObligation

  missingOrientabilityGate :
    MobiusOrientationGateOpenObligation

  missingPromotionAuthorityBoundary :
    MobiusOrientationGateOpenObligation

canonicalMobiusOrientationGateOpenObligations :
  List MobiusOrientationGateOpenObligation
canonicalMobiusOrientationGateOpenObligations =
  missingLocalOrientationCarrier
  ∷ missingGlobalOrientationCarrier
  ∷ missingOneLoopFlipTransportCertificate
  ∷ missingTwoLoopReturnCertificate
  ∷ missingOrientabilityGate
  ∷ missingPromotionAuthorityBoundary
  ∷ []

data MobiusOrientationTarget : Set where
  localVsGlobalOrientationTransportTarget :
    MobiusOrientationTarget

  oneLoopOrderTwoFlipTarget :
    MobiusOrientationTarget

  orientabilityFalseGateTarget :
    MobiusOrientationTarget

canonicalMobiusOrientationTargets :
  List MobiusOrientationTarget
canonicalMobiusOrientationTargets =
  localVsGlobalOrientationTransportTarget
  ∷ oneLoopOrderTwoFlipTarget
  ∷ orientabilityFalseGateTarget
  ∷ []

data MobiusOrientationPromotionAuthorityToken : Set where

record MobiusLocalGlobalOrientationSurface : Set where
  field
    localOrientationCarrier :
      String

    globalOrientationCarrier :
      String

    transportCarrier :
      String

    oneLoopFlipOrder :
      Nat

    oneLoopFlipOrder-v :
      oneLoopFlipOrder ≡ 2

    oneLoopFlipTargetName :
      String

    oneLoopFlipTargetName-v :
      oneLoopFlipTargetName
      ≡
      "target-only-mobius-band-one-loop-order-two-flip"

    orientabilityGate :
      Bool

    orientabilityGateIsFalse :
      orientabilityGate ≡ false

    transportPromoted :
      Bool

    transportPromotedIsFalse :
      transportPromoted ≡ false

    authorityBoundary :
      String

    receiptBoundary :
      List String

open MobiusLocalGlobalOrientationSurface public

canonicalMobiusLocalGlobalOrientationSurface :
  MobiusLocalGlobalOrientationSurface
canonicalMobiusLocalGlobalOrientationSurface =
  record
    { localOrientationCarrier =
        "local strip orientation carrier"
    ; globalOrientationCarrier =
        "global once-around transport carrier"
    ; transportCarrier =
        "orientation transport flip carrier"
    ; oneLoopFlipOrder =
        2
    ; oneLoopFlipOrder-v =
        refl
    ; oneLoopFlipTargetName =
        "target-only-mobius-band-one-loop-order-two-flip"
    ; oneLoopFlipTargetName-v =
        refl
    ; orientabilityGate =
        false
    ; orientabilityGateIsFalse =
        refl
    ; transportPromoted =
        false
    ; transportPromotedIsFalse =
        refl
    ; authorityBoundary =
        "no ordinary global orientability promotion is manufactured here"
    ; receiptBoundary =
        "Local and global orientation carriers are named but not promoted"
        ∷ "A one-loop transport flip is recorded as order 2"
        ∷ "Orientability stays gated false"
        ∷ "No promotion authority is manufactured in this candidate-only receipt"
        ∷ []
    }

canonicalMobiusOrientationGateStatus :
  MobiusOrientationGateStatus
canonicalMobiusOrientationGateStatus =
  mobiusOrientationTargetsOnlyNoPromotion

mobiusOrderTwoFlip :
  Nat
mobiusOrderTwoFlip =
  oneLoopFlipOrder canonicalMobiusLocalGlobalOrientationSurface

mobiusOrderTwoFlipIsTwo :
  mobiusOrderTwoFlip ≡ 2
mobiusOrderTwoFlipIsTwo =
  oneLoopFlipOrder-v canonicalMobiusLocalGlobalOrientationSurface

mobiusOrientabilityGateIsFalse :
  orientabilityGate canonicalMobiusLocalGlobalOrientationSurface ≡ false
mobiusOrientabilityGateIsFalse =
  orientabilityGateIsFalse canonicalMobiusLocalGlobalOrientationSurface

mobiusTransportPromotedIsFalse :
  transportPromoted canonicalMobiusLocalGlobalOrientationSurface ≡ false
mobiusTransportPromotedIsFalse =
  transportPromotedIsFalse canonicalMobiusLocalGlobalOrientationSurface
