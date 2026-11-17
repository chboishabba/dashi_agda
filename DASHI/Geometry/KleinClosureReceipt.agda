module DASHI.Geometry.KleinClosureReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Geometry.MobiusOrientationGate as MOG

------------------------------------------------------------------------
-- Klein bottle closure receipt.
--
-- This module is a candidate-only receipt surface for the closure of two
-- Mobius bands into a closed non-orientable surface.  It names the two-band
-- gluing target, records the non-orientability and global inside/outside
-- collapse as explicit false gates, and does not manufacture promotion.

data KleinClosureReceiptStatus : Set where
  kleinClosureTargetsOnlyNoPromotion :
    KleinClosureReceiptStatus

data KleinClosureOpenObligation : Set where
  missingFirstMobiusBandCarrier :
    KleinClosureOpenObligation

  missingSecondMobiusBandCarrier :
    KleinClosureOpenObligation

  missingClosureGluingSeam :
    KleinClosureOpenObligation

  missingClosedSurfaceCarrier :
    KleinClosureOpenObligation

  missingNonOrientabilityGate :
    KleinClosureOpenObligation

  missingInsideOutsideDistinctionGate :
    KleinClosureOpenObligation

  missingPromotionAuthorityBoundary :
    KleinClosureOpenObligation

canonicalKleinClosureOpenObligations :
  List KleinClosureOpenObligation
canonicalKleinClosureOpenObligations =
  missingFirstMobiusBandCarrier
  ∷ missingSecondMobiusBandCarrier
  ∷ missingClosureGluingSeam
  ∷ missingClosedSurfaceCarrier
  ∷ missingNonOrientabilityGate
  ∷ missingInsideOutsideDistinctionGate
  ∷ missingPromotionAuthorityBoundary
  ∷ []

data KleinClosureTarget : Set where
  twoMobiusBandsClosedTarget :
    KleinClosureTarget

  closedNonOrientableSurfaceTarget :
    KleinClosureTarget

  noGlobalInsideOutsideTarget :
    KleinClosureTarget

canonicalKleinClosureTargets :
  List KleinClosureTarget
canonicalKleinClosureTargets =
  twoMobiusBandsClosedTarget
  ∷ closedNonOrientableSurfaceTarget
  ∷ noGlobalInsideOutsideTarget
  ∷ []

data KleinClosurePromotionAuthorityToken : Set where

record KleinBottleClosureSurface : Set where
  field
    firstMobiusBandCarrier :
      String

    secondMobiusBandCarrier :
      String

    gluingSeamCarrier :
      String

    closedSurfaceCarrier :
      String

    twoMobiusClosureWitness :
      Nat

    twoMobiusClosureWitness-v :
      twoMobiusClosureWitness ≡ 2

    closureTargetName :
      String

    closureTargetName-v :
      closureTargetName
      ≡
      "target-only-klein-bottle-closure-of-two-mobius-bands"

    closedSurfaceDeclared :
      Bool

    closedSurfaceDeclaredIsTrue :
      closedSurfaceDeclared ≡ true

    nonOrientabilityGate :
      Bool

    nonOrientabilityGateIsFalse :
      nonOrientabilityGate ≡ false

    insideOutsideDistinctionGate :
      Bool

    insideOutsideDistinctionGateIsFalse :
      insideOutsideDistinctionGate ≡ false

    globallyInsideOutsideNeutral :
      Bool

    globallyInsideOutsideNeutralIsFalse :
      globallyInsideOutsideNeutral ≡ false

    twoMobiusBandsImported :
      Bool

    twoMobiusBandsImportedIsTrue :
      twoMobiusBandsImported ≡ true

    authorityBoundary :
      String

    receiptBoundary :
      List String

open KleinBottleClosureSurface public

canonicalKleinBottleClosureSurface :
  KleinBottleClosureSurface
canonicalKleinBottleClosureSurface =
  record
    { firstMobiusBandCarrier =
        "first Mobius band carrier"
    ; secondMobiusBandCarrier =
        "second Mobius band carrier"
    ; gluingSeamCarrier =
        "boundary gluing seam"
    ; closedSurfaceCarrier =
        "closed non-orientable surface carrier"
    ; twoMobiusClosureWitness =
        2
    ; twoMobiusClosureWitness-v =
        refl
    ; closureTargetName =
        "target-only-klein-bottle-closure-of-two-mobius-bands"
    ; closureTargetName-v =
        refl
    ; closedSurfaceDeclared =
        true
    ; closedSurfaceDeclaredIsTrue =
        refl
    ; nonOrientabilityGate =
        false
    ; nonOrientabilityGateIsFalse =
        refl
    ; insideOutsideDistinctionGate =
        false
    ; insideOutsideDistinctionGateIsFalse =
        refl
    ; globallyInsideOutsideNeutral =
        false
    ; globallyInsideOutsideNeutralIsFalse =
        refl
    ; twoMobiusBandsImported =
        true
    ; twoMobiusBandsImportedIsTrue =
        refl
    ; authorityBoundary =
        "no Klein-bottle orientation or duality promotion is manufactured here"
    ; receiptBoundary =
        "Two Mobius bands are named as imported carriers"
        ∷ "The closure witness is recorded as a two-band identification"
        ∷ "The closed surface carrier is named without promoting a theorem"
        ∷ "Non-orientability and global inside/outside distinction both stay false"
        ∷ "No promotion authority is manufactured in this candidate-only receipt"
        ∷ []
    }

canonicalKleinClosureReceiptStatus :
  KleinClosureReceiptStatus
canonicalKleinClosureReceiptStatus =
  kleinClosureTargetsOnlyNoPromotion

kleinTwoMobiusClosureWitness :
  Nat
kleinTwoMobiusClosureWitness =
  twoMobiusClosureWitness canonicalKleinBottleClosureSurface

kleinTwoMobiusClosureWitnessIsTwo :
  kleinTwoMobiusClosureWitness ≡ 2
kleinTwoMobiusClosureWitnessIsTwo =
  twoMobiusClosureWitness-v canonicalKleinBottleClosureSurface

kleinNonOrientabilityGateIsFalse :
  nonOrientabilityGate canonicalKleinBottleClosureSurface ≡ false
kleinNonOrientabilityGateIsFalse =
  nonOrientabilityGateIsFalse canonicalKleinBottleClosureSurface

kleinInsideOutsideDistinctionGateIsFalse :
  insideOutsideDistinctionGate canonicalKleinBottleClosureSurface ≡ false
kleinInsideOutsideDistinctionGateIsFalse =
  insideOutsideDistinctionGateIsFalse canonicalKleinBottleClosureSurface

kleinGloballyInsideOutsideNeutralIsFalse :
  globallyInsideOutsideNeutral canonicalKleinBottleClosureSurface ≡ false
kleinGloballyInsideOutsideNeutralIsFalse =
  globallyInsideOutsideNeutralIsFalse canonicalKleinBottleClosureSurface
