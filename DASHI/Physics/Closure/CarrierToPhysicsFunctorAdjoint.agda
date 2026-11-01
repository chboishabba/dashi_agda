module DASHI.Physics.Closure.CarrierToPhysicsFunctorAdjoint where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierToPhysicsInterpretationFunctor as Gate1

------------------------------------------------------------------------
-- Gate 1/6 adjunction and colimit bridge.
--
-- The interpretation functor is already inhabited, and the current bridge
-- remains fail-closed at the exact missing left-adjoint/colimit theorem.
-- This module packages the canonical Gate 1 receipts together with the
-- precise honest blockers instead of fabricating a promoted adjunction.

data CarrierToPhysicsFunctorAdjointStatus : Set where
  adjointBridgeRecordedNoPromotion :
    CarrierToPhysicsFunctorAdjointStatus

record CarrierToPhysicsFunctorAdjointReceipt : Setω where
  field
    status :
      CarrierToPhysicsFunctorAdjointStatus

    interpretationReceipt :
      Gate1.CarrierToPhysicsInterpretationReceipt

    functorLawReceiptSurface :
      Gate1.CarrierToPhysicsFunctorLawReceiptSurface

    filteredColimitLawReceipt :
      Gate1.FiniteSupportFilteredColimitLawReceipt

    dhrCompatibilityLawReceipt :
      Gate1.DHRSectorCompatibilityLawReceipt

    filteredColimitPrimitive :
      Gate1.CarrierToPhysicsMissingPrimitiveWitness
        Gate1.missingFilteredColimitPreservation

    dhrCompatibilityPrimitive :
      Gate1.CarrierToPhysicsMissingPrimitiveWitness
        Gate1.missingDHRSectorCompatibility

    leftAdjointDependency :
      Gate1.ExactStandardModelCarrierFunctorMatchDependency

    leftAdjointDependencyIsCanonical :
      leftAdjointDependency
      ≡
      Gate1.dependencyMissingLeftAdjointCarrierPhysicsColimitTheorem

    exactStandardModelCarrierFunctorMatchBlocker :
      Gate1.ExactStandardModelCarrierFunctorMatchBlocker

    exactStandardModelCarrierFunctorMatchBlockerIsCanonical :
      exactStandardModelCarrierFunctorMatchBlocker
      ≡
      Gate1.missingExactStandardModelCarrierFunctorMatch

    filteredColimitPreservationPromoted :
      Bool

    filteredColimitPreservationPromotedIsFalse :
      filteredColimitPreservationPromoted ≡ false

    dhrSectorCompatibilityPromoted :
      Bool

    dhrSectorCompatibilityPromotedIsFalse :
      dhrSectorCompatibilityPromoted ≡ false

    leftAdjointPromoted :
      Bool

    leftAdjointPromotedIsFalse :
      leftAdjointPromoted ≡ false

    adjointBoundary :
      List String

open CarrierToPhysicsFunctorAdjointReceipt public

canonicalCarrierToPhysicsFunctorAdjointReceipt :
  CarrierToPhysicsFunctorAdjointReceipt
canonicalCarrierToPhysicsFunctorAdjointReceipt =
  record
    { status =
        adjointBridgeRecordedNoPromotion
    ; interpretationReceipt =
        Gate1.canonicalCarrierToPhysicsInterpretationReceipt
    ; functorLawReceiptSurface =
        Gate1.canonicalCarrierToPhysicsFunctorLawReceiptSurface
    ; filteredColimitLawReceipt =
        Gate1.canonicalFiniteSupportFilteredColimitLawReceipt
    ; dhrCompatibilityLawReceipt =
        Gate1.canonicalDHRSectorCompatibilityLawReceipt
    ; filteredColimitPrimitive =
        Gate1.missingFiniteSupportFilteredColimitPrimitiveWitness
    ; dhrCompatibilityPrimitive =
        Gate1.missingDHRSectorCompatibilityPrimitiveWitness
    ; leftAdjointDependency =
        Gate1.dependencyMissingLeftAdjointCarrierPhysicsColimitTheorem
    ; leftAdjointDependencyIsCanonical =
        refl
    ; exactStandardModelCarrierFunctorMatchBlocker =
        Gate1.missingExactStandardModelCarrierFunctorMatch
    ; exactStandardModelCarrierFunctorMatchBlockerIsCanonical =
        refl
    ; filteredColimitPreservationPromoted =
        false
    ; filteredColimitPreservationPromotedIsFalse =
        refl
    ; dhrSectorCompatibilityPromoted =
        false
    ; dhrSectorCompatibilityPromotedIsFalse =
        refl
    ; leftAdjointPromoted =
        false
    ; leftAdjointPromotedIsFalse =
        refl
    ; adjointBoundary =
        "Gate 1 interpretation functor is inhabited and kept separate from the left-adjoint claim"
        ∷ "Filtered-colimit preservation is consumed only as the existing finite-support law surface"
        ∷ "DHR-sector compatibility is consumed only as the existing local compatibility law surface"
        ∷ "The exact left-adjoint/colimit theorem remains blocked by dependencyMissingLeftAdjointCarrierPhysicsColimitTheorem"
        ∷ "No filtered-colimit, DHR-sector, or adjunction promotion is fabricated"
        ∷ []
    }

carrierToPhysicsFunctorAdjointKeepsLeftAdjointFalse :
  leftAdjointPromoted canonicalCarrierToPhysicsFunctorAdjointReceipt
  ≡
  false
carrierToPhysicsFunctorAdjointKeepsLeftAdjointFalse =
  refl

carrierToPhysicsFunctorAdjointKeepsFilteredColimitFalse :
  filteredColimitPreservationPromoted
    canonicalCarrierToPhysicsFunctorAdjointReceipt
  ≡
  false
carrierToPhysicsFunctorAdjointKeepsFilteredColimitFalse =
  refl

carrierToPhysicsFunctorAdjointKeepsDHRCompatibilityFalse :
  dhrSectorCompatibilityPromoted
    canonicalCarrierToPhysicsFunctorAdjointReceipt
  ≡
  false
carrierToPhysicsFunctorAdjointKeepsDHRCompatibilityFalse =
  refl
