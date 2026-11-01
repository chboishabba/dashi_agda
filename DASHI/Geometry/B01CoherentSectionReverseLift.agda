module DASHI.Geometry.B01CoherentSectionReverseLift where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ; zero; suc)

open import DASHI.Geometry.DCHoTTBridgeObligationIndex

------------------------------------------------------------------------
-- B0.1 reverse-lift construction from a coherent tower of sections.
--
-- This is a genuine DASHI-side construction: if every refinement map
-- phi_d : X_(d+1) -> X_d admits a chosen section, then every depth-zero
-- point extends to a compatible family through the full refinement tower.
-- It discharges the reverse-Im-lift socket under that explicit hypothesis.
-- It does not construct the missing DCHoTT formal-space adapter and does
-- not promote B0, Levi-Civita, GR, AQFT, or the terminal composition claim.

record CoherentSectionTower (P : ProObjectCarrier) : Set₁ where
  field
    liftStep :
      (d : ℕ) →
      ProObjectCarrier.depthCarrier P d →
      ProObjectCarrier.depthCarrier P (suc d)

    liftStepSection :
      (d : ℕ) →
      (x : ProObjectCarrier.depthCarrier P d) →
      ProObjectCarrier.refinementMap P d (liftStep d x)
      ≡
      x

open CoherentSectionTower public

pointFromCoherentSections :
  {P : ProObjectCarrier} →
  CoherentSectionTower P →
  ProObjectCarrier.depthCarrier P zero →
  (d : ℕ) →
  ProObjectCarrier.depthCarrier P d
pointFromCoherentSections tower x0 zero =
  x0
pointFromCoherentSections tower x0 (suc d) =
  CoherentSectionTower.liftStep tower d
    (pointFromCoherentSections tower x0 d)

pointFromCoherentSectionsCompatible :
  {P : ProObjectCarrier} →
  (tower : CoherentSectionTower P) →
  (x0 : ProObjectCarrier.depthCarrier P zero) →
  (d : ℕ) →
  ProObjectCarrier.refinementMap P d
    (pointFromCoherentSections tower x0 (suc d))
  ≡
  pointFromCoherentSections tower x0 d
pointFromCoherentSectionsCompatible tower x0 d =
  CoherentSectionTower.liftStepSection tower d
    (pointFromCoherentSections tower x0 d)

proObjectPointFromCoherentSections :
  {P : ProObjectCarrier} →
  CoherentSectionTower P →
  ProObjectCarrier.depthCarrier P zero →
  ProObjectPoint P
proObjectPointFromCoherentSections tower x0 =
  record
    { point =
        pointFromCoherentSections tower x0
    ; coherence =
        pointFromCoherentSectionsCompatible tower x0
    }

proObjectPointFromCoherentSectionsAtZero :
  {P : ProObjectCarrier} →
  (tower : CoherentSectionTower P) →
  (x0 : ProObjectCarrier.depthCarrier P zero) →
  Im (proObjectPointFromCoherentSections tower x0)
  ≡
  x0
proObjectPointFromCoherentSectionsAtZero _ _ =
  refl

reverseLiftDataFromCoherentSections :
  {P : ProObjectCarrier} →
  CoherentSectionTower P →
  ReverseLiftData P
reverseLiftDataFromCoherentSections tower =
  record
    { liftPointAtIm =
        proObjectPointFromCoherentSections tower
    ; liftPointAtImSection =
        λ _ → refl
    }

coherentSectionsDischargeReverseImLift :
  {P : ProObjectCarrier} →
  CoherentSectionTower P →
  (x0 : ProObjectCarrier.depthCarrier P zero) →
  ImFibreAt {P = P} x0
coherentSectionsDischargeReverseImLift tower =
  reverseLiftDataToImFibre
    (reverseLiftDataFromCoherentSections tower)

record B01CoherentSectionReverseLiftReceipt
  (P : ProObjectCarrier) :
  Setω where
  field
    sectionTower :
      CoherentSectionTower P

    reverseLiftData :
      ReverseLiftData P

    reverseLiftData-v :
      reverseLiftData
      ≡
      reverseLiftDataFromCoherentSections sectionTower

    reverseLiftConstructedForAllDepthZeroPoints :
      Bool

    reverseLiftConstructedForAllDepthZeroPointsIsTrue :
      reverseLiftConstructedForAllDepthZeroPoints
      ≡
      true

    remainingFirstBlocker :
      DCHoTTB0BridgeBlocker

    remainingFirstBlocker-v :
      remainingFirstBlocker
      ≡
      missingCarrierToDSpace

    b0PromotedByThisReceipt :
      Bool

    b0PromotedByThisReceiptIsFalse :
      b0PromotedByThisReceipt
      ≡
      false

    scope :
      String

    scope-v :
      scope
      ≡
      "conditional-B0.1-reverse-lift-from-sections-only; DCHoTT-formal-space-and-modal-reflection-remain-open"

open B01CoherentSectionReverseLiftReceipt public

canonicalB01CoherentSectionReverseLiftReceipt :
  {P : ProObjectCarrier} →
  CoherentSectionTower P →
  B01CoherentSectionReverseLiftReceipt P
canonicalB01CoherentSectionReverseLiftReceipt tower =
  record
    { sectionTower =
        tower
    ; reverseLiftData =
        reverseLiftDataFromCoherentSections tower
    ; reverseLiftData-v =
        refl
    ; reverseLiftConstructedForAllDepthZeroPoints =
        true
    ; reverseLiftConstructedForAllDepthZeroPointsIsTrue =
        refl
    ; remainingFirstBlocker =
        missingCarrierToDSpace
    ; remainingFirstBlocker-v =
        refl
    ; b0PromotedByThisReceipt =
        false
    ; b0PromotedByThisReceiptIsFalse =
        refl
    ; scope =
        "conditional-B0.1-reverse-lift-from-sections-only; DCHoTT-formal-space-and-modal-reflection-remain-open"
    ; scope-v =
        refl
    }
