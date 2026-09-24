module DASHI.Physics.Boundaries.VHiggsDefinitionalReceipt where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Definitional v_Higgs value receipt.
--
-- This is an external numerical convention receipt, not a Higgs mechanism
-- proof and not a physical Yukawa promotion.  The value is recorded as a
-- rational decimal pair so downstream CKM/Yukawa lanes can cite the boundary
-- without claiming an inhabited W4/SI calibration theorem.

data VHiggsDefinitionalStatus : Set where
  vHiggsPDG2024RecordedNoPhysicalPromotion :
    VHiggsDefinitionalStatus

record VHiggsDefinitionalReceipt : Set where
  field
    status :
      VHiggsDefinitionalStatus

    valueGeVTimes100 :
      Nat

    valueGeVTimes100Is24622 :
      valueGeVTimes100 ≡ 24622

    uncertaintyGeVTimes100 :
      Nat

    uncertaintyGeVTimes100Is1 :
      uncertaintyGeVTimes100 ≡ 1

    citation :
      String

    citation-v :
      citation
      ≡
      "PDG 2024 Review of Particle Physics, Electroweak Model and Constraints on New Physics: v = 246.22 GeV"

    adapter4BoundaryRetained :
      Bool

    adapter4BoundaryRetainedIsTrue :
      adapter4BoundaryRetained ≡ true

    siUnitsPromoted :
      Bool

    siUnitsPromotedIsFalse :
      siUnitsPromoted ≡ false

    physicalYukawaPromotionClaimed :
      Bool

    physicalYukawaPromotionClaimedIsFalse :
      physicalYukawaPromotionClaimed ≡ false

    definitionalBoundary :
      List String

open VHiggsDefinitionalReceipt public

canonicalVHiggsDefinitionalReceipt :
  VHiggsDefinitionalReceipt
canonicalVHiggsDefinitionalReceipt =
  record
    { status =
        vHiggsPDG2024RecordedNoPhysicalPromotion
    ; valueGeVTimes100 =
        24622
    ; valueGeVTimes100Is24622 =
        refl
    ; uncertaintyGeVTimes100 =
        1
    ; uncertaintyGeVTimes100Is1 =
        refl
    ; citation =
        "PDG 2024 Review of Particle Physics, Electroweak Model and Constraints on New Physics: v = 246.22 GeV"
    ; citation-v =
        refl
    ; adapter4BoundaryRetained =
        true
    ; adapter4BoundaryRetainedIsTrue =
        refl
    ; siUnitsPromoted =
        false
    ; siUnitsPromotedIsFalse =
        refl
    ; physicalYukawaPromotionClaimed =
        false
    ; physicalYukawaPromotionClaimedIsFalse =
        refl
    ; definitionalBoundary =
        "v_Higgs is recorded as 246.22 GeV at the Adapter 4 boundary for bookkeeping"
        ∷ "This receipt does not prove the Higgs mechanism, nonzero VEV, or W4/SI calibration"
        ∷ "Downstream Yukawa lanes may cite the value only as a definitional external boundary"
        ∷ []
    }
