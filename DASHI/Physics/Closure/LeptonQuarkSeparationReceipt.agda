module DASHI.Physics.Closure.LeptonQuarkSeparationReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.D8LeptonLaneReceipt as D8

------------------------------------------------------------------------
-- Quark/lepton separation candidate at the first Heegner layers.

data LeptonQuarkSeparationStatus : Set where
  leptonQuarkSeparationCandidateRecorded :
    LeptonQuarkSeparationStatus

data LeptonQuarkSeparationBlocker : Set where
  unitGroupRatioDoesNotGiveSMChargeRatio :
    LeptonQuarkSeparationBlocker

  conductorAndCMTypeDistinctionNotEnough :
    LeptonQuarkSeparationBlocker

  leptonChargeAssignmentOpen :
    LeptonQuarkSeparationBlocker

canonicalLeptonQuarkSeparationBlockers :
  List LeptonQuarkSeparationBlocker
canonicalLeptonQuarkSeparationBlockers =
  unitGroupRatioDoesNotGiveSMChargeRatio
  ∷ conductorAndCMTypeDistinctionNotEnough
  ∷ leptonChargeAssignmentOpen
  ∷ []

data LeptonQuarkSeparationPromotion : Set where

leptonQuarkSeparationPromotionImpossibleHere :
  LeptonQuarkSeparationPromotion →
  ⊥
leptonQuarkSeparationPromotionImpossibleHere ()

record LeptonQuarkSeparationReceipt : Set where
  field
    status :
      LeptonQuarkSeparationStatus

    d8Lane :
      D8.D8LeptonLaneReceipt

    d8LaneIsCanonical :
      d8Lane ≡ D8.canonicalD8LeptonLaneReceipt

    p2QuarkDiscriminant :
      String

    p2QuarkJInvariant :
      Nat

    p2QuarkCMRing :
      String

    p2QuarkConductor :
      Nat

    p2QuarkUnitGroupOrder :
      Nat

    d8LeptonDiscriminant :
      String

    d8LeptonJInvariant :
      Nat

    d8LeptonCMRing :
      String

    d8LeptonConductor :
      Nat

    d8LeptonUnitGroupOrder :
      Nat

    unitGroupOrderRatio :
      Nat

    sameConductorClaim :
      Bool

    sameConductorClaimIsFalse :
      sameConductorClaim ≡ false

    differentCMTypeAtFirstLayer :
      Bool

    differentCMTypeAtFirstLayerIsTrue :
      differentCMTypeAtFirstLayer ≡ true

    unitGroupRatioGivesSMChargeRatio :
      Bool

    unitGroupRatioGivesSMChargeRatioIsFalse :
      unitGroupRatioGivesSMChargeRatio ≡ false

    separationMechanismIdentified :
      Bool

    separationMechanismIdentifiedIsFalse :
      separationMechanismIdentified ≡ false

    leptonSectorPromoted :
      Bool

    leptonSectorPromotedIsFalse :
      leptonSectorPromoted ≡ false

    smMatterPromoted :
      Bool

    smMatterPromotedIsFalse :
      smMatterPromoted ≡ false

    blockers :
      List LeptonQuarkSeparationBlocker

    blockersAreCanonical :
      blockers ≡ canonicalLeptonQuarkSeparationBlockers

    promotionFlags :
      List LeptonQuarkSeparationPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open LeptonQuarkSeparationReceipt public

canonicalLeptonQuarkSeparationReceipt :
  LeptonQuarkSeparationReceipt
canonicalLeptonQuarkSeparationReceipt =
  record
    { status =
        leptonQuarkSeparationCandidateRecorded
    ; d8Lane =
        D8.canonicalD8LeptonLaneReceipt
    ; d8LaneIsCanonical =
        refl
    ; p2QuarkDiscriminant =
        "D=-4"
    ; p2QuarkJInvariant =
        1728
    ; p2QuarkCMRing =
        "Z[i]"
    ; p2QuarkConductor =
        4
    ; p2QuarkUnitGroupOrder =
        4
    ; d8LeptonDiscriminant =
        "D=-8"
    ; d8LeptonJInvariant =
        8000
    ; d8LeptonCMRing =
        "Z[sqrt(-2)]"
    ; d8LeptonConductor =
        8
    ; d8LeptonUnitGroupOrder =
        2
    ; unitGroupOrderRatio =
        2
    ; sameConductorClaim =
        false
    ; sameConductorClaimIsFalse =
        refl
    ; differentCMTypeAtFirstLayer =
        true
    ; differentCMTypeAtFirstLayerIsTrue =
        refl
    ; unitGroupRatioGivesSMChargeRatio =
        false
    ; unitGroupRatioGivesSMChargeRatioIsFalse =
        refl
    ; separationMechanismIdentified =
        false
    ; separationMechanismIdentifiedIsFalse =
        refl
    ; leptonSectorPromoted =
        false
    ; leptonSectorPromotedIsFalse =
        refl
    ; smMatterPromoted =
        false
    ; smMatterPromotedIsFalse =
        refl
    ; blockers =
        canonicalLeptonQuarkSeparationBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The D=-4 and D=-8 lanes distinguish quark/lepton candidates by CM type and conductor"
        ∷ "The unit-group order ratio 4/2=2 does not reproduce the SM charge ratios"
        ∷ "No lepton or SM matter promotion is asserted"
        ∷ []
    }

leptonQuarkSeparationDoesNotPromoteSM :
  smMatterPromoted canonicalLeptonQuarkSeparationReceipt ≡ false
leptonQuarkSeparationDoesNotPromoteSM =
  refl

