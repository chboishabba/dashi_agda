module DASHI.Physics.Closure.NSTailDominanceCarryAnalogyReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSViscousTailDominanceReceipt as Tail

------------------------------------------------------------------------
-- Navier-Stokes tail-dominance carry analogy receipt.
--
-- This is a bookkeeping analogy only.  Tail dominance says the NS cascade
-- does not fall into the mod-3 trap: carries above K*(nu) are absorbed by
-- viscosity before cycling back as unresolved residuals.

data NSTailDominanceCarryAnalogyStatus : Set where
  nsTailDominanceCarryAnalogyRecorded_bookkeepingOnly :
    NSTailDominanceCarryAnalogyStatus

data BalancedCarryStep : Set where
  plusOnePlusPlusOneCarriesToNextScale :
    BalancedCarryStep

data NSCascadeBookkeepingRole : Set where
  cascadeInjection :
    NSCascadeBookkeepingRole

  currentScaleDepletion :
    NSCascadeBookkeepingRole

  nextScaleCarry :
    NSCascadeBookkeepingRole

  viscousAbsorptionAboveKStar :
    NSCascadeBookkeepingRole

canonicalCascadeBookkeepingRoles :
  List NSCascadeBookkeepingRole
canonicalCascadeBookkeepingRoles =
  cascadeInjection
  ∷ currentScaleDepletion
  ∷ nextScaleCarry
  ∷ viscousAbsorptionAboveKStar
  ∷ []

data TailEnergy : Set where
  energyPoppedPastKStarWithoutAbsorption :
    TailEnergy

data Lane7Reading : Set where
  empiricalFormalNonIncreasingBookkeeping :
    Lane7Reading

data NSTailDominanceCarryBoundary : Set where
  analogyBookkeepingOnly :
    NSTailDominanceCarryBoundary

  noNavierStokesProof :
    NSTailDominanceCarryBoundary

  noGate3Closure :
    NSTailDominanceCarryBoundary

  noClayPromotion :
    NSTailDominanceCarryBoundary

canonicalNSTailDominanceCarryBoundaries :
  List NSTailDominanceCarryBoundary
canonicalNSTailDominanceCarryBoundaries =
  analogyBookkeepingOnly
  ∷ noNavierStokesProof
  ∷ noGate3Closure
  ∷ noClayPromotion
  ∷ []

data NSTailDominanceCarryPromotion : Set where

nsTailDominanceCarryPromotionImpossibleHere :
  NSTailDominanceCarryPromotion →
  ⊥
nsTailDominanceCarryPromotionImpossibleHere ()

oneLineAnalogyStatement :
  String
oneLineAnalogyStatement =
  "Tail dominance says the NS cascade does not fall into the mod-3 trap; carries above K*(nu) are absorbed by viscosity before cycling back as unresolved residuals."

balancedCarryStatement :
  String
balancedCarryStatement =
  "+1 + +1 = (-1_k, +1_{k+1}) is read as NS cascade injection at scale k, depletion at scale k, and a carried deposit into scale k+1."

tailEnergyStatement :
  String
tailEnergyStatement =
  "TailEnergy tracks energy popped past K*(nu) without viscous absorption."

lane7Statement :
  String
lane7Statement =
  "Lane7 non-increasing is empirical/formal bookkeeping, not a Clay proof."

boundaryStatement :
  String
boundaryStatement =
  "This receipt records an analogy only: no NS proof, no Gate 3 closure, and no Clay promotion."

record NSTailDominanceCarryAnalogyReceipt : Setω where
  field
    status :
      NSTailDominanceCarryAnalogyStatus

    statusIsBookkeepingOnly :
      status ≡ nsTailDominanceCarryAnalogyRecorded_bookkeepingOnly

    viscousTailReceipt :
      Tail.NSViscousTailDominanceReceipt

    viscousTailClayFalse :
      Tail.clayNavierStokesPromoted viscousTailReceipt ≡ false

    viscousTailUniversalNSFalse :
      Tail.universalNSRegularityTheorem viscousTailReceipt ≡ false

    oneLineAnalogy :
      String

    oneLineAnalogyIsCanonical :
      oneLineAnalogy ≡ oneLineAnalogyStatement

    balancedCarryStep :
      BalancedCarryStep

    balancedCarryStepIsCanonical :
      balancedCarryStep ≡ plusOnePlusPlusOneCarriesToNextScale

    carryBookkeepingRoles :
      List NSCascadeBookkeepingRole

    carryBookkeepingRolesAreCanonical :
      carryBookkeepingRoles ≡ canonicalCascadeBookkeepingRoles

    carryBookkeeping :
      String

    carryBookkeepingIsCanonical :
      carryBookkeeping ≡ balancedCarryStatement

    tailEnergy :
      TailEnergy

    tailEnergyIsPoppedPastKStar :
      tailEnergy ≡ energyPoppedPastKStarWithoutAbsorption

    tailEnergyReading :
      String

    tailEnergyReadingIsCanonical :
      tailEnergyReading ≡ tailEnergyStatement

    lane7Reading :
      Lane7Reading

    lane7ReadingIsEmpiricalFormalBookkeeping :
      lane7Reading ≡ empiricalFormalNonIncreasingBookkeeping

    lane7Summary :
      String

    lane7SummaryIsCanonical :
      lane7Summary ≡ lane7Statement

    mod3TrapAvoidedByTailDominance :
      Bool

    mod3TrapAvoidedByTailDominanceIsTrue :
      mod3TrapAvoidedByTailDominance ≡ true

    residualCycleClaimed :
      Bool

    residualCycleClaimedIsFalse :
      residualCycleClaimed ≡ false

    nsProofPromoted :
      Bool

    nsProofPromotedIsFalse :
      nsProofPromoted ≡ false

    gate3ClosurePromoted :
      Bool

    gate3ClosurePromotedIsFalse :
      gate3ClosurePromoted ≡ false

    clayPromotionMade :
      Bool

    clayPromotionMadeIsFalse :
      clayPromotionMade ≡ false

    boundaries :
      List NSTailDominanceCarryBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalNSTailDominanceCarryBoundaries

    promotionFlags :
      List NSTailDominanceCarryPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    noPromotion :
      NSTailDominanceCarryPromotion →
      ⊥

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ boundaryStatement

open NSTailDominanceCarryAnalogyReceipt public

canonicalNSTailDominanceCarryAnalogyReceipt :
  NSTailDominanceCarryAnalogyReceipt
canonicalNSTailDominanceCarryAnalogyReceipt =
  record
    { status =
        nsTailDominanceCarryAnalogyRecorded_bookkeepingOnly
    ; statusIsBookkeepingOnly =
        refl
    ; viscousTailReceipt =
        Tail.canonicalNSViscousTailDominanceReceipt
    ; viscousTailClayFalse =
        refl
    ; viscousTailUniversalNSFalse =
        refl
    ; oneLineAnalogy =
        oneLineAnalogyStatement
    ; oneLineAnalogyIsCanonical =
        refl
    ; balancedCarryStep =
        plusOnePlusPlusOneCarriesToNextScale
    ; balancedCarryStepIsCanonical =
        refl
    ; carryBookkeepingRoles =
        canonicalCascadeBookkeepingRoles
    ; carryBookkeepingRolesAreCanonical =
        refl
    ; carryBookkeeping =
        balancedCarryStatement
    ; carryBookkeepingIsCanonical =
        refl
    ; tailEnergy =
        energyPoppedPastKStarWithoutAbsorption
    ; tailEnergyIsPoppedPastKStar =
        refl
    ; tailEnergyReading =
        tailEnergyStatement
    ; tailEnergyReadingIsCanonical =
        refl
    ; lane7Reading =
        empiricalFormalNonIncreasingBookkeeping
    ; lane7ReadingIsEmpiricalFormalBookkeeping =
        refl
    ; lane7Summary =
        lane7Statement
    ; lane7SummaryIsCanonical =
        refl
    ; mod3TrapAvoidedByTailDominance =
        true
    ; mod3TrapAvoidedByTailDominanceIsTrue =
        refl
    ; residualCycleClaimed =
        false
    ; residualCycleClaimedIsFalse =
        refl
    ; nsProofPromoted =
        false
    ; nsProofPromotedIsFalse =
        refl
    ; gate3ClosurePromoted =
        false
    ; gate3ClosurePromotedIsFalse =
        refl
    ; clayPromotionMade =
        false
    ; clayPromotionMadeIsFalse =
        refl
    ; boundaries =
        canonicalNSTailDominanceCarryBoundaries
    ; boundariesAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; noPromotion =
        nsTailDominanceCarryPromotionImpossibleHere
    ; receiptBoundary =
        boundaryStatement
    ; receiptBoundaryIsCanonical =
        refl
    }

canonicalNSTailDominanceCarryNoNSProof :
  nsProofPromoted canonicalNSTailDominanceCarryAnalogyReceipt ≡ false
canonicalNSTailDominanceCarryNoNSProof =
  refl

canonicalNSTailDominanceCarryNoGate3Closure :
  gate3ClosurePromoted canonicalNSTailDominanceCarryAnalogyReceipt ≡ false
canonicalNSTailDominanceCarryNoGate3Closure =
  refl

canonicalNSTailDominanceCarryNoClayPromotion :
  clayPromotionMade canonicalNSTailDominanceCarryAnalogyReceipt ≡ false
canonicalNSTailDominanceCarryNoClayPromotion =
  refl
