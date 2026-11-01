module DASHI.Physics.Closure.CarrierEnergyToMassShellReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Carrier-energy-to-mass-shell boundary receipt.
--
-- The receipt separates an internal carrier energy gap from a physical
-- mass-shell statement.  It records the bridge as a required conditional
-- boundary, not as a proof of continuum particle physics.

data MassShellBridgeAuthorityToken : Set where

massShellBridgePromotionBlockedHere :
  MassShellBridgeAuthorityToken →
  ⊥
massShellBridgePromotionBlockedHere ()

internalCarrierEnergyGapLabel : String
internalCarrierEnergyGapLabel =
  "internal-carrier-energy-gap"

physicalMassShellGapLabel : String
physicalMassShellGapLabel =
  "physical-continuum-mass-shell-gap"

requiredConditionalBridgeLabel : String
requiredConditionalBridgeLabel =
  "conditional-bridge-from-carrier-energy-gap-to-physical-mass-shell"

record CarrierEnergyToMassShellReceipt : Setω where
  field
    sourceGap :
      String

    sourceGap-v :
      sourceGap ≡ internalCarrierEnergyGapLabel

    targetGap :
      String

    targetGap-v :
      targetGap ≡ physicalMassShellGapLabel

    bridgeKind :
      String

    bridgeKind-v :
      bridgeKind ≡ requiredConditionalBridgeLabel

    internalCarrierEnergyGapRecorded :
      Bool

    internalCarrierEnergyGapRecorded-v :
      internalCarrierEnergyGapRecorded ≡ true

    physicalMassShellGapProvedHere :
      Bool

    physicalMassShellGapProvedHere-v :
      physicalMassShellGapProvedHere ≡ false

    bridgeRequired :
      Bool

    bridgeRequired-v :
      bridgeRequired ≡ true

    bridgeDischargedHere :
      Bool

    bridgeDischargedHere-v :
      bridgeDischargedHere ≡ false

    treatsCarrierGapAsPhysicalMassGap :
      Bool

    treatsCarrierGapAsPhysicalMassGap-v :
      treatsCarrierGapAsPhysicalMassGap ≡ false

    continuumParticlePhysicsConstructed :
      Bool

    continuumParticlePhysicsConstructed-v :
      continuumParticlePhysicsConstructed ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromoted-v :
      clayYangMillsPromoted ≡ false

    noMassShellPromotionWithoutAuthority :
      MassShellBridgeAuthorityToken →
      ⊥

    governanceBoundary :
      List String

open CarrierEnergyToMassShellReceipt public

canonicalCarrierEnergyToMassShellReceipt :
  CarrierEnergyToMassShellReceipt
canonicalCarrierEnergyToMassShellReceipt =
  record
    { sourceGap =
        internalCarrierEnergyGapLabel
    ; sourceGap-v =
        refl
    ; targetGap =
        physicalMassShellGapLabel
    ; targetGap-v =
        refl
    ; bridgeKind =
        requiredConditionalBridgeLabel
    ; bridgeKind-v =
        refl
    ; internalCarrierEnergyGapRecorded =
        true
    ; internalCarrierEnergyGapRecorded-v =
        refl
    ; physicalMassShellGapProvedHere =
        false
    ; physicalMassShellGapProvedHere-v =
        refl
    ; bridgeRequired =
        true
    ; bridgeRequired-v =
        refl
    ; bridgeDischargedHere =
        false
    ; bridgeDischargedHere-v =
        refl
    ; treatsCarrierGapAsPhysicalMassGap =
        false
    ; treatsCarrierGapAsPhysicalMassGap-v =
        refl
    ; continuumParticlePhysicsConstructed =
        false
    ; continuumParticlePhysicsConstructed-v =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromoted-v =
        refl
    ; noMassShellPromotionWithoutAuthority =
        massShellBridgePromotionBlockedHere
    ; governanceBoundary =
        "records internal carrier energy gap and physical mass-shell gap as distinct"
        ∷ "mass-shell bridge is required and conditional"
        ∷ "bridge is not discharged by this receipt"
        ∷ "continuum particle physics and Clay Yang-Mills promotion remain false"
        ∷ []
    }

canonicalCarrierEnergyBridgeRequired :
  bridgeRequired canonicalCarrierEnergyToMassShellReceipt ≡ true
canonicalCarrierEnergyBridgeRequired =
  refl

canonicalCarrierEnergyBridgeNotDischargedHere :
  bridgeDischargedHere canonicalCarrierEnergyToMassShellReceipt ≡ false
canonicalCarrierEnergyBridgeNotDischargedHere =
  refl

canonicalCarrierEnergyGapIsNotPhysicalMassGap :
  treatsCarrierGapAsPhysicalMassGap canonicalCarrierEnergyToMassShellReceipt ≡ false
canonicalCarrierEnergyGapIsNotPhysicalMassGap =
  refl
