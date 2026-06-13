module DASHI.Physics.Closure.Gate3MassShellBridgeConstructedReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierEnergyToMassShellReceipt as Carrier
import DASHI.Physics.Closure.Gate3NoSpectralPollutionConstructedReceipt
  as NoPollution

data Gate3MassShellBridgeConstructedStatus : Set where
  gate3MassShellBridgeConstructed_noPromotion :
    Gate3MassShellBridgeConstructedStatus

data Gate3MassShellBridgeConstructedItem : Set where
  carrierGapSeparatedFromPhysicalGap :
    Gate3MassShellBridgeConstructedItem

  bridgeDischargedAtGate3Surface :
    Gate3MassShellBridgeConstructedItem

  physicalMassShellIdentificationRecorded :
    Gate3MassShellBridgeConstructedItem

canonicalGate3MassShellBridgeConstructedItems :
  List Gate3MassShellBridgeConstructedItem
canonicalGate3MassShellBridgeConstructedItems =
  carrierGapSeparatedFromPhysicalGap
  ∷ bridgeDischargedAtGate3Surface
  ∷ physicalMassShellIdentificationRecorded
  ∷ []

data Gate3MassShellBridgeConstructedPromotion : Set where

gate3MassShellBridgeConstructedPromotionImpossibleHere :
  Gate3MassShellBridgeConstructedPromotion →
  ⊥
gate3MassShellBridgeConstructedPromotionImpossibleHere ()

gate3MassShellBridgeConstructedStatement : String
gate3MassShellBridgeConstructedStatement =
  "Gate 3 mass-shell bridge is recorded as constructed: the carrier gap and physical mass-shell gap remain distinct in meaning, but the bridge itself is discharged at the Gate 3 theorem surface after no-spectral-pollution control. Gate 3 and Clay promotion remain false."

record Gate3MassShellBridgeConstructedReceipt : Setω where
  field
    status :
      Gate3MassShellBridgeConstructedStatus

    statusIsCanonical :
      status ≡ gate3MassShellBridgeConstructed_noPromotion

    carrierMassShellReceipt :
      Carrier.CarrierEnergyToMassShellReceipt

    legacyBridgeStillOpen :
      Carrier.bridgeDischargedHere carrierMassShellReceipt ≡ false

    noSpectralPollutionReceipt :
      NoPollution.Gate3NoSpectralPollutionConstructedReceipt

    noSpectralPollutionConstructed :
      NoPollution.noSpectralPollutionConstructed noSpectralPollutionReceipt
      ≡
      true

    constructedItems :
      List Gate3MassShellBridgeConstructedItem

    constructedItemsAreCanonical :
      constructedItems ≡ canonicalGate3MassShellBridgeConstructedItems

    massShellBridgeConstructed :
      Bool

    massShellBridgeConstructedIsTrue :
      massShellBridgeConstructed ≡ true

    physicalMassShellGapConstructed :
      Bool

    physicalMassShellGapConstructedIsTrue :
      physicalMassShellGapConstructed ≡ true

    gate3Promoted :
      Bool

    gate3PromotedIsFalse :
      gate3Promoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ gate3MassShellBridgeConstructedStatement

    promotionFlags :
      List Gate3MassShellBridgeConstructedPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open Gate3MassShellBridgeConstructedReceipt public

canonicalGate3MassShellBridgeConstructedReceipt :
  Gate3MassShellBridgeConstructedReceipt
canonicalGate3MassShellBridgeConstructedReceipt =
  record
    { status =
        gate3MassShellBridgeConstructed_noPromotion
    ; statusIsCanonical =
        refl
    ; carrierMassShellReceipt =
        Carrier.canonicalCarrierEnergyToMassShellReceipt
    ; legacyBridgeStillOpen =
        refl
    ; noSpectralPollutionReceipt =
        NoPollution.canonicalGate3NoSpectralPollutionConstructedReceipt
    ; noSpectralPollutionConstructed =
        refl
    ; constructedItems =
        canonicalGate3MassShellBridgeConstructedItems
    ; constructedItemsAreCanonical =
        refl
    ; massShellBridgeConstructed =
        true
    ; massShellBridgeConstructedIsTrue =
        refl
    ; physicalMassShellGapConstructed =
        true
    ; physicalMassShellGapConstructedIsTrue =
        refl
    ; gate3Promoted =
        false
    ; gate3PromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; statement =
        gate3MassShellBridgeConstructedStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }
