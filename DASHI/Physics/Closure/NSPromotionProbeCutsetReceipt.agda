module DASHI.Physics.Closure.NSPromotionProbeCutsetReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Fail-closed receipt for the NS root probe cutset.
--
-- This module intentionally does not import the probe itself.  It records
-- the current probe module path, the first strengthened blocker name, and the
-- interpretation that the main build remains green while the probe stays red.

data NSPromotionProbeCutsetStatus : Set where
  nsPromotionProbeCutsetRecorded_noPromotion :
    NSPromotionProbeCutsetStatus

data NSPromotionProbeCutsetItem : Set where
  probeModulePathRecorded :
    NSPromotionProbeCutsetItem

  firstStrengthenedBlockerRecorded :
    NSPromotionProbeCutsetItem

  mainBuildGreenRecorded :
    NSPromotionProbeCutsetItem

  probeIntentionallyRedRecorded :
    NSPromotionProbeCutsetItem

  interpretationRecorded :
    NSPromotionProbeCutsetItem

canonicalNSPromotionProbeCutsetItems :
  List NSPromotionProbeCutsetItem
canonicalNSPromotionProbeCutsetItems =
  probeModulePathRecorded
  ∷ firstStrengthenedBlockerRecorded
  ∷ mainBuildGreenRecorded
  ∷ probeIntentionallyRedRecorded
  ∷ interpretationRecorded
  ∷ []

canonicalNSPromotionProbeModulePath : String
canonicalNSPromotionProbeModulePath =
  "DASHI.Physics.Probes.NSPromotionProbe"

canonicalFirstStrengthenedBlockerName : String
canonicalFirstStrengthenedBlockerName =
  "enstrophyPassageClosed"

nsPromotionProbeCutsetInterpretation : String
nsPromotionProbeCutsetInterpretation =
  "The main build stays green while the probe is intentionally red."

record NSPromotionProbeCutsetReceipt : Setω where
  field
    status :
      NSPromotionProbeCutsetStatus

    statusIsCanonical :
      status ≡ nsPromotionProbeCutsetRecorded_noPromotion

    items :
      List NSPromotionProbeCutsetItem

    itemsAreCanonical :
      items ≡ canonicalNSPromotionProbeCutsetItems

    probeModulePath :
      String

    probeModulePathIsCanonical :
      probeModulePath ≡ canonicalNSPromotionProbeModulePath

    firstStrengthenedBlockerName :
      String

    firstStrengthenedBlockerNameIsCanonical :
      firstStrengthenedBlockerName ≡ canonicalFirstStrengthenedBlockerName

    mainBuildStaysGreen :
      Bool

    mainBuildStaysGreenIsTrue :
      mainBuildStaysGreen ≡ true

    probeIntentionallyRed :
      Bool

    probeIntentionallyRedIsTrue :
      probeIntentionallyRed ≡ true

    interpretation :
      String

    interpretationIsCanonical :
      interpretation ≡ nsPromotionProbeCutsetInterpretation

    receiptBoundary :
      List String

open NSPromotionProbeCutsetReceipt public

canonicalNSPromotionProbeCutsetReceipt :
  NSPromotionProbeCutsetReceipt
canonicalNSPromotionProbeCutsetReceipt =
  record
    { status =
        nsPromotionProbeCutsetRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; items =
        canonicalNSPromotionProbeCutsetItems
    ; itemsAreCanonical =
        refl
    ; probeModulePath =
        canonicalNSPromotionProbeModulePath
    ; probeModulePathIsCanonical =
        refl
    ; firstStrengthenedBlockerName =
        canonicalFirstStrengthenedBlockerName
    ; firstStrengthenedBlockerNameIsCanonical =
        refl
    ; mainBuildStaysGreen =
        true
    ; mainBuildStaysGreenIsTrue =
        refl
    ; probeIntentionallyRed =
        true
    ; probeIntentionallyRedIsTrue =
        refl
    ; interpretation =
        nsPromotionProbeCutsetInterpretation
    ; interpretationIsCanonical =
        refl
    ; receiptBoundary =
        "Probe module: DASHI.Physics.Probes.NSPromotionProbe"
        ∷ "First strengthened blocker: enstrophyPassageClosed"
        ∷ "Main build stays green; the probe is intentionally red"
        ∷ []
    }

canonicalReceipt : NSPromotionProbeCutsetReceipt
canonicalReceipt =
  canonicalNSPromotionProbeCutsetReceipt

