module DASHI.Physics.Closure.GRGate4TowerSchemaInstance where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ContractedBianchiMatterClosure as BianchiMatter
import DASHI.Physics.Closure.FriedmannInstabilitySaddleReceipt as Friedmann
import DASHI.Physics.Closure.MillenniumTowerSchemaReceipt as Schema
import DASHI.Physics.Closure.WaldGRAuthorityReceipt as Wald

------------------------------------------------------------------------
-- Gate 4 GR/cosmology instance of the shared tower schema.
--
-- This adapter maps the contracted-Bianchi, Wald authority, and Friedmann
-- instability receipts into the common schema while preserving the existing
-- fail-closed Gate 4 boundary.  It records authority and finite compatibility
-- intake only; GR and cosmology promotion remain false.

data GRGate4TowerSchemaInstanceStatus : Set where
  grGate4BianchiWaldFriedmannMappedPromotionFalse :
    GRGate4TowerSchemaInstanceStatus

record GRGate4TowerSchemaInstance : Setω where
  field
    status :
      GRGate4TowerSchemaInstanceStatus

    schemaReceipt :
      Schema.MillenniumTowerSchemaReceipt

    schemaReceiptIsCanonical :
      schemaReceipt ≡ Schema.canonicalMillenniumTowerSchemaReceipt

    schemaContinuumObligationDischargedIsFalse :
      Schema.continuumObligationDischarged schemaReceipt ≡ false

    schemaFullUnificationIsFalse :
      Schema.fullUnification schemaReceipt ≡ false

    contractedBianchiMatterClosureSelectedCanonical :
      Bool

    contractedBianchiMatterClosureSelectedCanonicalIsTrue :
      contractedBianchiMatterClosureSelectedCanonical ≡ true

    contractedBianchiClosurePromotedIsFalse :
      BianchiMatter.closurePromoted
        BianchiMatter.canonicalContractedBianchiMatterClosureReceipt
      ≡
      false

    sourcedEinsteinCompatibilitySelectedCanonical :
      Bool

    sourcedEinsteinCompatibilitySelectedCanonicalIsTrue :
      sourcedEinsteinCompatibilitySelectedCanonical ≡ true

    finiteSourcedEinsteinCompatibilityRecorded :
      BianchiMatter.SourcedEinsteinCompatibilityReceipt.finiteCompatibilityRecorded
        BianchiMatter.canonicalSourcedEinsteinCompatibilityReceipt
      ≡
      true

    sourcedEinsteinCompatibilityPromotedIsFalse :
      BianchiMatter.SourcedEinsteinCompatibilityReceipt.sourcedEinsteinCompatibilityPromoted
        BianchiMatter.canonicalSourcedEinsteinCompatibilityReceipt
      ≡
      false

    waldGRAuthoritySelectedCanonical :
      Bool

    waldGRAuthoritySelectedCanonicalIsTrue :
      waldGRAuthoritySelectedCanonical ≡ true

    waldContinuumLeviCivitaPromotedIsFalse :
      Wald.WaldGRAuthorityReceipt.continuumLeviCivitaPromoted
        Wald.canonicalWaldGRAuthorityReceipt
      ≡
      false

    waldContinuumSourcedEinsteinPromotedIsFalse :
      Wald.WaldGRAuthorityReceipt.continuumSourcedEinsteinPromoted
        Wald.canonicalWaldGRAuthorityReceipt
      ≡
      false

    friedmannInstabilityAuthoritySelectedCanonical :
      Bool

    friedmannInstabilityAuthoritySelectedCanonicalIsTrue :
      friedmannInstabilityAuthoritySelectedCanonical ≡ true

    friedmannSaddlePointAuthorityBacked :
      Friedmann.FriedmannInstabilitySaddleReceipt.friedmannUnstableSaddlePoint
        Friedmann.canonicalFriedmannInstabilitySaddleReceipt
      ≡
      true

    friedmannCosmologyPromotedIsFalse :
      Friedmann.FriedmannInstabilitySaddleReceipt.cosmologyPromoted
        Friedmann.canonicalFriedmannInstabilitySaddleReceipt
      ≡
      false

    friedmannDarkEnergyRemovedIsFalse :
      Friedmann.FriedmannInstabilitySaddleReceipt.darkEnergyRemoved
        Friedmann.canonicalFriedmannInstabilitySaddleReceipt
      ≡
      false

    gate4GRPromoted :
      Bool

    gate4GRPromotedIsFalse :
      gate4GRPromoted ≡ false

    cosmologyPromoted :
      Bool

    cosmologyPromotedIsFalse :
      cosmologyPromoted ≡ false

    mappingBoundary :
      List String

open GRGate4TowerSchemaInstance public

canonicalGRGate4TowerSchemaInstance :
  GRGate4TowerSchemaInstance
canonicalGRGate4TowerSchemaInstance =
  record
    { status =
        grGate4BianchiWaldFriedmannMappedPromotionFalse
    ; schemaReceipt =
        Schema.canonicalMillenniumTowerSchemaReceipt
    ; schemaReceiptIsCanonical =
        refl
    ; schemaContinuumObligationDischargedIsFalse =
        refl
    ; schemaFullUnificationIsFalse =
        refl
    ; contractedBianchiMatterClosureSelectedCanonical =
        true
    ; contractedBianchiMatterClosureSelectedCanonicalIsTrue =
        refl
    ; contractedBianchiClosurePromotedIsFalse =
        BianchiMatter.contractedBianchiMatterClosureRemainsFailClosed
    ; sourcedEinsteinCompatibilitySelectedCanonical =
        true
    ; sourcedEinsteinCompatibilitySelectedCanonicalIsTrue =
        refl
    ; finiteSourcedEinsteinCompatibilityRecorded =
        BianchiMatter.sourcedEinsteinCompatibilityFiniteRecorded
    ; sourcedEinsteinCompatibilityPromotedIsFalse =
        BianchiMatter.sourcedEinsteinCompatibilityStillFailClosed
    ; waldGRAuthoritySelectedCanonical =
        true
    ; waldGRAuthoritySelectedCanonicalIsTrue =
        refl
    ; waldContinuumLeviCivitaPromotedIsFalse =
        Wald.waldGRAuthorityContinuumLeviCivitaStillFailClosed
    ; waldContinuumSourcedEinsteinPromotedIsFalse =
        Wald.waldGRAuthorityContinuumSourcedEinsteinStillFailClosed
    ; friedmannInstabilityAuthoritySelectedCanonical =
        true
    ; friedmannInstabilityAuthoritySelectedCanonicalIsTrue =
        refl
    ; friedmannSaddlePointAuthorityBacked =
        Friedmann.friedmannInstabilitySaddlePointAuthorityBacked
    ; friedmannCosmologyPromotedIsFalse =
        Friedmann.friedmannInstabilityCosmologyPromotionStillFailClosed
    ; friedmannDarkEnergyRemovedIsFalse =
        Friedmann.friedmannInstabilityDoesNotRemoveDarkEnergyHere
    ; gate4GRPromoted =
        false
    ; gate4GRPromotedIsFalse =
        refl
    ; cosmologyPromoted =
        false
    ; cosmologyPromotedIsFalse =
        refl
    ; mappingBoundary =
        "Gate 4 schema instance consumes contracted-Bianchi matter closure, finite sourced-Einstein compatibility, and Wald authority receipts"
        ∷ "The Friedmann instability receipt is threaded only as an external cosmology authority boundary"
        ∷ "Continuum Levi-Civita, sourced Einstein, Gate 4 GR promotion, cosmology promotion, dark-energy removal, and full unification remain false"
        ∷ []
    }

grGate4TowerSchemaGRPromotionFalse :
  gate4GRPromoted canonicalGRGate4TowerSchemaInstance
  ≡
  false
grGate4TowerSchemaGRPromotionFalse =
  refl

grGate4TowerSchemaCosmologyPromotionFalse :
  cosmologyPromoted canonicalGRGate4TowerSchemaInstance
  ≡
  false
grGate4TowerSchemaCosmologyPromotionFalse =
  refl
