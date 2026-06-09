module DASHI.Physics.Closure.MillenniumTowerGRInstanceReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MillenniumTowerSchemaReceipt as Schema
import DASHI.Physics.Closure.ContractedBianchiMatterClosure as Bianchi
import DASHI.Physics.Closure.WaldGRAuthorityReceipt as Wald
import DASHI.Physics.Closure.FriedmannInstabilitySaddleReceipt as Friedmann

------------------------------------------------------------------------
-- GR/Gate 4 instance of the shared tower schema.

record MillenniumTowerGRInstanceReceipt : Setω where
  field
    schema :
      Schema.MillenniumTowerSchemaReceipt

    schemaIsCanonical :
      schema ≡ Schema.canonicalMillenniumTowerSchemaReceipt

    contractedBianchiMatterClosure :
      Bianchi.ContractedBianchiMatterClosureReceipt

    sourcedEinsteinCompatibility :
      Bianchi.SourcedEinsteinCompatibilityReceipt

    waldAuthority :
      Wald.WaldGRAuthorityReceipt

    friedmannInstabilitySaddle :
      Friedmann.FriedmannInstabilitySaddleReceipt

    finiteSourcedEinsteinRecorded :
      Bool

    finiteSourcedEinsteinRecordedIsTrue :
      finiteSourcedEinsteinRecorded ≡ true

    waldAuthorityBoundaryRecorded :
      Bool

    waldAuthorityBoundaryRecordedIsTrue :
      waldAuthorityBoundaryRecorded ≡ true

    continuumGRAuthorityConstructedHere :
      Bool

    continuumGRAuthorityConstructedHereIsFalse :
      continuumGRAuthorityConstructedHere ≡ false

    cosmologyPromoted :
      Bool

    cosmologyPromotedIsFalse :
      cosmologyPromoted ≡ false

    grPromotion :
      Bool

    grPromotionIsFalse :
      grPromotion ≡ false

    instanceBoundary :
      List String

open MillenniumTowerGRInstanceReceipt public

canonicalMillenniumTowerGRInstanceReceipt :
  MillenniumTowerGRInstanceReceipt
canonicalMillenniumTowerGRInstanceReceipt =
  record
    { schema =
        Schema.canonicalMillenniumTowerSchemaReceipt
    ; schemaIsCanonical =
        refl
    ; contractedBianchiMatterClosure =
        Bianchi.canonicalContractedBianchiMatterClosureReceipt
    ; sourcedEinsteinCompatibility =
        Bianchi.canonicalSourcedEinsteinCompatibilityReceipt
    ; waldAuthority =
        Wald.canonicalWaldGRAuthorityReceipt
    ; friedmannInstabilitySaddle =
        Friedmann.canonicalFriedmannInstabilitySaddleReceipt
    ; finiteSourcedEinsteinRecorded =
        Bianchi.SourcedEinsteinCompatibilityReceipt.finiteCompatibilityRecorded
          Bianchi.canonicalSourcedEinsteinCompatibilityReceipt
    ; finiteSourcedEinsteinRecordedIsTrue =
        Bianchi.SourcedEinsteinCompatibilityReceipt.finiteCompatibilityRecordedIsTrue
          Bianchi.canonicalSourcedEinsteinCompatibilityReceipt
    ; waldAuthorityBoundaryRecorded =
        true
    ; waldAuthorityBoundaryRecordedIsTrue =
        refl
    ; continuumGRAuthorityConstructedHere =
        Wald.WaldGRAuthorityReceipt.acceptedContinuumAuthorityConstructedHere
          Wald.canonicalWaldGRAuthorityReceipt
    ; continuumGRAuthorityConstructedHereIsFalse =
        Wald.WaldGRAuthorityReceipt.acceptedContinuumAuthorityConstructedHereIsFalse
          Wald.canonicalWaldGRAuthorityReceipt
    ; cosmologyPromoted =
        Friedmann.FriedmannInstabilitySaddleReceipt.cosmologyPromoted
          Friedmann.canonicalFriedmannInstabilitySaddleReceipt
    ; cosmologyPromotedIsFalse =
        Friedmann.FriedmannInstabilitySaddleReceipt.cosmologyPromotedIsFalse
          Friedmann.canonicalFriedmannInstabilitySaddleReceipt
    ; grPromotion =
        false
    ; grPromotionIsFalse =
        refl
    ; instanceBoundary =
        "T0 finiteControl: contracted-Bianchi matter closure and finite sourced-Einstein compatibility are recorded"
        ∷ "T1 depthFamily: Gate 4 finite carrier geometry is consumed through the existing Bianchi/sourced-Einstein receipts"
        ∷ "T2 liftAttempt: Wald authority and Friedmann-instability saddle receipts stage the continuum bridge"
        ∷ "T3 continuumObligation: continuum Levi-Civita/stress-energy authority remains fail-closed"
        ∷ "T4 authorityBoundary: no dark-energy, LCDM-falsification, cosmology, or GR promotion is introduced"
        ∷ []
    }

millenniumTowerGRNoPromotion :
  grPromotion canonicalMillenniumTowerGRInstanceReceipt
  ≡
  false
millenniumTowerGRNoPromotion =
  refl
