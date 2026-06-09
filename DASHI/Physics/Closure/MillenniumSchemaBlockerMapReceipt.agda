module DASHI.Physics.Closure.MillenniumSchemaBlockerMapReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MillenniumTowerSchemaReceipt as Schema
import DASHI.Physics.Closure.YMClayUpdatedBlockerReceipt as YM
import DASHI.Physics.Closure.NSH118VsClayGapReceipt as NS

------------------------------------------------------------------------
-- Millennium schema blocker map receipt.
--
-- B3 records the active YM and NS blockers against the shared schema tier.
-- Both active blockers live at T2, the schema lift-attempt tier.  This is
-- a structural location result only; it does not promote either Clay target.

data MillenniumSchemaBlockerMapStatus : Set where
  bothActiveBlockersLocatedAtT2NoClayPromotion :
    MillenniumSchemaBlockerMapStatus

data MillenniumSchemaActiveBlocker : Set where
  hyperbolicFlatLimitUniversalityClass :
    MillenniumSchemaActiveBlocker

  largeDataContractionH118 :
    MillenniumSchemaActiveBlocker

data MillenniumSchemaBlockerMapResult : Set where
  structuralResult :
    MillenniumSchemaBlockerMapResult

data MillenniumSchemaBlockerMapPromotion : Set where

millenniumSchemaBlockerMapPromotionImpossibleHere :
  MillenniumSchemaBlockerMapPromotion →
  ⊥
millenniumSchemaBlockerMapPromotionImpossibleHere ()

canonicalMillenniumSchemaActiveBlockers :
  List MillenniumSchemaActiveBlocker
canonicalMillenniumSchemaActiveBlockers =
  hyperbolicFlatLimitUniversalityClass
  ∷ largeDataContractionH118
  ∷ []

ymActiveBlockerStatement : String
ymActiveBlockerStatement =
  "YM active blocker: hyperbolicFlatLimitUniversalityClass."

nsActiveBlockerStatement : String
nsActiveBlockerStatement =
  "NS active blocker: largeDataContractionH118."

schemaBlockerMapStatement : String
schemaBlockerMapStatement =
  "The Millennium schema locates both active blockers at T2: YM hyperbolicFlatLimitUniversalityClass and NS largeDataContractionH118. This is a structural result only and makes no Clay promotion."

record MillenniumSchemaBlockerMapReceipt : Setω where
  field
    status :
      MillenniumSchemaBlockerMapStatus

    schema :
      Schema.MillenniumTowerSchemaReceipt

    schemaIsCanonical :
      schema ≡ Schema.canonicalMillenniumTowerSchemaReceipt

    schemaTier :
      Schema.MillenniumTowerSchemaStage

    schemaTierIsT2 :
      schemaTier ≡ Schema.T2

    ymUpdatedBlockerReceipt :
      YM.YMClayUpdatedBlockerReceipt

    ymPriorBlockerIsFlatLimitUniversality :
      YM.blocker ymUpdatedBlockerReceipt
      ≡
      YM.hyperbolicToFlatLimitUniversalityClass

    ymPriorClayPromotionFalse :
      YM.clayYangMillsPromoted ymUpdatedBlockerReceipt ≡ false

    nsH118VsClayGapReceipt :
      NS.NSH118VsClayGapReceipt

    nsLargeDataContractionStillMissing :
      NS.missingLargeDataContractionProof nsH118VsClayGapReceipt
      ≡
      true

    nsPriorClayPromotionFalse :
      NS.clayNavierStokesPromoted nsH118VsClayGapReceipt ≡ false

    ymActiveBlocker :
      MillenniumSchemaActiveBlocker

    ymActiveBlockerIsCanonical :
      ymActiveBlocker ≡ hyperbolicFlatLimitUniversalityClass

    ymActiveBlockerTier :
      Schema.MillenniumTowerSchemaStage

    ymActiveBlockerTierIsT2 :
      ymActiveBlockerTier ≡ Schema.T2

    nsActiveBlocker :
      MillenniumSchemaActiveBlocker

    nsActiveBlockerIsCanonical :
      nsActiveBlocker ≡ largeDataContractionH118

    nsActiveBlockerTier :
      Schema.MillenniumTowerSchemaStage

    nsActiveBlockerTierIsT2 :
      nsActiveBlockerTier ≡ Schema.T2

    activeBlockers :
      List MillenniumSchemaActiveBlocker

    activeBlockersAreCanonical :
      activeBlockers ≡ canonicalMillenniumSchemaActiveBlockers

    schemaLocatesBlockerAtSameTier :
      MillenniumSchemaBlockerMapResult

    schemaLocatesBlockerAtSameTierIsStructuralResult :
      schemaLocatesBlockerAtSameTier ≡ structuralResult

    ymStatement :
      String

    ymStatementIsCanonical :
      ymStatement ≡ ymActiveBlockerStatement

    nsStatement :
      String

    nsStatementIsCanonical :
      nsStatement ≡ nsActiveBlockerStatement

    statement :
      String

    statementIsCanonical :
      statement ≡ schemaBlockerMapStatement

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    promotionFlags :
      List MillenniumSchemaBlockerMapPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open MillenniumSchemaBlockerMapReceipt public

canonicalMillenniumSchemaBlockerMapReceipt :
  MillenniumSchemaBlockerMapReceipt
canonicalMillenniumSchemaBlockerMapReceipt =
  record
    { status =
        bothActiveBlockersLocatedAtT2NoClayPromotion
    ; schema =
        Schema.canonicalMillenniumTowerSchemaReceipt
    ; schemaIsCanonical =
        refl
    ; schemaTier =
        Schema.T2
    ; schemaTierIsT2 =
        refl
    ; ymUpdatedBlockerReceipt =
        YM.canonicalYMClayUpdatedBlockerReceipt
    ; ymPriorBlockerIsFlatLimitUniversality =
        refl
    ; ymPriorClayPromotionFalse =
        refl
    ; nsH118VsClayGapReceipt =
        NS.canonicalNSH118VsClayGapReceipt
    ; nsLargeDataContractionStillMissing =
        refl
    ; nsPriorClayPromotionFalse =
        refl
    ; ymActiveBlocker =
        hyperbolicFlatLimitUniversalityClass
    ; ymActiveBlockerIsCanonical =
        refl
    ; ymActiveBlockerTier =
        Schema.T2
    ; ymActiveBlockerTierIsT2 =
        refl
    ; nsActiveBlocker =
        largeDataContractionH118
    ; nsActiveBlockerIsCanonical =
        refl
    ; nsActiveBlockerTier =
        Schema.T2
    ; nsActiveBlockerTierIsT2 =
        refl
    ; activeBlockers =
        canonicalMillenniumSchemaActiveBlockers
    ; activeBlockersAreCanonical =
        refl
    ; schemaLocatesBlockerAtSameTier =
        structuralResult
    ; schemaLocatesBlockerAtSameTierIsStructuralResult =
        refl
    ; ymStatement =
        ymActiveBlockerStatement
    ; ymStatementIsCanonical =
        refl
    ; nsStatement =
        nsActiveBlockerStatement
    ; nsStatementIsCanonical =
        refl
    ; statement =
        schemaBlockerMapStatement
    ; statementIsCanonical =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "YM active blocker = hyperbolicFlatLimitUniversalityClass"
        ∷ "NS active blocker = largeDataContractionH118"
        ∷ "YM active blocker tier = T2"
        ∷ "NS active blocker tier = T2"
        ∷ "schemaLocatesBlockerAtSameTier = structuralResult"
        ∷ "No Yang-Mills, Navier-Stokes, or terminal Clay promotion is made"
        ∷ []
    }

millenniumSchemaYMTierIsT2 :
  ymActiveBlockerTier canonicalMillenniumSchemaBlockerMapReceipt
  ≡
  Schema.T2
millenniumSchemaYMTierIsT2 =
  refl

millenniumSchemaNSTierIsT2 :
  nsActiveBlockerTier canonicalMillenniumSchemaBlockerMapReceipt
  ≡
  Schema.T2
millenniumSchemaNSTierIsT2 =
  refl

millenniumSchemaSameTierStructuralResult :
  schemaLocatesBlockerAtSameTier canonicalMillenniumSchemaBlockerMapReceipt
  ≡
  structuralResult
millenniumSchemaSameTierStructuralResult =
  refl

millenniumSchemaBlockerMapKeepsYangMillsClayFalse :
  clayYangMillsPromoted canonicalMillenniumSchemaBlockerMapReceipt
  ≡
  false
millenniumSchemaBlockerMapKeepsYangMillsClayFalse =
  refl

millenniumSchemaBlockerMapKeepsNavierStokesClayFalse :
  clayNavierStokesPromoted canonicalMillenniumSchemaBlockerMapReceipt
  ≡
  false
millenniumSchemaBlockerMapKeepsNavierStokesClayFalse =
  refl

millenniumSchemaBlockerMapKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalMillenniumSchemaBlockerMapReceipt
  ≡
  false
millenniumSchemaBlockerMapKeepsTerminalFalse =
  refl

millenniumSchemaBlockerMapNoPromotion :
  MillenniumSchemaBlockerMapPromotion →
  ⊥
millenniumSchemaBlockerMapNoPromotion =
  millenniumSchemaBlockerMapPromotionImpossibleHere
