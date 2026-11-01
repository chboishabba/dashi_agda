module DASHI.Physics.Closure.NavierStokesTowerSchemaInstance where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MillenniumTowerSchemaReceipt as Schema
import DASHI.Physics.Closure.NavierStokesRegularityTowerReceipt as NS
import DASHI.Physics.Closure.NavierStokesWeakSolutionInterface as NSWeak

------------------------------------------------------------------------
-- Navier-Stokes instance of the shared tower schema.
--
-- This adapter only maps the existing finite weak-solution interface and
-- regularity tower receipt into the shared five-stage schema.  It preserves
-- the existing boundary: continuum regularity, Clay promotion, and terminal
-- promotion remain false.

data NavierStokesTowerSchemaInstanceStatus : Set where
  navierStokesFiniteWeakTowerMappedContinuumRegularityFalse :
    NavierStokesTowerSchemaInstanceStatus

record NavierStokesTowerSchemaInstance : Setω where
  field
    status :
      NavierStokesTowerSchemaInstanceStatus

    schemaReceipt :
      Schema.MillenniumTowerSchemaReceipt

    schemaReceiptIsCanonical :
      schemaReceipt ≡ Schema.canonicalMillenniumTowerSchemaReceipt

    schemaStagesAreCanonical :
      Schema.stages schemaReceipt
      ≡
      Schema.canonicalMillenniumTowerSchemaStages

    schemaContinuumObligationDischargedIsFalse :
      Schema.continuumObligationDischarged schemaReceipt ≡ false

    schemaClayPromotionIsFalse :
      Schema.promotionToClay schemaReceipt ≡ false

    schemaTerminalPromotionIsFalse :
      Schema.terminalPromotion schemaReceipt ≡ false

    weakSolutionInterfaceReceipt :
      NSWeak.NavierStokesWeakSolutionInterfaceReceipt

    weakSolutionInterfaceReceiptIsCanonical :
      weakSolutionInterfaceReceipt
      ≡
      NSWeak.canonicalNavierStokesWeakSolutionInterfaceReceipt

    weakFormulationRecorded :
      NSWeak.NavierStokesWeakSolutionInterfaceReceipt.carrierWeakFormulationRecorded
        weakSolutionInterfaceReceipt
      ≡
      true

    weakInterfaceContinuumRegularityPromotedIsFalse :
      NSWeak.NavierStokesWeakSolutionInterfaceReceipt.continuumRegularityPromoted
        weakSolutionInterfaceReceipt
      ≡
      false

    regularityTowerReceiptSelectedCanonical :
      Bool

    regularityTowerReceiptSelectedCanonicalIsTrue :
      regularityTowerReceiptSelectedCanonical ≡ true

    canonicalFiniteVorticityControlRecordedAtDepthZero :
      NS.finiteDepthVorticityControlRecordedAtDepthZero
        NS.canonicalNavierStokesRegularityTowerReceipt
      ≡
      refl

    canonicalFiniteEnergyEstimateRecordedAtDepthZero :
      NS.finiteDepthL2EnergyEstimateRecordedAtDepthZero
        NS.canonicalNavierStokesRegularityTowerReceipt
      ≡
      refl

    canonicalContinuumRegularityLiftConstructedIsFalse :
      NS.continuumRegularityLiftConstructed
        NS.canonicalNavierStokesRegularityTowerReceipt
      ≡
      false

    canonicalContinuumClayNavierStokesPromotedIsFalse :
      NS.continuumClayNavierStokesPromoted
        NS.canonicalNavierStokesRegularityTowerReceipt
      ≡
      false

    instancePromoted :
      Bool

    instancePromotedIsFalse :
      instancePromoted ≡ false

    mappingBoundary :
      List String

open NavierStokesTowerSchemaInstance public

canonicalNavierStokesTowerSchemaInstance :
  NavierStokesTowerSchemaInstance
canonicalNavierStokesTowerSchemaInstance =
  record
    { status =
        navierStokesFiniteWeakTowerMappedContinuumRegularityFalse
    ; schemaReceipt =
        Schema.canonicalMillenniumTowerSchemaReceipt
    ; schemaReceiptIsCanonical =
        refl
    ; schemaStagesAreCanonical =
        refl
    ; schemaContinuumObligationDischargedIsFalse =
        refl
    ; schemaClayPromotionIsFalse =
        refl
    ; schemaTerminalPromotionIsFalse =
        refl
    ; weakSolutionInterfaceReceipt =
        NSWeak.canonicalNavierStokesWeakSolutionInterfaceReceipt
    ; weakSolutionInterfaceReceiptIsCanonical =
        refl
    ; weakFormulationRecorded =
        refl
    ; weakInterfaceContinuumRegularityPromotedIsFalse =
        refl
    ; regularityTowerReceiptSelectedCanonical =
        true
    ; regularityTowerReceiptSelectedCanonicalIsTrue =
        refl
    ; canonicalFiniteVorticityControlRecordedAtDepthZero =
        refl
    ; canonicalFiniteEnergyEstimateRecordedAtDepthZero =
        refl
    ; canonicalContinuumRegularityLiftConstructedIsFalse =
        NS.navierStokesRegularityTowerKeepsContinuumLiftFalse
    ; canonicalContinuumClayNavierStokesPromotedIsFalse =
        NS.navierStokesRegularityTowerKeepsClayFalse
    ; instancePromoted =
        false
    ; instancePromotedIsFalse =
        refl
    ; mappingBoundary =
        "Schema T0/T1/T2 consume finite weak formulation, finite depth tower, and lift-attempt bookkeeping"
        ∷ "The Navier-Stokes weak-solution interface is canonical and carrier-level only"
        ∷ "The regularity tower supplies finite vorticity and energy rungs at depth zero"
        ∷ "Continuum regularity lift, Clay promotion, terminal promotion, and this schema instance promotion remain false"
        ∷ []
    }

navierStokesTowerSchemaContinuumRegularityFalse :
  NS.continuumRegularityLiftConstructed
    NS.canonicalNavierStokesRegularityTowerReceipt
  ≡
  false
navierStokesTowerSchemaContinuumRegularityFalse =
  refl

navierStokesTowerSchemaInstancePromotedFalse :
  instancePromoted canonicalNavierStokesTowerSchemaInstance
  ≡
  false
navierStokesTowerSchemaInstancePromotedFalse =
  refl
