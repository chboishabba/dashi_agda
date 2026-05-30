module DASHI.Physics.Closure.NSRegularityGapReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClayMillenniumClosureTargetReceipt as Clay
import DASHI.Physics.Closure.NavierStokesRegularityTowerReceipt as Tower

data NSRegularityGapStatus : Set where
  finiteDepthControlsRecordedContinuumRegularityOpen :
    NSRegularityGapStatus

data NSRegularityGapItem : Set where
  finiteDepthEnergyEstimate :
    NSRegularityGapItem
  finiteDepthEnstrophyControl :
    NSRegularityGapItem
  finiteDepthVorticityEquation :
    NSRegularityGapItem
  missingUniformBKMControl :
    NSRegularityGapItem
  missingContinuumSmoothRegularity :
    NSRegularityGapItem

canonicalNSRegularityGapItems :
  List NSRegularityGapItem
canonicalNSRegularityGapItems =
  finiteDepthEnergyEstimate
  ∷ finiteDepthEnstrophyControl
  ∷ finiteDepthVorticityEquation
  ∷ missingUniformBKMControl
  ∷ missingContinuumSmoothRegularity
  ∷ []

nsRegularityGapStatement : String
nsRegularityGapStatement =
  "Finite-depth NS energy, enstrophy, vorticity, and BKM rungs are recorded, but uniform vorticity control, continuum BKM passage, global smooth regularity, and Clay closure remain open."

record NSRegularityGapReceipt : Setω where
  field
    status :
      NSRegularityGapStatus

    regularityTower :
      Tower.NavierStokesRegularityTowerReceipt

    towerContinuumLiftFalse :
      Tower.continuumRegularityLiftConstructed regularityTower ≡ false

    towerClayFalse :
      Tower.continuumClayNavierStokesPromoted regularityTower ≡ false

    clayTargetReceipt :
      Clay.CarrierBKMControlTargetReceipt

    uniformVorticityControlFalse :
      Clay.uniformVorticityLInfinityControlConstructed
        clayTargetReceipt
      ≡
      false

    continuumBKMRegularityPassageFalse :
      Clay.continuumBKMRegularityPassageConstructed
        clayTargetReceipt
      ≡
      false

    gapItems :
      List NSRegularityGapItem

    gapItemsAreCanonical :
      gapItems ≡ canonicalNSRegularityGapItems

    energyRungRecorded :
      Bool

    energyRungRecordedIsTrue :
      energyRungRecorded ≡ true

    vorticityRungRecorded :
      Bool

    vorticityRungRecordedIsTrue :
      vorticityRungRecorded ≡ true

    bkmRungRecorded :
      Bool

    bkmRungRecordedIsTrue :
      bkmRungRecorded ≡ true

    finiteDepthRegularityRungsRecorded :
      Bool

    finiteDepthRegularityRungsRecordedIsTrue :
      finiteDepthRegularityRungsRecorded ≡ true

    globalSmoothRegularityProved :
      Bool

    globalSmoothRegularityProvedIsFalse :
      globalSmoothRegularityProved ≡ false

    bkmVorticityControlClosed :
      Bool

    bkmVorticityControlClosedIsFalse :
      bkmVorticityControlClosed ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsRegularityGapStatement

    receiptBoundary :
      List String

open NSRegularityGapReceipt public

canonicalNSRegularityGapReceipt :
  NSRegularityGapReceipt
canonicalNSRegularityGapReceipt =
  record
    { status =
        finiteDepthControlsRecordedContinuumRegularityOpen
    ; regularityTower =
        Tower.canonicalNavierStokesRegularityTowerReceipt
    ; towerContinuumLiftFalse =
        refl
    ; towerClayFalse =
        refl
    ; clayTargetReceipt =
        Clay.canonicalCarrierBKMControlTargetReceipt
    ; uniformVorticityControlFalse =
        refl
    ; continuumBKMRegularityPassageFalse =
        refl
    ; gapItems =
        canonicalNSRegularityGapItems
    ; gapItemsAreCanonical =
        refl
    ; energyRungRecorded =
        true
    ; energyRungRecordedIsTrue =
        refl
    ; vorticityRungRecorded =
        true
    ; vorticityRungRecordedIsTrue =
        refl
    ; bkmRungRecorded =
        true
    ; bkmRungRecordedIsTrue =
        refl
    ; finiteDepthRegularityRungsRecorded =
        true
    ; finiteDepthRegularityRungsRecordedIsTrue =
        refl
    ; globalSmoothRegularityProved =
        false
    ; globalSmoothRegularityProvedIsFalse =
        refl
    ; bkmVorticityControlClosed =
        false
    ; bkmVorticityControlClosedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        nsRegularityGapStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Finite-depth rungs are recorded by the tower at every Nat depth"
        ∷ "Uniform vorticity Linfinity control is not constructed"
        ∷ "Continuum BKM passage and global smooth regularity remain false"
        ∷ "Clay Navier-Stokes promotion remains false"
        ∷ []
    }

nsRegularityGapKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSRegularityGapReceipt ≡ false
nsRegularityGapKeepsClayFalse =
  refl
