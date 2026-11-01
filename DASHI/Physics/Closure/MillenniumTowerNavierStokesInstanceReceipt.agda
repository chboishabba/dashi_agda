module DASHI.Physics.Closure.MillenniumTowerNavierStokesInstanceReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MillenniumTowerSchemaReceipt as Schema
import DASHI.Physics.Closure.NavierStokesWeakSolutionInterface as NSWeak
import DASHI.Physics.Closure.NavierStokesRegularityTowerReceipt as NSTower
import DASHI.Physics.Closure.ClayMillenniumClosureTargetReceipt as ClayTarget

------------------------------------------------------------------------
-- Navier-Stokes instance of the shared tower schema.

record MillenniumTowerNavierStokesInstanceReceipt : Setω where
  field
    schema :
      Schema.MillenniumTowerSchemaReceipt

    schemaIsCanonical :
      schema ≡ Schema.canonicalMillenniumTowerSchemaReceipt

    weakSolutionInterface :
      NSWeak.NavierStokesWeakSolutionInterfaceReceipt

    regularityTower :
      NSTower.NavierStokesRegularityTowerReceipt

    carrierBKMClosureTarget :
      ClayTarget.CarrierBKMControlTargetReceipt

    carrierUniformBKMControlFalse :
      ClayTarget.uniformVorticityLInfinityControlConstructed
        carrierBKMClosureTarget
      ≡
      false

    carrierContinuumBKMRegularityPassageFalse :
      ClayTarget.continuumBKMRegularityPassageConstructed
        carrierBKMClosureTarget
      ≡
      false

    finiteLerayProjectionRecorded :
      Bool

    finiteLerayProjectionRecordedIsTrue :
      finiteLerayProjectionRecorded ≡ true

    finiteLocalExistenceRecorded :
      Bool

    finiteLocalExistenceRecordedIsTrue :
      finiteLocalExistenceRecorded ≡ true

    finiteEnergyEstimateRecorded :
      Bool

    finiteEnergyEstimateRecordedIsTrue :
      finiteEnergyEstimateRecorded ≡ true

    finiteBKMRecorded :
      Bool

    finiteBKMRecordedIsTrue :
      finiteBKMRecorded ≡ true

    continuumRegularityPromoted :
      Bool

    continuumRegularityPromotedIsFalse :
      continuumRegularityPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    instanceBoundary :
      List String

open MillenniumTowerNavierStokesInstanceReceipt public

canonicalMillenniumTowerNavierStokesInstanceReceipt :
  MillenniumTowerNavierStokesInstanceReceipt
canonicalMillenniumTowerNavierStokesInstanceReceipt =
  record
    { schema =
        Schema.canonicalMillenniumTowerSchemaReceipt
    ; schemaIsCanonical =
        refl
    ; weakSolutionInterface =
        NSWeak.canonicalNavierStokesWeakSolutionInterfaceReceipt
    ; regularityTower =
        NSTower.canonicalNavierStokesRegularityTowerReceipt
    ; carrierBKMClosureTarget =
        ClayTarget.canonicalCarrierBKMControlTargetReceipt
    ; carrierUniformBKMControlFalse =
        refl
    ; carrierContinuumBKMRegularityPassageFalse =
        refl
    ; finiteLerayProjectionRecorded =
        true
    ; finiteLerayProjectionRecordedIsTrue =
        refl
    ; finiteLocalExistenceRecorded =
        true
    ; finiteLocalExistenceRecordedIsTrue =
        refl
    ; finiteEnergyEstimateRecorded =
        true
    ; finiteEnergyEstimateRecordedIsTrue =
        refl
    ; finiteBKMRecorded =
        NSTower.ContinuumBKMAuthorityObligation.finiteDepthBKMReceiptAvailable
          NSTower.canonicalContinuumBKMAuthorityObligation
    ; finiteBKMRecordedIsTrue =
        NSTower.ContinuumBKMAuthorityObligation.finiteDepthBKMReceiptAvailableIsTrue
          NSTower.canonicalContinuumBKMAuthorityObligation
    ; continuumRegularityPromoted =
        NSTower.ContinuumBKMAuthorityObligation.clayRegularityPromotedByBKM
          NSTower.canonicalContinuumBKMAuthorityObligation
    ; continuumRegularityPromotedIsFalse =
        NSTower.ContinuumBKMAuthorityObligation.clayRegularityPromotedByBKMIsFalse
          NSTower.canonicalContinuumBKMAuthorityObligation
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; instanceBoundary =
        "T0 finiteControl: finite weak/Leray-Hopf carrier interface and divergence-free Leray projection are inhabited"
        ∷ "T1 depthFamily: local existence, energy estimate, vorticity, and BKM rungs are recorded at finite depth"
        ∷ "T2 liftAttempt: the finite BKM continuation criterion is recorded as a structural lift attempt"
        ∷ "CarrierBKMControlTargetReceipt records uniform-in-depth enstrophy and vorticity Linfinity control as open hard targets"
        ∷ "T3 continuumObligation: uniform-in-depth enstrophy/BKM passage and continuum regularity remain open"
        ∷ "T4 authorityBoundary: Clay Navier-Stokes regularity promotion remains false"
        ∷ []
    }

millenniumTowerNavierStokesNoClayPromotion :
  clayNavierStokesPromoted canonicalMillenniumTowerNavierStokesInstanceReceipt
  ≡
  false
millenniumTowerNavierStokesNoClayPromotion =
  refl
