module DASHI.Biology.Physical.Biological369CubicalOpenSignedChargeExact where

------------------------------------------------------------------------
-- Exact open-system signed ionic charge ledger on the ORIGINAL
-- 3×3×3 cubical voxel carrier, using the six actual exterior faces.
--
-- Internal native 54-bond cation/anion transport is owned by
-- BiologicalSignedIonicSharedGridExact. This module handles
-- environmental ionic charge SOURCE/SINKS separately, using
-- ORIGINAL OnFace-verified injection/outflow for EACH charge sign.
--
-- The resulting integer signed-charge law contains precisely the
-- actual injected and removed cations/anions. It is not an assumed
-- PNP field equation, measured current density or local Gauss law.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Data.Vec.Base as V
import Data.Integer.Base as Int
import DASHI.Biology.Physical.Biological369CubicalBoundaryMaterialExact as Faces
import DASHI.Biology.Physical.BiologicalSignedIonicSharedGridExact as Ionic

record OriginalCubicalOpenIonSystem : Set where
  constructor original-cubical-open-ion-system
  field
    initialIons : Ionic.TwoIonSharedGrid
    positiveOuterFaceEvents : List Faces.OriginalFaceExchange
    negativeOuterFaceEvents : List Faces.OriginalFaceExchange

open OriginalCubicalOpenIonSystem public

positiveResult :
  OriginalCubicalOpenIonSystem → Faces.BoundaryHistoryResult
positiveResult system =
  Faces.runOriginalBoundaryExchange
    (positiveOuterFaceEvents system)
    (Ionic.positiveIon (initialIons system))

negativeResult :
  OriginalCubicalOpenIonSystem → Faces.BoundaryHistoryResult
negativeResult system =
  Faces.runOriginalBoundaryExchange
    (negativeOuterFaceEvents system)
    (Ionic.negativeIon (initialIons system))

positiveOpenMaterialBalance :
  (system : OriginalCubicalOpenIonSystem) →
  V.sum (Faces.finalMaterial (positiveResult system))
    + Faces.totalExternalOutput (positiveResult system)
    ≡ Ionic.positiveTotal (initialIons system)
      + Faces.totalExternalInput (positiveResult system)
positiveOpenMaterialBalance system =
  Faces.allOriginalBoundaryExchangeHistoriesBalance
    (positiveOuterFaceEvents system)
    (Ionic.positiveIon (initialIons system))

negativeOpenMaterialBalance :
  (system : OriginalCubicalOpenIonSystem) →
  V.sum (Faces.finalMaterial (negativeResult system))
    + Faces.totalExternalOutput (negativeResult system)
    ≡ Ionic.negativeTotal (initialIons system)
      + Faces.totalExternalInput (negativeResult system)
negativeOpenMaterialBalance system =
  Faces.allOriginalBoundaryExchangeHistoriesBalance
    (negativeOuterFaceEvents system)
    (Ionic.negativeIon (initialIons system))

-- The same selected exact integer signed-charge representation
-- from the existing original internal-ionic owner is consumed.
openChargeAfterPlusOutputs :
  OriginalCubicalOpenIonSystem → Int.ℤ
openChargeAfterPlusOutputs system =
  Ionic.integerSignedCharge
    (V.sum (Faces.finalMaterial (positiveResult system))
      + Faces.totalExternalOutput (positiveResult system))
    (V.sum (Faces.finalMaterial (negativeResult system))
      + Faces.totalExternalOutput (negativeResult system))

openChargeBeforePlusInputs :
  OriginalCubicalOpenIonSystem → Int.ℤ
openChargeBeforePlusInputs system =
  Ionic.integerSignedCharge
    (Ionic.positiveTotal (initialIons system)
      + Faces.totalExternalInput (positiveResult system))
    (Ionic.negativeTotal (initialIons system)
      + Faces.totalExternalInput (negativeResult system))

nativeSignedChargeWithEnvironmentalSourcesAndSinks :
  (system : OriginalCubicalOpenIonSystem) →
  openChargeAfterPlusOutputs system
    ≡ openChargeBeforePlusInputs system
nativeSignedChargeWithEnvironmentalSourcesAndSinks system =
  cong₂ Ionic.integerSignedCharge
    (positiveOpenMaterialBalance system)
    (negativeOpenMaterialBalance system)

-- Concrete native 3D exterior-face receipt; zero influx and outflow
-- otherwise. It uses the actual source-owned OnFace witness and does
-- not invent an experimental concentration or ionic mobility.
selectedNativeOpenIonicFixture : OriginalCubicalOpenIonSystem
selectedNativeOpenIonicFixture =
  original-cubical-open-ion-system
    (Ionic.two-ion-shared-grid
      (V.replicate 27 0)
      (V.replicate 27 0))
    (Faces.addAtOuterFace Faces.selectedOriginalBoundaryEvent ∷ [])
    []

selectedNativeOpenIonicFixtureBalances :
  openChargeAfterPlusOutputs selectedNativeOpenIonicFixture
    ≡ openChargeBeforePlusInputs selectedNativeOpenIonicFixture
selectedNativeOpenIonicFixtureBalances =
  nativeSignedChargeWithEnvironmentalSourcesAndSinks
    selectedNativeOpenIonicFixture

------------------------------------------------------------------------
-- COMPOSITION: native closed internal ion transport may precede
-- ANY source-paid external face exchange. Original signed charge
-- then differs from its prior physical inventory only by explicit
-- face-indexed positive/negative environmental inputs and outputs.
------------------------------------------------------------------------

afterNativeInternalTransport :
  List Ionic.IonMovement →
  OriginalCubicalOpenIonSystem →
  OriginalCubicalOpenIonSystem
afterNativeInternalTransport actions system =
  original-cubical-open-ion-system
    (Ionic.runIonHistory actions (initialIons system))
    (positiveOuterFaceEvents system)
    (negativeOuterFaceEvents system)

originalFullSpatialOpenSignedChargeBalance :
  (actions : List Ionic.IonMovement)
  (system : OriginalCubicalOpenIonSystem) →
  openChargeAfterPlusOutputs (afterNativeInternalTransport actions system)
    ≡
  Ionic.integerSignedCharge
    (Ionic.positiveTotal (initialIons system)
      + Faces.totalExternalInput
          (positiveResult (afterNativeInternalTransport actions system)))
    (Ionic.negativeTotal (initialIons system)
      + Faces.totalExternalInput
          (negativeResult (afterNativeInternalTransport actions system)))
originalFullSpatialOpenSignedChargeBalance actions system =
  trans
    (nativeSignedChargeWithEnvironmentalSourcesAndSinks
      (afterNativeInternalTransport actions system))
    (cong₂ Ionic.integerSignedCharge
      (cong
        (λ n → n + Faces.totalExternalInput
          (positiveResult (afterNativeInternalTransport actions system)))
        (Ionic.allIonHistoriesPreservePositiveTotal actions
          (initialIons system)))
      (cong
        (λ n → n + Faces.totalExternalInput
          (negativeResult (afterNativeInternalTransport actions system)))
        (Ionic.allIonHistoriesPreserveNegativeTotal actions
          (initialIons system))))


------------------------------------------------------------------------
-- TRUE SIGNED LOCAL NATIVE CURRENT: the original directed geometric
-- bond and its executed 0/1 moved quantum select the current. This
-- combines per-voxel cation (+) and anion (-) contributions without
-- interpreting a global unsigned magnitude as signed charge.
--
-- Current equation at one actual bond event, in an integer ledger:
-- Q_after + signedOutgoing = Q_before + signedIncoming.
-- This is exact finite-state transport, not measured PNP kinetics.
------------------------------------------------------------------------

import Data.Fin.Base as F
import DASHI.Biology.Physical.BiologicalOriginal54BondSharedVectorExact as Native

data OriginalSignedNativeBondAction : Set where
  moveCation : Native.OriginalDirectedNativeBond →
    OriginalSignedNativeBondAction
  moveAnion : Native.OriginalDirectedNativeBond →
    OriginalSignedNativeBondAction

signedNativeBond :
  OriginalSignedNativeBondAction → Native.OriginalDirectedNativeBond
signedNativeBond (moveCation bond) = bond
signedNativeBond (moveAnion bond) = bond

applyOriginalSignedNativeBond :
  OriginalSignedNativeBondAction →
  Ionic.TwoIonSharedGrid → Ionic.TwoIonSharedGrid
applyOriginalSignedNativeBond (moveCation bond)
  (Ionic.two-ion-shared-grid pos neg) =
  Ionic.two-ion-shared-grid (Native.applyNativeDirectedBond bond pos) neg
applyOriginalSignedNativeBond (moveAnion bond)
  (Ionic.two-ion-shared-grid pos neg) =
  Ionic.two-ion-shared-grid pos (Native.applyNativeDirectedBond bond neg)

positiveNativeOut :
  (action : OriginalSignedNativeBondAction)
  (state : Ionic.TwoIonSharedGrid) (observer : F.Fin 27) →
  Native.NativeVoxelRole (signedNativeBond action) observer → Nat
positiveNativeOut (moveCation bond) state observer role =
  Native.nativeRoleOutgoing bond (Ionic.positiveIon state) observer role
positiveNativeOut (moveAnion bond) state observer role = 0

negativeNativeOut :
  (action : OriginalSignedNativeBondAction)
  (state : Ionic.TwoIonSharedGrid) (observer : F.Fin 27) →
  Native.NativeVoxelRole (signedNativeBond action) observer → Nat
negativeNativeOut (moveCation bond) state observer role = 0
negativeNativeOut (moveAnion bond) state observer role =
  Native.nativeRoleOutgoing bond (Ionic.negativeIon state) observer role

positiveNativeIn :
  (action : OriginalSignedNativeBondAction)
  (state : Ionic.TwoIonSharedGrid) (observer : F.Fin 27) →
  Native.NativeVoxelRole (signedNativeBond action) observer → Nat
positiveNativeIn (moveCation bond) state observer role =
  Native.nativeRoleIncoming bond (Ionic.positiveIon state) observer role
positiveNativeIn (moveAnion bond) state observer role = 0

negativeNativeIn :
  (action : OriginalSignedNativeBondAction)
  (state : Ionic.TwoIonSharedGrid) (observer : F.Fin 27) →
  Native.NativeVoxelRole (signedNativeBond action) observer → Nat
negativeNativeIn (moveCation bond) state observer role = 0
negativeNativeIn (moveAnion bond) state observer role =
  Native.nativeRoleIncoming bond (Ionic.negativeIon state) observer role

nativeSignedChargeAfterWithOut :
  (action : OriginalSignedNativeBondAction)
  (state : Ionic.TwoIonSharedGrid) (observer : F.Fin 27)
  (role : Native.NativeVoxelRole (signedNativeBond action) observer) →
  Int.ℤ
nativeSignedChargeAfterWithOut action state observer role =
  Ionic.integerSignedCharge
    (V.lookup (Ionic.positiveIon (applyOriginalSignedNativeBond action state))
      observer + positiveNativeOut action state observer role)
    (V.lookup (Ionic.negativeIon (applyOriginalSignedNativeBond action state))
      observer + negativeNativeOut action state observer role)

nativeSignedChargeBeforeWithIn :
  (action : OriginalSignedNativeBondAction)
  (state : Ionic.TwoIonSharedGrid) (observer : F.Fin 27)
  (role : Native.NativeVoxelRole (signedNativeBond action) observer) →
  Int.ℤ
nativeSignedChargeBeforeWithIn action state observer role =
  Ionic.integerSignedCharge
    (V.lookup (Ionic.positiveIon state) observer
      + positiveNativeIn action state observer role)
    (V.lookup (Ionic.negativeIon state) observer
      + negativeNativeIn action state observer role)

original369SignedNativeOneStepContinuity :
  (action : OriginalSignedNativeBondAction)
  (state : Ionic.TwoIonSharedGrid) (observer : F.Fin 27)
  (role : Native.NativeVoxelRole (signedNativeBond action) observer) →
  nativeSignedChargeAfterWithOut action state observer role
    ≡ nativeSignedChargeBeforeWithIn action state observer role
original369SignedNativeOneStepContinuity
  (moveCation bond) (Ionic.two-ion-shared-grid pos neg)
  observer role =
  cong₂ Ionic.integerSignedCharge
    (Native.originalNativeVoxelIncidenceBalance bond pos observer role)
    refl
original369SignedNativeOneStepContinuity
  (moveAnion bond) (Ionic.two-ion-shared-grid pos neg)
  observer role =
  cong₂ Ionic.integerSignedCharge refl
    (Native.originalNativeVoxelIncidenceBalance bond neg observer role)
