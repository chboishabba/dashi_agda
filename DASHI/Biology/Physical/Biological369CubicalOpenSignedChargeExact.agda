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
