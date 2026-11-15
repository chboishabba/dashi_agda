module DASHI.Biology.Physical.Biological369MixedNativeFaceSignedContinuityExact where

-- ORIGINAL 3×3×3 MIXED LOCAL SIGNED CURRENT.
-- One shared two-ion cubical inventory; physically typed original
-- directed 54-bond actions, plus actual six-face injection/withdrawal.
-- Each event is classified at every original voxel by decidable Fin
-- equality; no arbitrary remote currents or fictional internal edges.
-- Output is a finite integer charge ledger, not calibrated PNP kinetics.

open import DASHI.Core.Prelude
import Data.Fin.Base as F
import Data.Vec.Base as V
import Data.Integer.Base as Int
import DASHI.Biology.Physical.BiologicalSignedIonicSharedGridExact as Ionic
import DASHI.Biology.Physical.BiologicalOriginal54BondSharedVectorExact as Native
import DASHI.Biology.Physical.Biological369CubicalBoundaryMaterialExact as Faces
import DASHI.Biology.Physical.Biological369CubicalOpenSignedChargeExact as Ion

data OriginalSignedPhysicalEvent : Set where
  nativeIon : Ion.OriginalSignedNativeBondAction → OriginalSignedPhysicalEvent
  positiveFaceIon : Faces.OriginalFaceExchange → OriginalSignedPhysicalEvent
  negativeFaceIon : Faces.OriginalFaceExchange → OriginalSignedPhysicalEvent

PhysicalEventRole : OriginalSignedPhysicalEvent → F.Fin 27 → Set
PhysicalEventRole (nativeIon action) observer =
  Native.NativeVoxelRole (Ion.signedNativeBond action) observer
PhysicalEventRole (positiveFaceIon event) observer =
  Faces.FaceVoxelRole event observer
PhysicalEventRole (negativeFaceIon event) observer =
  Faces.FaceVoxelRole event observer

classifyPhysicalEvent :
  (event : OriginalSignedPhysicalEvent) (observer : F.Fin 27) →
  PhysicalEventRole event observer
classifyPhysicalEvent (nativeIon action) observer =
  Ion.classifyOriginalNativeVoxel action observer
classifyPhysicalEvent (positiveFaceIon event) observer =
  Faces.classifyFaceVoxel event observer
classifyPhysicalEvent (negativeFaceIon event) observer =
  Faces.classifyFaceVoxel event observer

applyPhysicalEvent :
  OriginalSignedPhysicalEvent →
  Ionic.TwoIonSharedGrid → Ionic.TwoIonSharedGrid
applyPhysicalEvent (nativeIon action) state =
  Ion.applyOriginalSignedNativeBond action state
applyPhysicalEvent (positiveFaceIon event)
  (Ionic.two-ion-shared-grid positive negative) =
  Ionic.two-ion-shared-grid
    (Faces.applyOriginalFaceExchange event positive) negative
applyPhysicalEvent (negativeFaceIon event)
  (Ionic.two-ion-shared-grid positive negative) =
  Ionic.two-ion-shared-grid
    positive (Faces.applyOriginalFaceExchange event negative)

positiveOut :
  (event : OriginalSignedPhysicalEvent)
  (state : Ionic.TwoIonSharedGrid) (observer : F.Fin 27) →
  PhysicalEventRole event observer → Nat
positiveOut (nativeIon action) state observer role =
  Ion.positiveNativeOut action state observer role
positiveOut (positiveFaceIon event) state observer role =
  Faces.localFaceOut event (Ionic.positiveIon state) observer role
positiveOut (negativeFaceIon event) state observer role = 0

positiveIn :
  (event : OriginalSignedPhysicalEvent)
  (state : Ionic.TwoIonSharedGrid) (observer : F.Fin 27) →
  PhysicalEventRole event observer → Nat
positiveIn (nativeIon action) state observer role =
  Ion.positiveNativeIn action state observer role
positiveIn (positiveFaceIon event) state observer role =
  Faces.localFaceIn event (Ionic.positiveIon state) observer role
positiveIn (negativeFaceIon event) state observer role = 0

negativeOut :
  (event : OriginalSignedPhysicalEvent)
  (state : Ionic.TwoIonSharedGrid) (observer : F.Fin 27) →
  PhysicalEventRole event observer → Nat
negativeOut (nativeIon action) state observer role =
  Ion.negativeNativeOut action state observer role
negativeOut (positiveFaceIon event) state observer role = 0
negativeOut (negativeFaceIon event) state observer role =
  Faces.localFaceOut event (Ionic.negativeIon state) observer role

negativeIn :
  (event : OriginalSignedPhysicalEvent)
  (state : Ionic.TwoIonSharedGrid) (observer : F.Fin 27) →
  PhysicalEventRole event observer → Nat
negativeIn (nativeIon action) state observer role =
  Ion.negativeNativeIn action state observer role
negativeIn (positiveFaceIon event) state observer role = 0
negativeIn (negativeFaceIon event) state observer role =
  Faces.localFaceIn event (Ionic.negativeIon state) observer role

positiveOnePhysicalStep :
  (event : OriginalSignedPhysicalEvent)
  (state : Ionic.TwoIonSharedGrid) (observer : F.Fin 27)
  (role : PhysicalEventRole event observer) →
  Ion.positiveAtVoxel observer (applyPhysicalEvent event state)
    + positiveOut event state observer role
    ≡ Ion.positiveAtVoxel observer state
      + positiveIn event state observer role
positiveOnePhysicalStep (nativeIon action) state observer role =
  Ion.positiveNativeOneStepBalance action state observer role
positiveOnePhysicalStep (positiveFaceIon event)
  (Ionic.two-ion-shared-grid positive negative) observer role =
  Faces.originalFaceVoxelBalance event positive observer role
positiveOnePhysicalStep (negativeFaceIon event)
  (Ionic.two-ion-shared-grid positive negative) observer role = refl

negativeOnePhysicalStep :
  (event : OriginalSignedPhysicalEvent)
  (state : Ionic.TwoIonSharedGrid) (observer : F.Fin 27)
  (role : PhysicalEventRole event observer) →
  Ion.negativeAtVoxel observer (applyPhysicalEvent event state)
    + negativeOut event state observer role
    ≡ Ion.negativeAtVoxel observer state
      + negativeIn event state observer role
negativeOnePhysicalStep (nativeIon action) state observer role =
  Ion.negativeNativeOneStepBalance action state observer role
negativeOnePhysicalStep (positiveFaceIon event)
  (Ionic.two-ion-shared-grid positive negative) observer role = refl
negativeOnePhysicalStep (negativeFaceIon event)
  (Ionic.two-ion-shared-grid positive negative) observer role =
  Faces.originalFaceVoxelBalance event negative observer role

record SignedPhysicalVoxelLedger : Set where
  constructor signed-physical-voxel-ledger
  field
    finalState : Ionic.TwoIonSharedGrid
    plusOut : Nat
    plusIn : Nat
    minusOut : Nat
    minusIn : Nat
open SignedPhysicalVoxelLedger public

runPhysicalHistoryAt :
  (observer : F.Fin 27) →
  List OriginalSignedPhysicalEvent →
  Ionic.TwoIonSharedGrid → SignedPhysicalVoxelLedger
runPhysicalHistoryAt observer [] state =
  signed-physical-voxel-ledger state 0 0 0 0
runPhysicalHistoryAt observer (event ∷ rest) state
  with runPhysicalHistoryAt observer rest (applyPhysicalEvent event state)
... | signed-physical-voxel-ledger final pOut pIn nOut nIn =
  signed-physical-voxel-ledger final
    (positiveOut event state observer
      (classifyPhysicalEvent event observer) + pOut)
    (positiveIn event state observer
      (classifyPhysicalEvent event observer) + pIn)
    (negativeOut event state observer
      (classifyPhysicalEvent event observer) + nOut)
    (negativeIn event state observer
      (classifyPhysicalEvent event observer) + nIn)

positiveMixedHistoryBalance :
  (observer : F.Fin 27)
  (events : List OriginalSignedPhysicalEvent)
  (state : Ionic.TwoIonSharedGrid) →
  Ion.positiveAtVoxel observer (finalState (runPhysicalHistoryAt observer events state))
    + plusOut (runPhysicalHistoryAt observer events state)
    ≡ Ion.positiveAtVoxel observer state
      + plusIn (runPhysicalHistoryAt observer events state)
positiveMixedHistoryBalance observer [] state = refl
positiveMixedHistoryBalance observer (event ∷ rest) state
  with runPhysicalHistoryAt observer rest (applyPhysicalEvent event state)
     | positiveMixedHistoryBalance observer rest (applyPhysicalEvent event state)
... | signed-physical-voxel-ledger final pOut pIn nOut nIn | induction =
  trans
    (Faces.exchangeAssociative
      (Ion.positiveAtVoxel observer final)
      (positiveOut event state observer
        (classifyPhysicalEvent event observer)) pOut)
    (trans
      (cong (λ n → n + positiveOut event state observer
        (classifyPhysicalEvent event observer)) induction)
      (trans
        (Ion.swapAccumulatedCurrent
          (Ion.positiveAtVoxel observer (applyPhysicalEvent event state))
          pIn (positiveOut event state observer
            (classifyPhysicalEvent event observer)))
        (trans
          (cong (λ n → n + pIn)
            (positiveOnePhysicalStep event state observer
              (classifyPhysicalEvent event observer)))
          (+-assoc (Ion.positiveAtVoxel observer state)
            (positiveIn event state observer
              (classifyPhysicalEvent event observer)) pIn))))

negativeMixedHistoryBalance :
  (observer : F.Fin 27)
  (events : List OriginalSignedPhysicalEvent)
  (state : Ionic.TwoIonSharedGrid) →
  Ion.negativeAtVoxel observer (finalState (runPhysicalHistoryAt observer events state))
    + minusOut (runPhysicalHistoryAt observer events state)
    ≡ Ion.negativeAtVoxel observer state
      + minusIn (runPhysicalHistoryAt observer events state)
negativeMixedHistoryBalance observer [] state = refl
negativeMixedHistoryBalance observer (event ∷ rest) state
  with runPhysicalHistoryAt observer rest (applyPhysicalEvent event state)
     | negativeMixedHistoryBalance observer rest (applyPhysicalEvent event state)
... | signed-physical-voxel-ledger final pOut pIn nOut nIn | induction =
  trans
    (Faces.exchangeAssociative
      (Ion.negativeAtVoxel observer final)
      (negativeOut event state observer
        (classifyPhysicalEvent event observer)) nOut)
    (trans
      (cong (λ n → n + negativeOut event state observer
        (classifyPhysicalEvent event observer)) induction)
      (trans
        (Ion.swapAccumulatedCurrent
          (Ion.negativeAtVoxel observer (applyPhysicalEvent event state))
          nIn (negativeOut event state observer
            (classifyPhysicalEvent event observer)))
        (trans
          (cong (λ n → n + nIn)
            (negativeOnePhysicalStep event state observer
              (classifyPhysicalEvent event observer)))
          (+-assoc (Ion.negativeAtVoxel observer state)
            (negativeIn event state observer
              (classifyPhysicalEvent event observer)) nIn))))

-- Intended original P0 source theorem: for every genuine cubical voxel
-- and arbitrary chronological cation/anion native-bond and six-face
-- event history, signed final+outflow equals signed initial+inflow.
-- Exact-head kernel checking remains independently REQUIRED.
original369LocalSignedContinuityExact :
  (observer : F.Fin 27)
  (events : List OriginalSignedPhysicalEvent)
  (state : Ionic.TwoIonSharedGrid) →
  Ionic.integerSignedCharge
    (Ion.positiveAtVoxel observer
      (finalState (runPhysicalHistoryAt observer events state))
      + plusOut (runPhysicalHistoryAt observer events state))
    (Ion.negativeAtVoxel observer
      (finalState (runPhysicalHistoryAt observer events state))
      + minusOut (runPhysicalHistoryAt observer events state))
    ≡ Ionic.integerSignedCharge
      (Ion.positiveAtVoxel observer state
        + plusIn (runPhysicalHistoryAt observer events state))
      (Ion.negativeAtVoxel observer state
        + minusIn (runPhysicalHistoryAt observer events state))
original369LocalSignedContinuityExact observer events state =
  cong₂ Ionic.integerSignedCharge
    (positiveMixedHistoryBalance observer events state)
    (negativeMixedHistoryBalance observer events state)
