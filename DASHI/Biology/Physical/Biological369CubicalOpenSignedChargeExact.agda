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


------------------------------------------------------------------------
-- CHRONOLOGICAL SIGNED NATIVE TRANSPORT HISTORY: each history entry
-- includes its actual original 54-bond action and the observed voxel's
-- certified source/target/spectator role. Two separate natural current
-- ledgers retain the actual positive and negative ion currents.
-- The final theorem transports both exact balances into integer signed
-- charge. Boundary face events remain a separate pending mixed-history
-- owner: they are NOT silently treated as internal zero-current events.
------------------------------------------------------------------------

record LocatedSignedNativeAction (observer : F.Fin 27) : Set where
  constructor located-signed-native-action
  field
    locatedAction : OriginalSignedNativeBondAction
    locatedRole : Native.NativeVoxelRole (signedNativeBond locatedAction) observer
open LocatedSignedNativeAction public

positiveAtVoxel : F.Fin 27 → Ionic.TwoIonSharedGrid → Nat
positiveAtVoxel observer state =
  V.lookup (Ionic.positiveIon state) observer

negativeAtVoxel : F.Fin 27 → Ionic.TwoIonSharedGrid → Nat
negativeAtVoxel observer state =
  V.lookup (Ionic.negativeIon state) observer

positiveNativeOneStepBalance :
  (action : OriginalSignedNativeBondAction)
  (state : Ionic.TwoIonSharedGrid) (observer : F.Fin 27)
  (role : Native.NativeVoxelRole (signedNativeBond action) observer) →
  positiveAtVoxel observer (applyOriginalSignedNativeBond action state)
    + positiveNativeOut action state observer role
    ≡ positiveAtVoxel observer state
      + positiveNativeIn action state observer role
positiveNativeOneStepBalance (moveCation bond)
  (Ionic.two-ion-shared-grid pos neg) observer role =
  Native.originalNativeVoxelIncidenceBalance bond pos observer role
positiveNativeOneStepBalance (moveAnion bond)
  (Ionic.two-ion-shared-grid pos neg) observer role = refl

negativeNativeOneStepBalance :
  (action : OriginalSignedNativeBondAction)
  (state : Ionic.TwoIonSharedGrid) (observer : F.Fin 27)
  (role : Native.NativeVoxelRole (signedNativeBond action) observer) →
  negativeAtVoxel observer (applyOriginalSignedNativeBond action state)
    + negativeNativeOut action state observer role
    ≡ negativeAtVoxel observer state
      + negativeNativeIn action state observer role
negativeNativeOneStepBalance (moveCation bond)
  (Ionic.two-ion-shared-grid pos neg) observer role = refl
negativeNativeOneStepBalance (moveAnion bond)
  (Ionic.two-ion-shared-grid pos neg) observer role =
  Native.originalNativeVoxelIncidenceBalance bond neg observer role

record NativeSignedVoxelHistoryLedger : Set where
  constructor native-signed-voxel-history-ledger
  field
    finalNativeIons : Ionic.TwoIonSharedGrid
    cumulativePositiveOut : Nat
    cumulativePositiveIn : Nat
    cumulativeNegativeOut : Nat
    cumulativeNegativeIn : Nat
open NativeSignedVoxelHistoryLedger public

runLocatedSignedNativeHistory :
  (observer : F.Fin 27) →
  List (LocatedSignedNativeAction observer) →
  Ionic.TwoIonSharedGrid → NativeSignedVoxelHistoryLedger
runLocatedSignedNativeHistory observer [] state =
  native-signed-voxel-history-ledger state 0 0 0 0
runLocatedSignedNativeHistory observer
  (located-signed-native-action action role ∷ rest) state
  with runLocatedSignedNativeHistory observer rest
    (applyOriginalSignedNativeBond action state)
... | native-signed-voxel-history-ledger final posOut posIn negOut negIn =
  native-signed-voxel-history-ledger final
    (positiveNativeOut action state observer role + posOut)
    (positiveNativeIn action state observer role + posIn)
    (negativeNativeOut action state observer role + negOut)
    (negativeNativeIn action state observer role + negIn)

-- Rearrange (a+b)+c without cancellation or subtraction.
swapAccumulatedCurrent :
  (a b c : Nat) → (a + b) + c ≡ (a + c) + b
swapAccumulatedCurrent a b c =
  trans (sym (+-assoc a b c))
    (trans (cong (λ n → a + n) (+-comm b c))
      (sym (+-assoc a c b)))

allLocatedNativeHistoriesPositiveBalance :
  (observer : F.Fin 27)
  (actions : List (LocatedSignedNativeAction observer))
  (state : Ionic.TwoIonSharedGrid) →
  positiveAtVoxel observer
    (finalNativeIons (runLocatedSignedNativeHistory observer actions state))
    + cumulativePositiveOut (runLocatedSignedNativeHistory observer actions state)
    ≡ positiveAtVoxel observer state
      + cumulativePositiveIn (runLocatedSignedNativeHistory observer actions state)
allLocatedNativeHistoriesPositiveBalance observer [] state = refl
allLocatedNativeHistoriesPositiveBalance observer
  (located-signed-native-action action role ∷ rest) state
  with runLocatedSignedNativeHistory observer rest
         (applyOriginalSignedNativeBond action state)
     | allLocatedNativeHistoriesPositiveBalance observer rest
         (applyOriginalSignedNativeBond action state)
... | native-signed-voxel-history-ledger final pOut pIn nOut nIn | induction =
  trans
    (Faces.exchangeAssociative
      (positiveAtVoxel observer final)
      (positiveNativeOut action state observer role) pOut)
    (trans
      (cong (λ n → n + positiveNativeOut action state observer role)
        induction)
      (trans
        (swapAccumulatedCurrent
          (positiveAtVoxel observer
            (applyOriginalSignedNativeBond action state))
          pIn (positiveNativeOut action state observer role))
        (trans
          (cong (λ n → n + pIn)
            (positiveNativeOneStepBalance action state observer role))
          (+-assoc
            (positiveAtVoxel observer state)
            (positiveNativeIn action state observer role) pIn))))

allLocatedNativeHistoriesNegativeBalance :
  (observer : F.Fin 27)
  (actions : List (LocatedSignedNativeAction observer))
  (state : Ionic.TwoIonSharedGrid) →
  negativeAtVoxel observer
    (finalNativeIons (runLocatedSignedNativeHistory observer actions state))
    + cumulativeNegativeOut (runLocatedSignedNativeHistory observer actions state)
    ≡ negativeAtVoxel observer state
      + cumulativeNegativeIn (runLocatedSignedNativeHistory observer actions state)
allLocatedNativeHistoriesNegativeBalance observer [] state = refl
allLocatedNativeHistoriesNegativeBalance observer
  (located-signed-native-action action role ∷ rest) state
  with runLocatedSignedNativeHistory observer rest
         (applyOriginalSignedNativeBond action state)
     | allLocatedNativeHistoriesNegativeBalance observer rest
         (applyOriginalSignedNativeBond action state)
... | native-signed-voxel-history-ledger final pOut pIn nOut nIn | induction =
  trans
    (Faces.exchangeAssociative
      (negativeAtVoxel observer final)
      (negativeNativeOut action state observer role) nOut)
    (trans
      (cong (λ n → n + negativeNativeOut action state observer role)
        induction)
      (trans
        (swapAccumulatedCurrent
          (negativeAtVoxel observer
            (applyOriginalSignedNativeBond action state))
          nIn (negativeNativeOut action state observer role))
        (trans
          (cong (λ n → n + nIn)
            (negativeNativeOneStepBalance action state observer role))
          (+-assoc
            (negativeAtVoxel observer state)
            (negativeNativeIn action state observer role) nIn))))

original369LocatedNativeSignedHistoryContinuity :
  (observer : F.Fin 27)
  (actions : List (LocatedSignedNativeAction observer))
  (state : Ionic.TwoIonSharedGrid) →
  Ionic.integerSignedCharge
    (positiveAtVoxel observer
      (finalNativeIons (runLocatedSignedNativeHistory observer actions state))
      + cumulativePositiveOut
        (runLocatedSignedNativeHistory observer actions state))
    (negativeAtVoxel observer
      (finalNativeIons (runLocatedSignedNativeHistory observer actions state))
      + cumulativeNegativeOut
        (runLocatedSignedNativeHistory observer actions state))
    ≡ Ionic.integerSignedCharge
      (positiveAtVoxel observer state
        + cumulativePositiveIn
          (runLocatedSignedNativeHistory observer actions state))
      (negativeAtVoxel observer state
        + cumulativeNegativeIn
          (runLocatedSignedNativeHistory observer actions state))
original369LocatedNativeSignedHistoryContinuity observer actions state =
  cong₂ Ionic.integerSignedCharge
    (allLocatedNativeHistoriesPositiveBalance observer actions state)
    (allLocatedNativeHistoriesNegativeBalance observer actions state)


------------------------------------------------------------------------
-- REMOVE MANUAL VOXEL ROLE EVIDENCE: stdlib decidable Fin equality
-- assigns source, target or spectator at EVERY original voxel.
-- No classical choice, no 27-case hardcoding, no unconstrained edge.
------------------------------------------------------------------------

import Data.Fin.Properties as FinProps
import Relation.Nullary as Nullary

classifyOriginalNativeVoxel :
  (action : OriginalSignedNativeBondAction) →
  (observer : F.Fin 27) →
  Native.NativeVoxelRole (signedNativeBond action) observer
classifyOriginalNativeVoxel action observer
  with FinProps._≟_ (Native.nativeDirectedSource (signedNativeBond action))
         observer
... | Nullary.yes sourceProof = Native.atNativeSource sourceProof
... | Nullary.no sourceDifferent
  with FinProps._≟_ (Native.nativeDirectedTarget (signedNativeBond action))
         observer
...   | Nullary.yes targetProof = Native.atNativeTarget targetProof
...   | Nullary.no targetDifferent =
  Native.offNativeEndpoints sourceDifferent targetDifferent

locateEveryOriginalNativeEvent :
  (observer : F.Fin 27) →
  List OriginalSignedNativeBondAction →
  List (LocatedSignedNativeAction observer)
locateEveryOriginalNativeEvent observer [] = []
locateEveryOriginalNativeEvent observer (action ∷ rest) =
  located-signed-native-action action
    (classifyOriginalNativeVoxel action observer)
    ∷ locateEveryOriginalNativeEvent observer rest

-- Final per-voxel integer current balance for any chronological
-- original signed-bond history, with role classification constructed
-- from original source/target indices rather than supplied by caller.
original369AllVoxelNativeSignedHistoryContinuity :
  (observer : F.Fin 27)
  (actions : List OriginalSignedNativeBondAction)
  (state : Ionic.TwoIonSharedGrid) →
  Ionic.integerSignedCharge
    (positiveAtVoxel observer
      (finalNativeIons (runLocatedSignedNativeHistory observer
        (locateEveryOriginalNativeEvent observer actions) state))
      + cumulativePositiveOut
        (runLocatedSignedNativeHistory observer
          (locateEveryOriginalNativeEvent observer actions) state))
    (negativeAtVoxel observer
      (finalNativeIons (runLocatedSignedNativeHistory observer
        (locateEveryOriginalNativeEvent observer actions) state))
      + cumulativeNegativeOut
        (runLocatedSignedNativeHistory observer
          (locateEveryOriginalNativeEvent observer actions) state))
    ≡ Ionic.integerSignedCharge
      (positiveAtVoxel observer state
        + cumulativePositiveIn
          (runLocatedSignedNativeHistory observer
            (locateEveryOriginalNativeEvent observer actions) state))
      (negativeAtVoxel observer state
        + cumulativeNegativeIn
          (runLocatedSignedNativeHistory observer
            (locateEveryOriginalNativeEvent observer actions) state))
original369AllVoxelNativeSignedHistoryContinuity observer actions state =
  original369LocatedNativeSignedHistoryContinuity observer
    (locateEveryOriginalNativeEvent observer actions) state
