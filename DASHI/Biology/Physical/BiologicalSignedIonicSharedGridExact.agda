module DASHI.Biology.Physical.BiologicalSignedIonicSharedGridExact where

-- ORIGINAL SHARED 27-SITE INTERNAL IONIC TRANSPORT.
-- Separate positive and negative ion inventories, each on the
-- same canonical 54-bond voxel indexing. Their independent total
-- conservation induces equality for ANY signed charge interpretation.
-- This proves closed-system transport charge accounting, not a Poisson
-- field, calibrated ionic mobility or external boundary current.

open import DASHI.Core.Prelude

import Data.Integer.Base as Int
import Data.Vec.Base as V
import Data.Fin.Base as F
import DASHI.Biology.Physical.BiologicalSharedFiniteVectorTransferExact as Transfer
import DASHI.Biology.Physical.BiologicalOriginal54BondSharedVectorExact as Grid
import DASHI.Biology.Physical.BiologicalFullCubeIncidenceExact as Bonds

record TwoIonSharedGrid : Set where
  constructor two-ion-shared-grid
  field
    positiveIon : V.Vec Nat 27
    negativeIon : V.Vec Nat 27

open TwoIonSharedGrid public

data IonMovement : Set where
  movePositive : F.Fin 27 → F.Fin 27 → IonMovement
  moveNegative : F.Fin 27 → F.Fin 27 → IonMovement

moveIon :
  IonMovement → TwoIonSharedGrid → TwoIonSharedGrid
moveIon (movePositive source target)
  (two-ion-shared-grid pos neg) =
  two-ion-shared-grid (Transfer.transferOne source target pos) neg
moveIon (moveNegative source target)
  (two-ion-shared-grid pos neg) =
  two-ion-shared-grid pos (Transfer.transferOne source target neg)

positiveTotal : TwoIonSharedGrid → Nat
positiveTotal state = V.sum (positiveIon state)

negativeTotal : TwoIonSharedGrid → Nat
negativeTotal state = V.sum (negativeIon state)

positiveIonTotalPreserved :
  (event : IonMovement) (state : TwoIonSharedGrid) →
  positiveTotal (moveIon event state) ≡ positiveTotal state
positiveIonTotalPreserved (movePositive source target)
  (two-ion-shared-grid pos neg) =
  Transfer.everyDirectedPairConservesSharedInventory source target pos
positiveIonTotalPreserved (moveNegative source target)
  (two-ion-shared-grid pos neg) = refl

negativeIonTotalPreserved :
  (event : IonMovement) (state : TwoIonSharedGrid) →
  negativeTotal (moveIon event state) ≡ negativeTotal state
negativeIonTotalPreserved (movePositive source target)
  (two-ion-shared-grid pos neg) = refl
negativeIonTotalPreserved (moveNegative source target)
  (two-ion-shared-grid pos neg) =
  Transfer.everyDirectedPairConservesSharedInventory source target neg

-- Signed charge may be interpreted with integer-valued signs,
-- valence magnitude, charge units or symbolic net-charge operators
-- by supplying the SAME total-charge function at both endpoints.
-- No unsigned "charge magnitude" is mislabeled net signed charge.
anySignedChargeInterpretationPreserved :
  ∀ {Charge : Set}
  (signedCharge : Nat → Nat → Charge)
  (event : IonMovement)
  (state : TwoIonSharedGrid) →
  signedCharge
    (positiveTotal (moveIon event state))
    (negativeTotal (moveIon event state))
    ≡
  signedCharge (positiveTotal state) (negativeTotal state)
anySignedChargeInterpretationPreserved signedCharge event state =
  cong₂ signedCharge
    (positiveIonTotalPreserved event state)
    (negativeIonTotalPreserved event state)

runIonHistory :
  List IonMovement → TwoIonSharedGrid → TwoIonSharedGrid
runIonHistory [] state = state
runIonHistory (action ∷ rest) state =
  runIonHistory rest (moveIon action state)

allIonHistoriesPreservePositiveTotal :
  (actions : List IonMovement)
  (state : TwoIonSharedGrid) →
  positiveTotal (runIonHistory actions state) ≡ positiveTotal state
allIonHistoriesPreservePositiveTotal [] state = refl
allIonHistoriesPreservePositiveTotal (event ∷ rest) state =
  trans
    (allIonHistoriesPreservePositiveTotal rest (moveIon event state))
    (positiveIonTotalPreserved event state)

allIonHistoriesPreserveNegativeTotal :
  (actions : List IonMovement)
  (state : TwoIonSharedGrid) →
  negativeTotal (runIonHistory actions state) ≡ negativeTotal state
allIonHistoriesPreserveNegativeTotal [] state = refl
allIonHistoriesPreserveNegativeTotal (event ∷ rest) state =
  trans
    (allIonHistoriesPreserveNegativeTotal rest (moveIon event state))
    (negativeIonTotalPreserved event state)

allIonHistoriesPreserveSignedCharge :
  ∀ {Charge : Set}
  (signedCharge : Nat → Nat → Charge)
  (actions : List IonMovement)
  (state : TwoIonSharedGrid) →
  signedCharge
    (positiveTotal (runIonHistory actions state))
    (negativeTotal (runIonHistory actions state))
    ≡ signedCharge (positiveTotal state) (negativeTotal state)
allIonHistoriesPreserveSignedCharge signedCharge actions state =
  cong₂ signedCharge
    (allIonHistoriesPreservePositiveTotal actions state)
    (allIonHistoriesPreserveNegativeTotal actions state)

-- A *source-selected* original native bond yields the same shared
-- 27-site update as the arbitrary-index owner, not two edge copies.
originalForwardPositive :
  Bonds.PositiveBond → IonMovement
originalForwardPositive bond =
  movePositive
    (Transfer.sourceIndex Grid.canonical54BondIndexing bond)
    (Transfer.targetIndex Grid.canonical54BondIndexing bond)

originalForwardNegative :
  Bonds.PositiveBond → IonMovement
originalForwardNegative bond =
  moveNegative
    (Transfer.sourceIndex Grid.canonical54BondIndexing bond)
    (Transfer.targetIndex Grid.canonical54BondIndexing bond)

all54PositiveActions : List IonMovement
all54PositiveActions =
  Bonds.mapList originalForwardPositive Bonds.allPositiveBonds

all54NegativeActions : List IonMovement
all54NegativeActions =
  Bonds.mapList originalForwardNegative Bonds.allPositiveBonds

allOriginal54PositiveTransportHistoriesPreserveSignedCharge :
  ∀ {Charge : Set}
  (signedCharge : Nat → Nat → Charge)
  (state : TwoIonSharedGrid) →
  signedCharge
    (positiveTotal (runIonHistory all54PositiveActions state))
    (negativeTotal (runIonHistory all54PositiveActions state))
  ≡ signedCharge (positiveTotal state) (negativeTotal state)
allOriginal54PositiveTransportHistoriesPreserveSignedCharge
  signedCharge state =
  allIonHistoriesPreserveSignedCharge signedCharge
    all54PositiveActions state

allOriginal54NegativeTransportHistoriesPreserveSignedCharge :
  ∀ {Charge : Set}
  (signedCharge : Nat → Nat → Charge)
  (state : TwoIonSharedGrid) →
  signedCharge
    (positiveTotal (runIonHistory all54NegativeActions state))
    (negativeTotal (runIonHistory all54NegativeActions state))
  ≡ signedCharge (positiveTotal state) (negativeTotal state)
allOriginal54NegativeTransportHistoriesPreserveSignedCharge
  signedCharge state =
  allIonHistoriesPreserveSignedCharge signedCharge
    all54NegativeActions state

------------------------------------------------------------------------
-- Native integer-valued signed net charge; not merely an abstract
-- unsigned charge-magnitude witness.
------------------------------------------------------------------------

integerSignedCharge : Nat → Nat → Int.ℤ
integerSignedCharge positive negative =
  Int._-_ (Int.+ positive) (Int.+ negative)

originalNetSignedCharge : TwoIonSharedGrid → Int.ℤ
originalNetSignedCharge state =
  integerSignedCharge (positiveTotal state) (negativeTotal state)

nativeSignedChargeConservedByEveryHistory :
  (actions : List IonMovement)
  (state : TwoIonSharedGrid) →
  originalNetSignedCharge (runIonHistory actions state)
    ≡ originalNetSignedCharge state
nativeSignedChargeConservedByEveryHistory actions state =
  allIonHistoriesPreserveSignedCharge integerSignedCharge actions state

nativeOriginal54BondSignedChargeConserved :
  (state : TwoIonSharedGrid) →
  originalNetSignedCharge
    (runIonHistory all54PositiveActions
      (runIonHistory all54NegativeActions state))
    ≡ originalNetSignedCharge state
nativeOriginal54BondSignedChargeConserved state =
  trans
    (nativeSignedChargeConservedByEveryHistory
      all54PositiveActions (runIonHistory all54NegativeActions state))
    (nativeSignedChargeConservedByEveryHistory
      all54NegativeActions state)
