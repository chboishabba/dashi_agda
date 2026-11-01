module DASHI.Foundations.TrialecticStageThirteenMarkedOrbitAdapterExact where

------------------------------------------------------------------------
-- Nontrivial 3-slot -> 27-cubie C3 intertwiner.
-- The marked slots are not identified with all 27 cubies: this is one
-- actual free orbit inside the non-free coordinate-permutation action.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Foundations.SSPTritCarrier as T
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as G
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as S
import DASHI.Foundations.TrialecticStageThirteenMarkedC3CubieExact as Stage13

data MarkedUnitSlot : Set where slotX slotY slotZ : MarkedUnitSlot

rotateSlot : MarkedUnitSlot → MarkedUnitSlot
rotateSlot slotX = slotZ
rotateSlot slotZ = slotY
rotateSlot slotY = slotX

rotateSlotThree : (u : MarkedUnitSlot) →
  rotateSlot (rotateSlot (rotateSlot u)) ≡ u
rotateSlotThree slotX = refl
rotateSlotThree slotY = refl
rotateSlotThree slotZ = refl

markedUnitToCubie : MarkedUnitSlot → G.Ternary27Point
markedUnitToCubie slotX = G.ternary27Point T.sspPosOne T.sspZero T.sspZero
markedUnitToCubie slotY = G.ternary27Point T.sspZero T.sspPosOne T.sspZero
markedUnitToCubie slotZ = G.ternary27Point T.sspZero T.sspZero T.sspPosOne

markedUnitIntertwinesC3 : (u : MarkedUnitSlot) →
  markedUnitToCubie (rotateSlot u) ≡
    Stage13.stage13Rotate (markedUnitToCubie u)
markedUnitIntertwinesC3 slotX = refl
markedUnitIntertwinesC3 slotY = refl
markedUnitIntertwinesC3 slotZ = refl

slotInjective : (u v : MarkedUnitSlot) →
  markedUnitToCubie u ≡ markedUnitToCubie v → u ≡ v
slotInjective slotX slotX equality = refl
slotInjective slotX slotY ()
slotInjective slotX slotZ ()
slotInjective slotY slotX ()
slotInjective slotY slotY equality = refl
slotInjective slotY slotZ ()
slotInjective slotZ slotX ()
slotInjective slotZ slotY ()
slotInjective slotZ slotZ equality = refl

slotRotationMoves : (u : MarkedUnitSlot) →
  rotateSlot u ≡ u → ⊥
slotRotationMoves slotX ()
slotRotationMoves slotY ()
slotRotationMoves slotZ ()

-- The all-positive (111) cubie is a separate C3 fixed point.
-- It is not within this marked one-hot orbit.
positiveCornerNotSlot : (u : MarkedUnitSlot) →
  markedUnitToCubie u ≡ G.positiveCorner → ⊥
positiveCornerNotSlot slotX ()
positiveCornerNotSlot slotY ()
positiveCornerNotSlot slotZ ()
