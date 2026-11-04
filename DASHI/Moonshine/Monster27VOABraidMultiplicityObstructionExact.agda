module DASHI.Moonshine.Monster27VOABraidMultiplicityObstructionExact where

-- SOURCE/OWNERS: FLM weight-two V^natural, ATLAS 27A/B -> 9B -> 3B,
-- and the existing Monster27VOACubeWeightedChargeNoGoExact rank chart.
-- This concerns an ACTUAL 3x3x3 balanced ternary cube as a CHOSEN
-- labelling of the cyclic Monster charge eigenspaces. No new VOA action.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Moonshine.JInvariant369Cube27ModularSliceActionExact as Modular
import DASHI.Moonshine.Monster27VOACubeWeightedChargeNoGoExact as Charge

site9To27 : Cube.Ternary27Point
site9To27 =
  Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero

beforeRank : Charge.chargeFibreRank site9To27 ≡ 7296
beforeRank = refl

afterRank :
  Charge.chargeFibreRank (Modular.modularSheetAction site9To27)
    ≡ 7290
afterRank = refl

-- An exact unitary sending the ENTIRE eigenspace indexed by p onto
-- the ENTIRE eigenspace indexed by M p requires equal dimensions.
-- The selected braid M changes an order-nine charge to order 27.
noWholeFibreRankPreservation :
  ((p : Cube.Ternary27Point) →
     Charge.chargeFibreRank (Modular.modularSheetAction p)
       ≡ Charge.chargeFibreRank p) → ⊥
noWholeFibreRankPreservation rankPreserved with rankPreserved site9To27
... | ()

record WholeFibreUnitaryDimensionReceipt : Set where
  field
    dimensionsTransportExactly :
      (p : Cube.Ternary27Point) →
      Charge.chargeFibreRank (Modular.modularSheetAction p)
        ≡ Charge.chargeFibreRank p

noWholeFibreModularUnitary :
  WholeFibreUnitaryDimensionReceipt → ⊥
noWholeFibreModularUnitary certificate =
  noWholeFibreRankPreservation
    (WholeFibreUnitaryDimensionReceipt.dimensionsTransportExactly certificate)

-- Per mixed four-cycle: dimensions 7290,7296,7290,7296.
-- Making every block equal costs twelve dimensions per orbit, for
-- three mixed orbits = 36 additional spectator dimensions.
oneMixedOrbitPadding :
  2 * 7296 + 2 * 7296 ≡
  (2 * 7290 + 2 * 7296) + 12
oneMixedOrbitPadding = refl

threeMixedOrbitPadding : 3 * 12 ≡ 36
threeMixedOrbitPadding = refl

fullWeightTwoWithMinimalSpectators : 196884 + 36 ≡ 196920
fullWeightTwoWithMinimalSpectators = refl

fullWeightTwoAfterMinimalTruncation : 196848 + 36 ≡ 196884
fullWeightTwoAfterMinimalTruncation = refl

-- "36" is a mathematical dimension repair; it is NOT a source
-- identification with the separately found 36 nonlocal spatial
-- edges required to symmetrise the native cube graph.
-- In particular a modular label M which changes charge conductor
-- cannot act by a C27 group automorphism g -> g^a at all.
