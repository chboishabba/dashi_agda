module DASHI.Reasoning.Ternary27FirstTitsHeisenbergSchlafliBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Mathematics.Algebra.Ternary27FirstTitsAlbertExact as Tits
import DASHI.Reasoning.Ternary27HeisenbergThirteenSchlafliBridgeExact as H13

------------------------------------------------------------------------
-- SAME 27-POINT INDEX SET, TWO EXACT COORDINATE CHARTS
--
-- Chart A: (sector,row,column) basis slots for the first-Tits M3^3 carrier.
-- Chart B: 6 + 15 + 6 Schlaefli/Heisenberg labels, with the central phase kept
--          outside the 27 vertices as the +1 in 3^(1+12).
--
-- Because both charts are already two-sided with the literal Ternary27Point,
-- they are two-sided with each other by composition.  This is a carrier theorem
-- only.  It does not identify the first-Tits Jordan multiplication with the
-- Heisenberg group law or manufacture an action intertwiner.
------------------------------------------------------------------------

firstTitsToHeisenberg27 : Tits.TitsBasisSlot → H13.HeisenbergSchlafli27
firstTitsToHeisenberg27 slot =
  H13.rawTernaryToHeisenberg27 (Tits.basisSlotToPoint slot)

heisenberg27ToFirstTits : H13.HeisenbergSchlafli27 → Tits.TitsBasisSlot
heisenberg27ToFirstTits label =
  Tits.pointToBasisSlot (H13.heisenberg27ToRawTernary label)

firstTitsHeisenbergRoundTrip :
  (slot : Tits.TitsBasisSlot) →
  heisenberg27ToFirstTits (firstTitsToHeisenberg27 slot) ≡ slot
firstTitsHeisenbergRoundTrip slot
  rewrite H13.rawAfterHeisenberg (Tits.basisSlotToPoint slot) =
  Tits.basisPointRoundTrip slot

heisenbergFirstTitsRoundTrip :
  (label : H13.HeisenbergSchlafli27) →
  firstTitsToHeisenberg27 (heisenberg27ToFirstTits label) ≡ label
heisenbergFirstTitsRoundTrip label
  rewrite Tits.pointBasisRoundTrip (H13.heisenberg27ToRawTernary label) =
  H13.heisenbergAfterRaw label

record FirstTitsHeisenbergSchlafliBoundary : Set where
  constructor first-tits-heisenberg-schlafli-boundary
  field
    literalSameTernary27Carrier : Bool
    firstTitsBasisChartTwoSided : Bool
    heisenbergSixFifteenSixChartTwoSided : Bool
    composedChartsTwoSided : Bool
    centralPhaseStillSeparateFromTwentySevenVertices : Bool
    jordanProductEqualsHeisenbergCompositionPaid : Bool
    f4ActionIntertwinesHeisenbergNormalizerPaid : Bool
    e6MinusculeActionIntertwinesBothChartsPaid : Bool
    boundary : String
open FirstTitsHeisenbergSchlafliBoundary public

canonicalFirstTitsHeisenbergSchlafliBoundary : FirstTitsHeisenbergSchlafliBoundary
canonicalFirstTitsHeisenbergSchlafliBoundary =
  first-tits-heisenberg-schlafli-boundary
    true true true true true
    false false false
    "The first-Tits 3x3x3 basis indexing and the existing Heisenberg/Schlaefli 6+15+6 indexing are now exact two-sided charts on the same literal Ternary27Point. The central C3 phase remains the separate +1 coordinate of 3^(1+12). Product/action compatibility remains an explicit intertwiner obligation rather than following from the carrier bijection."

data SameCarrierCreatesSameProduct : Set where
data SameCarrierCreatesSameAction : Set where

sameCarrierDoesNotCreateSameProduct : SameCarrierCreatesSameProduct → {A : Set} → A
sameCarrierDoesNotCreateSameProduct ()

sameCarrierDoesNotCreateSameAction : SameCarrierCreatesSameAction → {A : Set} → A
sameCarrierDoesNotCreateSameAction ()
