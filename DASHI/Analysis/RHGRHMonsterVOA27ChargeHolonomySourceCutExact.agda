module DASHI.Analysis.RHGRHMonsterVOA27ChargeHolonomySourceCutExact where

-- Native 27-site / selected-Monster-VOA charge source cross-cut.
-- The actual 27-charge C27 chart and forbidden uncharged spatial hopping
-- are reused from the ORIGINAL Monster27VOACubeWeightedChargeNoGoExact.
-- Five-axis 13×Bool oriented codec is native P3^3, not a new VOA chart.
--
-- This is an exact SOURCE-DEFINED obstruction on original cube edges.
-- It does not prove an actual charged link exists, nor identify a
-- 13-axis/projective quotient with selected Monster Vnatural_2.
-- Literal selected 3B to actual kernel and Griess/FLM generation still
-- require their OWN original same-object receipts.
-- New source uncompiled: no Agda kernel acceptance or CI.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Moonshine.Monster27VOACubeWeightedChargeNoGoExact as Charge
import DASHI.Unified.HyperfabricPunctured27Projective13OrientationExact as Axis
import DASHI.Analysis.RHGRHIndexedPunctured27HolonomyExact as Indexed
import DASHI.Core.GovernedIndexedResidualCubeExact as CubeIndex
import DASHI.Moonshine.Monster196884FibreInterferenceExact as Dim
import DASHI.Moonshine.MonsterGradedVOAActual3BKernelSameElementBidiExact as ThreeB
import DASHI.Moonshine.Monster369ZetaSameObjectWeldExact as Zeta
import DASHI.Moonshine.Monster3BKernelCharacterCriterionExact as Criterion
import DASHI.Moonshine.Monster27VOAVertexModeChargeSelectionExact as ModeCharge
import DASHI.Moonshine.JInvariant369Cube27CuspCodecNonIsometryExact as Chart
import DASHI.Foundations.SSPTritCarrier as SSP

-- This is the ORIGINAL native spectral-charge chart (a chosen exact
-- cyclic C27 label); not a property of geometric neighbours by fiat.
selectedCubeCharge = Charge.chargeLabel

-- The actual source charge rank 196884 is owned by the existing
-- charge decomposition. This is not a Monster representation construction.
selectedWeightTwoRank :
  7298 + (2 * 7295) + (6 * 7296) + (18 * 7290) ≡ 196884
selectedWeightTwoRank = Charge.fullMonsterWeightTwoCount

sameArithmeticRankAsFibreInterference :
  7298 + (2 * 7295) + (6 * 7296) + (18 * 7290)
    ≡ Dim.fibreInterferenceTotal
sameArithmeticRankAsFibreInterference =
  Charge.fullMonsterWeightTwoCount

-- Crucial: on ORIGINAL P3^3 the charge of two endpoints of a
-- native nearest-neighbour spatial edge is never equal.
nativeChargeChangesAtEveryEdge :
  ∀ {p q : Cube.Ternary27Point} →
  Cube.HypervoxelAdjacent p q →
  Charge.chargeLabel p ≡ Charge.chargeLabel q → ⊥
nativeChargeChangesAtEveryEdge =
  Charge.edgeEndpointsHaveDifferentCharge

-- A claimed charge-preserving bare hopping bond on any source
-- native edge is impossible. The existing charged-link theory must
-- supply a distinct transport and prove its genuine VOA equivariance.
noBareNeutralVOANeighbourHopping :
  ∀ {Bond : Cube.Ternary27Point → Cube.Ternary27Point → Set}
  (preserves : Charge.ChargePreservingOffDiagonalBond Bond)
  {p q : Cube.Ternary27Point} →
  Cube.HypervoxelAdjacent p q →
  Bond p q → ⊥
noBareNeutralVOANeighbourHopping =
  Charge.noNonzeroNearestNeighbourBond

-- Exact oriented native punctured chart reconstruction; the scalar
-- axis projection alone loses the Bool of the original site.
chargeProbeRoundTrip :
  (a : Axis.Axis13) (o : Bool) →
  Axis.encode (Axis.decode (a , o)) ≡ just (a , o)
chargeProbeRoundTrip = Axis.decodeEncode

-- Five separate index axes do not cure native four-cycle holonomy.
indexedGlobalGaugeSectionImpossible :
  (index : Indexed.AxisIndex) →
  Indexed.ClaimedGlobalOrientationAt index → ⊥
indexedGlobalGaugeSectionImpossible =
  Indexed.noGlobalEdgeSectionAt

-- ORIGINAL 3B kernel source: a chosen literal selected Monster element
-- and the actual kernel class MUST be joined by the receipt inside
-- Actual3BKernelSameElementAttachment; this is intentionally conditional.
selectedKernelCharacterIsZetaIfAttached :
  ∀ {Monster K : Set} →
  (attachment : ThreeB.Actual3BKernelSameElementAttachment Monster K) →
  Criterion.coefficientZeta
    (ThreeB.selectedActualRestrictedCharacter attachment) ≡ 65610
selectedKernelCharacterIsZetaIfAttached =
  ThreeB.selectedCentralZetaAmplitudeIs65610

-- A source-correct mathematical next obligation is a *genuine*
-- same-cube source VOA operator, which is charged and carries its
-- edge index/residual; equality of ranks does not construct it.

-- The original selected literal VOA charge-adder already supplies a
-- concrete source chart for positive x/y/z shifts (1,3,9 in C27).
-- These are source-site label equalities, not a construction of a
-- nonzero local hopping matrix element or a global flat gauge section.
selectedPositiveXChargeIsNative :
  Chart.encodeCubeDigits
    (Cube.ternary27Point
      SSP.sspPosOne
      SSP.sspZero
      SSP.sspZero)
  ≡ ModeCharge.positiveXCharge
selectedPositiveXChargeIsNative = ModeCharge.positiveXAxisSite

-- Source-required witness for a *genuine* selected Monster VOA mode:
-- LiteralMonster27ModeChargeReceipt source includes an actual Sector,
-- a typed embedding into the same VOA carrier, and the equality
-- tying cyclic charge addition to the original vertex mode action.
-- It has not been inhabited here and never follows from counts.
