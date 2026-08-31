module DASHI.Moonshine.Base369HeisenbergTranslationGridObstructionExact where

------------------------------------------------------------------------
-- CARRIER EQUIVALENCE DOES NOT FORCE DYNAMICAL EQUIVALENCE
--
-- The 729-point appraisal fibre is exactly charted by the Monster 3B finite
-- Heisenberg X6 carrier.  But X6 translation is cyclic mod 3, whereas the
-- geometric hypervoxel uses the non-periodic path -1 <-> 0 <-> +1.
-- Therefore the Heisenberg translation action cannot be silently identified
-- with native nearest-neighbour fibre transport.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import DASHI.Algebra.Trit using (neg; zer; pos)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as Heisenberg
import DASHI.Moonshine.Base369AppraisalFibreHeisenbergCarrierBidiExact as Carrier
import DASHI.Moonshine.Base369Ternary27SignedSymmetryMonsterIntertwinerExact as Signed

------------------------------------------------------------------------
-- 1. Transport Heisenberg translations through the exact carrier chart.
--    This constructs a fibre permutation; it does not make it a P3 edge.
------------------------------------------------------------------------

heisenbergTranslateFibre :
  Heisenberg.Axis6 → Geometry.AppraisalFibrePoint → Geometry.AppraisalFibrePoint
heisenbergTranslateFibre axis fibre =
  Carrier.x6ToAppraisalFibre
    (Heisenberg.translate axis (Carrier.appraisalFibreToX6 fibre))

heisenbergTranslateIntertwinesByConstruction :
  (axis : Heisenberg.Axis6) →
  (fibre : Geometry.AppraisalFibrePoint) →
  Carrier.appraisalFibreToX6 (heisenbergTranslateFibre axis fibre)
  ≡ Heisenberg.translate axis (Carrier.appraisalFibreToX6 fibre)
heisenbergTranslateIntertwinesByConstruction axis fibre =
  Carrier.x6RoundTrip
    (Heisenberg.translate axis (Carrier.appraisalFibreToX6 fibre))

------------------------------------------------------------------------
-- 2. Exact wraparound witness: +1 -> -1 on axis0.
------------------------------------------------------------------------

positiveAxisFibre : Geometry.AppraisalFibrePoint
positiveAxisFibre =
  Geometry.appraisalFibrePoint
    (Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero)
    Geometry.origin

wrappedAxisFibre : Geometry.AppraisalFibrePoint
wrappedAxisFibre =
  Geometry.appraisalFibrePoint
    (Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero)
    Geometry.origin

axis0HeisenbergTranslationWrapsPositiveToNegative :
  heisenbergTranslateFibre Heisenberg.axis0 positiveAxisFibre
  ≡ wrappedAxisFibre
axis0HeisenbergTranslationWrapsPositiveToNegative = refl

nativeGridHasNoPositiveToNegativeStep :
  Geometry.TritGridStep SSP.sspPosOne SSP.sspNegOne → ⊥
nativeGridHasNoPositiveToNegativeStep = Geometry.noDirectPosToNeg

------------------------------------------------------------------------
-- 3. The same cyclic translation also maps a native edge to a non-edge.
------------------------------------------------------------------------

zeroAxisPoint : Geometry.Ternary27Point
zeroAxisPoint = Geometry.origin

positiveAxisPoint : Geometry.Ternary27Point
positiveAxisPoint =
  Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero

zeroToPositiveIsNativeEdge :
  Geometry.HypervoxelAdjacent zeroAxisPoint positiveAxisPoint
zeroToPositiveIsNativeEdge = Geometry.adjacentX Geometry.zeroToPos

translatedZeroAxisPoint : Geometry.Ternary27Point
translatedZeroAxisPoint = positiveAxisPoint

translatedPositiveAxisPoint : Geometry.Ternary27Point
translatedPositiveAxisPoint =
  Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero

translatedNativeEdgeWouldRequireWraparound :
  Geometry.HypervoxelAdjacent translatedZeroAxisPoint translatedPositiveAxisPoint → ⊥
translatedNativeEdgeWouldRequireWraparound (Geometry.adjacentX step) =
  Geometry.noDirectPosToNeg step

------------------------------------------------------------------------
-- 4. In contrast, sign inversion DOES match an existing geometric symmetry.
------------------------------------------------------------------------

heisenbergNegateTritMatchesGeometricNegation :
  (t : SSP.SSPTrit) →
  Carrier.tritToSSP (Heisenberg.negate3 (Carrier.sspToTrit t))
  ≡ Signed.negateTrit t
heisenbergNegateTritMatchesGeometricNegation SSP.sspNegOne = refl
heisenbergNegateTritMatchesGeometricNegation SSP.sspZero = refl
heisenbergNegateTritMatchesGeometricNegation SSP.sspPosOne = refl

------------------------------------------------------------------------
-- 5. BIDI boundary.
------------------------------------------------------------------------

record HeisenbergGridBidiBoundary : Set where
  constructor heisenbergGridBidiBoundary
  field
    carrierBijectionExists : Bool
    cyclicTranslationTransfersThroughChart : Bool
    cyclicTranslationEqualsNativePathAdjacency : Bool
    wraparoundObstructionExhibited : Bool
    signInversionMatchesGeometricReflection : Bool
    fullHeisenbergActionIsVoxelGraphAction : Bool

canonicalHeisenbergGridBidiBoundary : HeisenbergGridBidiBoundary
canonicalHeisenbergGridBidiBoundary =
  heisenbergGridBidiBoundary true true false true true false
