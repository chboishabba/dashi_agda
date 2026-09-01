module DASHI.Moonshine.Base369Ternary27StratifiedFibreHolonomyExact where

------------------------------------------------------------------------
-- STRATIFIED FIBRE HOLONOMY ANALOGUE ON THE 27^3 BASE369 HYPERFABRIC
--
-- Two exact graph symmetries act on appraisal-A while leaving the interaction
-- base and appraisal-B fixed:
--
--   S = swap appraisal-A x/y coordinates
--   F = reflect appraisal-A x coordinate
--
-- They do not commute on a concrete fibre point.  The ordered endpoints stay
-- over the same interaction base and even in the same coarse product stratum.
-- Thus base projection and stratum projection cannot recover transport order.
--
-- This is an algebraic/cubical holonomy analogue only.  No gauge connection,
-- curvature two-form, Wilson action, Monster representation, or physical field
-- is asserted by this module.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Stratification
import DASHI.Foundations.Base369Ternary27StratifiedAppraisalFibreExact as Fibre
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral
import DASHI.Moonshine.Base369Ternary27SignedSymmetryMonsterIntertwinerExact as Signed
import DASHI.Core.CubieFaceOrderHolonomyAnalogueExact as PriorHolonomy

------------------------------------------------------------------------
-- 1. Fibre-preserving transports.
------------------------------------------------------------------------

swapAppraisalAXY :
  Geometry.TernaryHyperformalPoint → Geometry.TernaryHyperformalPoint
swapAppraisalAXY (Geometry.ternaryHyperformalPoint i a b) =
  Geometry.ternaryHyperformalPoint i (Spectral.swapXY a) b

flipAppraisalAX :
  Geometry.TernaryHyperformalPoint → Geometry.TernaryHyperformalPoint
flipAppraisalAX (Geometry.ternaryHyperformalPoint i a b) =
  Geometry.ternaryHyperformalPoint i (Signed.flipX a) b

swapPreservesInteractionBase :
  (p : Geometry.TernaryHyperformalPoint) →
  Geometry.projectInteractionVoxel (swapAppraisalAXY p)
  ≡ Geometry.projectInteractionVoxel p
swapPreservesInteractionBase (Geometry.ternaryHyperformalPoint i a b) = refl

flipPreservesInteractionBase :
  (p : Geometry.TernaryHyperformalPoint) →
  Geometry.projectInteractionVoxel (flipAppraisalAX p)
  ≡ Geometry.projectInteractionVoxel p
flipPreservesInteractionBase (Geometry.ternaryHyperformalPoint i a b) = refl

------------------------------------------------------------------------
-- 2. Concrete noncommuting transport witness in the origin fibre.
------------------------------------------------------------------------

seedAppraisal : Geometry.Ternary27Point
seedAppraisal =
  Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero

fibreSeed : Geometry.TernaryHyperformalPoint
fibreSeed =
  Geometry.ternaryHyperformalPoint Geometry.origin seedAppraisal Geometry.origin

flipThenSwapEndpoint : Geometry.TernaryHyperformalPoint
flipThenSwapEndpoint = swapAppraisalAXY (flipAppraisalAX fibreSeed)

swapThenFlipEndpoint : Geometry.TernaryHyperformalPoint
swapThenFlipEndpoint = flipAppraisalAX (swapAppraisalAXY fibreSeed)

orderedFibreEndpointsDiffer :
  flipThenSwapEndpoint ≡ swapThenFlipEndpoint → ⊥
orderedFibreEndpointsDiffer ()

flipThenSwapAppraisalIsNegativeY :
  Geometry.appraisalAVoxel flipThenSwapEndpoint
  ≡ Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero
flipThenSwapAppraisalIsNegativeY = refl

swapThenFlipAppraisalIsPositiveY :
  Geometry.appraisalAVoxel swapThenFlipEndpoint
  ≡ Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero
swapThenFlipAppraisalIsPositiveY = refl

------------------------------------------------------------------------
-- 3. The defect is vertical: both endpoints remain over the same base.
------------------------------------------------------------------------

flipThenSwapBaseIsOrigin :
  Geometry.projectInteractionVoxel flipThenSwapEndpoint ≡ Geometry.origin
flipThenSwapBaseIsOrigin = refl

swapThenFlipBaseIsOrigin :
  Geometry.projectInteractionVoxel swapThenFlipEndpoint ≡ Geometry.origin
swapThenFlipBaseIsOrigin = refl

orderedEndpointsShareInteractionBase :
  Geometry.projectInteractionVoxel flipThenSwapEndpoint
  ≡ Geometry.projectInteractionVoxel swapThenFlipEndpoint
orderedEndpointsShareInteractionBase = refl

------------------------------------------------------------------------
-- 4. They also share the same coarse product stratum.
------------------------------------------------------------------------

flipThenSwapFabricStratum :
  Stratification.fabricStratum flipThenSwapEndpoint
  ≡ Stratification.fabricStratum3
      Stratification.centreStratum
      Stratification.faceCentreStratum
      Stratification.centreStratum
flipThenSwapFabricStratum = refl

swapThenFlipFabricStratum :
  Stratification.fabricStratum swapThenFlipEndpoint
  ≡ Stratification.fabricStratum3
      Stratification.centreStratum
      Stratification.faceCentreStratum
      Stratification.centreStratum
swapThenFlipFabricStratum = refl

orderedEndpointsShareFabricStratum :
  Stratification.fabricStratum flipThenSwapEndpoint
  ≡ Stratification.fabricStratum swapThenFlipEndpoint
orderedEndpointsShareFabricStratum = refl

------------------------------------------------------------------------
-- 5. Finite non-factorability through the coarse stratum surface.
------------------------------------------------------------------------

data TransportOrder : Set where
  flipThenSwap
  swapThenFlip
  : TransportOrder

routeEndpoint : TransportOrder → Geometry.TernaryHyperformalPoint
routeEndpoint flipThenSwap = flipThenSwapEndpoint
routeEndpoint swapThenFlip = swapThenFlipEndpoint

routeSurface : TransportOrder → Stratification.FabricStratum3
routeSurface order = Stratification.fabricStratum (routeEndpoint order)

record FactorsTransportOrderThroughStratum : Set where
  constructor factorsTransportOrderThroughStratum
  field
    decode : Stratification.FabricStratum3 → TransportOrder
    factor : (order : TransportOrder) → decode (routeSurface order) ≡ order
open FactorsTransportOrderThroughStratum public

stratumCannotRecoverTransportOrder :
  FactorsTransportOrderThroughStratum → ⊥
stratumCannotRecoverTransportOrder witness with decode witness (routeSurface flipThenSwap)
... | flipThenSwap with factor witness flipThenSwap | factor witness swapThenFlip
...   | refl | ()
... | swapThenFlip with factor witness flipThenSwap
...   | ()

------------------------------------------------------------------------
-- 6. The same order defect appears on C3^3 frequency labels.
------------------------------------------------------------------------

frequencySeed : Spectral.CubeFrequencySector
frequencySeed =
  Spectral.cubeFrequencySector
    Spectral.frequencyPositive
    Spectral.frequencyZero
    Spectral.frequencyZero

frequencyFlipThenSwap : Spectral.CubeFrequencySector
frequencyFlipThenSwap =
  Spectral.swapSectorXY (Signed.reflectFrequencyX frequencySeed)

frequencySwapThenFlip : Spectral.CubeFrequencySector
frequencySwapThenFlip =
  Signed.reflectFrequencyX (Spectral.swapSectorXY frequencySeed)

frequencyFlipThenSwapIsNegativeY :
  frequencyFlipThenSwap
  ≡ Spectral.cubeFrequencySector
      Spectral.frequencyZero
      Spectral.frequencyNegative
      Spectral.frequencyZero
frequencyFlipThenSwapIsNegativeY = refl

frequencySwapThenFlipIsPositiveY :
  frequencySwapThenFlip
  ≡ Spectral.cubeFrequencySector
      Spectral.frequencyZero
      Spectral.frequencyPositive
      Spectral.frequencyZero
frequencySwapThenFlipIsPositiveY = refl

frequencyTransportOrdersDiffer :
  frequencyFlipThenSwap ≡ frequencySwapThenFlip → ⊥
frequencyTransportOrdersDiffer ()

------------------------------------------------------------------------
-- 7. Cross-pollination receipt with the older generic cubie holonomy owner.
------------------------------------------------------------------------

record StratifiedFibreHolonomyCrossPollination : Set where
  constructor stratifiedFibreHolonomyCrossPollination
  field
    priorGenericNoncommutingHiddenTransportExists : Bool
    currentTransportActsInsideFixedInteractionFibre : Bool
    orderedEndpointsDiffer : Bool
    orderedEndpointsShareBase : Bool
    orderedEndpointsShareProductStratum : Bool
    frequencyLabelsRetainOrderDefect : Bool
    monsterPhaseConjugationAvailableForReflectionLeg : Bool
    literalGaugeConnectionConstructed : Bool
    wilsonLoopComputed : Bool
    monsterRepresentationEstablished : Bool

canonicalStratifiedFibreHolonomyCrossPollination :
  StratifiedFibreHolonomyCrossPollination
canonicalStratifiedFibreHolonomyCrossPollination =
  stratifiedFibreHolonomyCrossPollination
    (PriorHolonomy.CubieHolonomyBoundary.noncommutingHiddenTransportExists
      PriorHolonomy.canonicalCubieHolonomyBoundary)
    true true true true true
    (Signed.SignedTernaryVoxelSymmetryBoundary.monster3BPhaseInversionMatchesFrequencyConjugation
      Signed.canonicalSignedTernaryVoxelSymmetryBoundary)
    false false false

------------------------------------------------------------------------
-- 8. Boundary: fibre, stratum, spectral defect and physical holonomy differ.
------------------------------------------------------------------------

record StratifiedFibreHolonomyBoundary : Set where
  constructor stratifiedFibreHolonomyBoundary
  field
    verticalNoncommutativityEstablished : Bool
    coarseStratumErasesTransportOrder : Bool
    spectralOrderDefectEstablished : Bool
    sameStratumImpliesSameFineEndpoint : Bool
    sameBaseImpliesSameFibrePoint : Bool
    spectralOrderDefectIsGaugeCurvature : Bool
    monsterIntertwinerMakesVoxelMonsterModule : Bool

canonicalStratifiedFibreHolonomyBoundary : StratifiedFibreHolonomyBoundary
canonicalStratifiedFibreHolonomyBoundary =
  stratifiedFibreHolonomyBoundary true true true false false false false
