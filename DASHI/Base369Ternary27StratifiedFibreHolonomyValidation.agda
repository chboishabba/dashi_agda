module DASHI.Base369Ternary27StratifiedFibreHolonomyValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Stratification
import DASHI.Foundations.Base369Ternary27StratifiedAppraisalFibreExact as Fibre
import DASHI.Foundations.Base369Ternary27StratifiedFibrePlaquetteExact as Plaquette
import DASHI.Moonshine.Base369Ternary27StratifiedFibreHolonomyExact as Holonomy

------------------------------------------------------------------------
-- Stratified fibre cardinalities.
------------------------------------------------------------------------

centreLayerHas729States : Fibre.centreFibreStateCount ≡ 729
centreLayerHas729States = Fibre.centreFibreStateCountIs729

faceLayerHas4374States : Fibre.faceCentreFibreStateCount ≡ 4374
faceLayerHas4374States = Fibre.faceCentreFibreStateCountIs4374

edgeLayerHas8748States : Fibre.edgeCentreFibreStateCount ≡ 8748
edgeLayerHas8748States = Fibre.edgeCentreFibreStateCountIs8748

cornerLayerHas5832States : Fibre.cornerFibreStateCount ≡ 5832
cornerLayerHas5832States = Fibre.cornerFibreStateCountIs5832

liftedStrataRecoverWholeFabric : Fibre.stratifiedFabricStateCount ≡ 19683
liftedStrataRecoverWholeFabric = Fibre.stratifiedFabricStateCountIs19683

------------------------------------------------------------------------
-- Concrete unit plaquette and fibre lift.
------------------------------------------------------------------------

lowerPlaquetteItineraryPinned :
  Plaquette.plaquetteStrata Plaquette.lowerXYPlaquette ≡
  Plaquette.plaquetteStratumItinerary
    Stratification.edgeCentreStratum
    Stratification.faceCentreStratum
    Stratification.centreStratum
    Stratification.faceCentreStratum
lowerPlaquetteItineraryPinned = Plaquette.lowerXYStratumItinerary

plaquetteLiftStaysOverOrigin00 :
  Geometry.projectInteractionVoxel
    (Plaquette.liftA00 Geometry.origin Plaquette.originFibreLowerXY)
  ≡ Geometry.origin
plaquetteLiftStaysOverOrigin00 = Plaquette.originFibrePlaquetteBasePinned00

plaquetteLiftStaysOverOrigin11 :
  Geometry.projectInteractionVoxel
    (Plaquette.liftA11 Geometry.origin Plaquette.originFibreLowerXY)
  ≡ Geometry.origin
plaquetteLiftStaysOverOrigin11 = Plaquette.originFibrePlaquetteBasePinned11

------------------------------------------------------------------------
-- Vertical holonomy/order defect.
------------------------------------------------------------------------

orderedEndpointsAreDifferent :
  Holonomy.flipThenSwapEndpoint ≡ Holonomy.swapThenFlipEndpoint → ⊥
orderedEndpointsAreDifferent = Holonomy.orderedFibreEndpointsDiffer

orderedEndpointsHaveSameBase :
  Geometry.projectInteractionVoxel Holonomy.flipThenSwapEndpoint
  ≡ Geometry.projectInteractionVoxel Holonomy.swapThenFlipEndpoint
orderedEndpointsHaveSameBase = Holonomy.orderedEndpointsShareInteractionBase

orderedEndpointsHaveSameCoarseStratum :
  Stratification.fabricStratum Holonomy.flipThenSwapEndpoint
  ≡ Stratification.fabricStratum Holonomy.swapThenFlipEndpoint
orderedEndpointsHaveSameCoarseStratum = Holonomy.orderedEndpointsShareFabricStratum

coarseStratumCannotDecodeOrder :
  Holonomy.FactorsTransportOrderThroughStratum → ⊥
coarseStratumCannotDecodeOrder = Holonomy.stratumCannotRecoverTransportOrder

frequencyOrderDefectPinned :
  Holonomy.frequencyFlipThenSwap ≡ Holonomy.frequencySwapThenFlip → ⊥
frequencyOrderDefectPinned = Holonomy.frequencyTransportOrdersDiffer

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

sameStratumDoesNotMeanSameFineEndpoint :
  Holonomy.StratifiedFibreHolonomyBoundary.sameStratumImpliesSameFineEndpoint
    Holonomy.canonicalStratifiedFibreHolonomyBoundary ≡ false
sameStratumDoesNotMeanSameFineEndpoint = refl

sameBaseDoesNotMeanSameFibrePoint :
  Holonomy.StratifiedFibreHolonomyBoundary.sameBaseImpliesSameFibrePoint
    Holonomy.canonicalStratifiedFibreHolonomyBoundary ≡ false
sameBaseDoesNotMeanSameFibrePoint = refl

spectralDefectNotPromotedToGaugeCurvature :
  Holonomy.StratifiedFibreHolonomyBoundary.spectralOrderDefectIsGaugeCurvature
    Holonomy.canonicalStratifiedFibreHolonomyBoundary ≡ false
spectralDefectNotPromotedToGaugeCurvature = refl

plaquetteDoesNotClaimGaugeConnection :
  Plaquette.StratifiedFibrePlaquetteBoundary.gaugeConnectionAssignedToEdges
    Plaquette.canonicalStratifiedFibrePlaquetteBoundary ≡ false
plaquetteDoesNotClaimGaugeConnection = refl

plaquetteDoesNotClaimWilsonLoop :
  Plaquette.StratifiedFibrePlaquetteBoundary.wilsonLoopComputed
    Plaquette.canonicalStratifiedFibrePlaquetteBoundary ≡ false
plaquetteDoesNotClaimWilsonLoop = refl

monsterModuleStillNotClaimed :
  Holonomy.StratifiedFibreHolonomyBoundary.monsterIntertwinerMakesVoxelMonsterModule
    Holonomy.canonicalStratifiedFibreHolonomyBoundary ≡ false
monsterModuleStillNotClaimed = refl
