module DASHI.Base369Ternary27StratifiedFibreHolonomyValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Stratification
import DASHI.Foundations.Base369Ternary27StratifiedAppraisalFibreExact as Fibre
import DASHI.Foundations.Base369Ternary27StratifiedFibrePlaquetteExact as Plaquette
import DASHI.Moonshine.Base369Ternary27StratifiedFibreHolonomyExact as Holonomy
import DASHI.Moonshine.Base369AppraisalFibreHeisenbergCarrierBidiExact as HeisenbergCarrier
import DASHI.Moonshine.Base369HeisenbergTranslationGridObstructionExact as TranslationAudit
import DASHI.Moonshine.Base369MonsterFineCarrierEquivarianceAuditExact as FineAudit
import DASHI.Moonshine.Base369PeriodicTernaryTorusPathRestrictionBidiExact as Torus
import DASHI.Moonshine.Base369PeriodicHeisenbergFibreEquivarianceExact as PeriodicHeisenberg
import DASHI.Moonshine.Base369DecimalCompletionMonsterBulkBidiExact as DecimalMonster
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as Heisenberg

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
-- Exact 729 appraisal-fibre <-> finite Heisenberg carrier weld.
------------------------------------------------------------------------

heisenbergFibreHas729States :
  HeisenbergCarrier.heisenbergFibreStateCount ≡ 729
heisenbergFibreHas729States = HeisenbergCarrier.heisenbergFibreStateCountIs729

fabricFactorsAs27Times729 :
  HeisenbergCarrier.factorisedFabricStateCount ≡ 19683
fabricFactorsAs27Times729 = HeisenbergCarrier.factorisedFabricStateCountIs19683

fullFabricRoundTripsThroughInteractionAndX6 :
  (p : Geometry.TernaryHyperformalPoint) →
  HeisenbergCarrier.interactionHeisenbergToFabric
    (HeisenbergCarrier.fabricToInteractionHeisenberg p) ≡ p
fullFabricRoundTripsThroughInteractionAndX6 =
  HeisenbergCarrier.fabricHeisenbergRoundTrip

------------------------------------------------------------------------
-- BIDI operator audit: path obstruction and periodic resolution.
------------------------------------------------------------------------

heisenbergAxis0WrapsPositiveToNegative :
  TranslationAudit.heisenbergTranslateFibre Heisenberg.axis0
    TranslationAudit.positiveAxisFibre
  ≡ TranslationAudit.wrappedAxisFibre
heisenbergAxis0WrapsPositiveToNegative =
  TranslationAudit.axis0HeisenbergTranslationWrapsPositiveToNegative

nativeGridRejectsHeisenbergWraparound :
  Geometry.TritGridStep SSP.sspPosOne SSP.sspNegOne → ⊥
nativeGridRejectsHeisenbergWraparound =
  TranslationAudit.nativeGridHasNoPositiveToNegativeStep

carrierDoesNotPromoteTranslationToPathAdjacency :
  TranslationAudit.HeisenbergGridBidiBoundary.cyclicTranslationEqualsNativePathAdjacency
    TranslationAudit.canonicalHeisenbergGridBidiBoundary ≡ false
carrierDoesNotPromoteTranslationToPathAdjacency = refl

signInversionCompatibilityPinned :
  TranslationAudit.HeisenbergGridBidiBoundary.signInversionMatchesGeometricReflection
    TranslationAudit.canonicalHeisenbergGridBidiBoundary ≡ true
signInversionCompatibilityPinned = refl

nativePathEdgeEmbedsInPeriodicTorus :
  Torus.TorusVoxelAdjacent
    TranslationAudit.zeroAxisPoint
    TranslationAudit.positiveAxisPoint
nativePathEdgeEmbedsInPeriodicTorus =
  Torus.pathVoxelEdgeEmbedsInTorus TranslationAudit.zeroToPositiveIsNativeEdge

wraparoundIsPeriodicEdge :
  Torus.TorusVoxelAdjacent
    TranslationAudit.translatedZeroAxisPoint
    TranslationAudit.translatedPositiveAxisPoint
wraparoundIsPeriodicEdge = Torus.heisenbergWrapLivesOnPeriodicTorus

wraparoundIsCutDownstairs :
  Geometry.HypervoxelAdjacent
    TranslationAudit.translatedZeroAxisPoint
    TranslationAudit.translatedPositiveAxisPoint → ⊥
wraparoundIsCutDownstairs = Torus.heisenbergWrapIsCutByPathRestriction

allSixHeisenbergTranslationsArePeriodicAutomorphisms :
  PeriodicHeisenberg.PeriodicHeisenbergEquivarianceBoundary.allSixTranslationsArePeriodicGraphAutomorphisms
    PeriodicHeisenberg.canonicalPeriodicHeisenbergEquivarianceBoundary ≡ true
allSixHeisenbergTranslationsArePeriodicAutomorphisms = refl

allSixHeisenbergTranslationsAreNotPathAutomorphisms :
  PeriodicHeisenberg.PeriodicHeisenbergEquivarianceBoundary.allSixTranslationsArePathGraphAutomorphisms
    PeriodicHeisenberg.canonicalPeriodicHeisenbergEquivarianceBoundary ≡ false
allSixHeisenbergTranslationsAreNotPathAutomorphisms = refl

------------------------------------------------------------------------
-- 19683 harmonic fine-carrier audit.
------------------------------------------------------------------------

geometricAndHarmonicFineCountsAgree :
  FineAudit.geometricFineCount ≡ FineAudit.harmonicFineCount
geometricAndHarmonicFineCountsAgree = FineAudit.fineCountsAgree

geometryReconstructsMonsterBulkCount :
  FineAudit.monsterBulkFromGeometry ≡ 196830
geometryReconstructsMonsterBulkCount = FineAudit.monsterBulkFromGeometryIs196830

sameCountNotPromotedToEquivariance :
  FineAudit.FineCarrierBidiBoundary.sameCardinalityTreatedAsEquivariance
    FineAudit.canonicalFineCarrierBidiBoundary ≡ false
sameCountNotPromotedToEquivariance = refl

canonicalFinChartStillRequired :
  FineAudit.FineCarrierBidiBoundary.canonicalFin19683NineTritChartConstructed
    FineAudit.canonicalFineCarrierBidiBoundary ≡ false
canonicalFinChartStillRequired = refl

fullMonsterActionStillNotEstablished :
  FineAudit.FineCarrierBidiBoundary.fullMonsterActionOnHyperfabricEstablished
    FineAudit.canonicalFineCarrierBidiBoundary ≡ false
fullMonsterActionStillNotEstablished = refl

------------------------------------------------------------------------
-- Decimal / completion / 10 x fine Monster ledger.
------------------------------------------------------------------------

nineOrdinaryPlusCompletionIsTen : DecimalMonster.coarseWithCompletionCount ≡ 10
nineOrdinaryPlusCompletionIsTen = DecimalMonster.coarseWithCompletionCountIsTen

tenTimesBase369FineIs196830 : DecimalMonster.base369TenChannelBulk ≡ 196830
tenTimesBase369FineIs196830 = DecimalMonster.base369TenChannelBulkIs196830

base369BulkPlus53IsMonsterDimension :
  DecimalMonster.monsterDimensionFromBase369Bulk ≡ 196883
base369BulkPlus53IsMonsterDimension = DecimalMonster.monsterDimensionFromBase369BulkIs196883

base369BulkPlus54IsMoonshineWeightTwo :
  DecimalMonster.moonshineWeightTwoFromBase369Bulk ≡ 196884
base369BulkPlus54IsMoonshineWeightTwo = DecimalMonster.moonshineWeightTwoFromBase369BulkIs196884

nineTenthsThreeAxisNumeratorIsFineCarrier :
  DecimalMonster.ninetyPercentThreeAxisNumeratorIsHyperfabric ≡
  DecimalMonster.ninetyPercentThreeAxisNumeratorIsHyperfabric
nineTenthsThreeAxisNumeratorIsFineCarrier = refl

tenOverNineCarryAtNineIsExact :
  DecimalMonster.DecimalCompletionMonsterBulkBoundary.tenOverNineCompletionIdentityAvailable
    DecimalMonster.canonicalDecimalCompletionMonsterBulkBoundary ≡ true
tenOverNineCarryAtNineIsExact = refl

decimalArithmeticNotPromotedToMonsterCause :
  DecimalMonster.DecimalCompletionMonsterBulkBoundary.decimalLadderCausesMonsterDimension
    DecimalMonster.canonicalDecimalCompletionMonsterBulkBoundary ≡ false
decimalArithmeticNotPromotedToMonsterCause = refl

------------------------------------------------------------------------
-- Existing non-promotion boundaries.
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
