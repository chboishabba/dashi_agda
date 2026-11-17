module DASHI.Biology.KitzerowBH4RedoxSpatialDiscriminatorValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Biology.KitzerowBH4RedoxSpatialDiscriminatorExact as RedoxSpatial

redoxRegenerationAndSpatialTopologyArePaidWithoutScalarPoolPromotion :
  RedoxSpatial.nadphRegenerationRelevant RedoxSpatial.canonicalRedoxSpatialBoundary ≡ true
  × RedoxSpatial.intracellularExtracellularRouteDistinctionPaid RedoxSpatial.canonicalRedoxSpatialBoundary ≡ true
  × RedoxSpatial.scalarWellMixedPoolSufficient RedoxSpatial.canonicalRedoxSpatialBoundary ≡ false
redoxRegenerationAndSpatialTopologyArePaidWithoutScalarPoolPromotion = refl , (refl , refl)

cellularUptakeAndFunctionalCrossTalkArePaidWithoutInventingFlux :
  RedoxSpatial.cellularBH4UptakeDirectlyMeasured RedoxSpatial.canonicalRedoxSpatialBoundary ≡ true
  × RedoxSpatial.specificMembraneCarrierRequiredByUptakeStudy RedoxSpatial.canonicalRedoxSpatialBoundary ≡ false
  × RedoxSpatial.functionalCocultureCrossTalkSupported RedoxSpatial.canonicalRedoxSpatialBoundary ≡ true
  × RedoxSpatial.intercellBH4TransferDirectlyMeasured RedoxSpatial.canonicalRedoxSpatialBoundary ≡ false
cellularUptakeAndFunctionalCrossTalkArePaidWithoutInventingFlux =
  refl , (refl , (refl , refl))

neuralSupplyAndConsumptionNeedNotBeColocalized :
  RedoxSpatial.gtpchAndNnosMustBeSameCell RedoxSpatial.canonicalRedoxSpatialBoundary ≡ false
  × RedoxSpatial.intercellBH4TransferDirectlyMeasured RedoxSpatial.canonicalRedoxSpatialBoundary ≡ false
neuralSupplyAndConsumptionNeedNotBeColocalized = refl , refl

striatalRouteAmbiguityBlocksNaiveCofactorInterpretation :
  RedoxSpatial.exogenousBH4EffectRequiresTHOrNOS RedoxSpatial.canonicalRedoxSpatialBoundary ≡ false
  × RedoxSpatial.intracellularBH4CanEngageTHAndNOS RedoxSpatial.canonicalRedoxSpatialBoundary ≡ true
striatalRouteAmbiguityBlocksNaiveCofactorInterpretation = refl , refl

topologyResolvedBalanceReplacesScalarAsSufficientStateWithoutInventingFlux :
  RedoxSpatial.topologyResolvedStateRequired RedoxSpatial.canonicalTopologyResolvedPoolBalance ≡ true
  × RedoxSpatial.scalarProjectionIsLossy RedoxSpatial.canonicalTopologyResolvedPoolBalance ≡ true
  × RedoxSpatial.numericEdgeFluxesPaid RedoxSpatial.canonicalTopologyResolvedPoolBalance ≡ false
  × RedoxSpatial.directTransferFluxPaid RedoxSpatial.canonicalTopologyResolvedPoolBalance ≡ false
topologyResolvedBalanceReplacesScalarAsSufficientStateWithoutInventingFlux =
  refl , (refl , (refl , refl))

redoxSpatialEvidenceDoesNotCloseWholeAllocator :
  RedoxSpatial.redoxSpatialEvidenceClosesWholeAllocator RedoxSpatial.canonicalRedoxSpatialBoundary ≡ false
redoxSpatialEvidenceDoesNotCloseWholeAllocator = refl
