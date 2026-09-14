module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLigandConditionedLandscapeValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLigandConditionedLandscapeExact as L

------------------------------------------------------------------------
-- RED/GREEN validation root: the AdK NDim landscape is context-indexed.
------------------------------------------------------------------------

contextRegression :
  L.AdKLigandConditionedBoundary.sameGeometricAxesRetainedAcrossContexts
    L.canonicalAdKLigandConditionedBoundary
  ≡ true
  × L.AdKLigandConditionedBoundary.ligandChangesFreeEnergyLandscape
    L.canonicalAdKLigandConditionedBoundary
  ≡ true
contextRegression = refl , refl

boundEnergyRegression :
  L.boundOpenToClosedDeltaGTenthsKcal L.canonicalLigandBoundLandscape ≡ 80
  × L.AdKLigandConditionedBoundary.boundClosedStateEnergeticallyFavoured
    L.canonicalAdKLigandConditionedBoundary
  ≡ true
boundEnergyRegression = refl , refl

pathwayRegression :
  L.AdKLigandConditionedBoundary.boundNmpFirstRegionStronglyUnfavourable
    L.canonicalAdKLigandConditionedBoundary
  ≡ true
  × L.AdKLigandConditionedBoundary.freePathFluxRatioTransfersToBoundContext
    L.canonicalAdKLigandConditionedBoundary
  ≡ false
pathwayRegression = refl , refl

promotionRegression :
  L.AdKLigandConditionedBoundary.deltaGDeterminesFullKinetics
    L.canonicalAdKLigandConditionedBoundary
  ≡ false
  × L.AdKLigandConditionedBoundary.computationalLandscapeEqualsExperimentalPopulation
    L.canonicalAdKLigandConditionedBoundary
  ≡ false
promotionRegression = refl , refl
