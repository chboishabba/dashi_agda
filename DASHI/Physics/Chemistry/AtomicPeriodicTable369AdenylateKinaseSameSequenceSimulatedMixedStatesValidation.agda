module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSameSequenceSimulatedMixedStatesValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSameSequenceSimulatedMixedStatesExact as S

------------------------------------------------------------------------
-- RED/GREEN validation root for the same-sequence computational mixed-state
-- witness.  This must stay distinct from the cross-homolog PDB reference square:
-- the claim here is only that the Ping et al. E. coli MD carrier reports both
-- mixed domain combinations in addition to open/open and closed/closed clusters.
------------------------------------------------------------------------

fourCornerSimulationRegression :
  S.SameSequenceSimulatedMixedBoundary.sameSequenceSimulationCarrierPaid
    S.canonicalSameSequenceSimulatedMixedBoundary
  ≡ true
  × S.SameSequenceSimulatedMixedBoundary.openOpenObserved
    S.canonicalSameSequenceSimulatedMixedBoundary
  ≡ true
  × S.SameSequenceSimulatedMixedBoundary.closedClosedObserved
    S.canonicalSameSequenceSimulatedMixedBoundary
  ≡ true
  × S.SameSequenceSimulatedMixedBoundary.closedNMPOpenLIDObserved
    S.canonicalSameSequenceSimulatedMixedBoundary
  ≡ true
  × S.SameSequenceSimulatedMixedBoundary.openNMPClosedLIDObserved
    S.canonicalSameSequenceSimulatedMixedBoundary
  ≡ true
fourCornerSimulationRegression = refl , refl , refl , refl , refl

promotionRegression :
  S.SameSequenceSimulatedMixedBoundary.fourSimulationClustersEqualFourExperimentalPDBStates
    S.canonicalSameSequenceSimulatedMixedBoundary
  ≡ false
  × S.SameSequenceSimulatedMixedBoundary.mixedClustersProveThermodynamicIndependence
    S.canonicalSameSequenceSimulatedMixedBoundary
  ≡ false
  × S.SameSequenceSimulatedMixedBoundary.mixedClustersProveKineticIndependence
    S.canonicalSameSequenceSimulatedMixedBoundary
  ≡ false
  × S.SameSequenceSimulatedMixedBoundary.mixedClustersProveUniqueTransitionPath
    S.canonicalSameSequenceSimulatedMixedBoundary
  ≡ false
promotionRegression = refl , refl , refl , refl
