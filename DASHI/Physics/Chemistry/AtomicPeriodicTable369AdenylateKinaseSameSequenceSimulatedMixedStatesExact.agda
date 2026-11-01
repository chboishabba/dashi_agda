module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSameSequenceSimulatedMixedStatesExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseConformationalEmpiricalExact as AdK
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseNDimGeometricResidualExact as Geo
import DASHI.ComputerScience.FlyStructureFunctionNDimFibreExact as FlyNDim

------------------------------------------------------------------------
-- SAME-SEQUENCE COMPUTATIONAL FOUR-CORNER CARRIER
--
-- Ping et al. 2013 (DOI 10.1155/2013/628536) use the E. coli AdK open/closed
-- crystal endpoints 4AKE/1AKE and report four major clusters in the two domain-
-- distance chart.  Besides the open/open and closed/closed endpoint clusters,
-- the study identifies configurations with:
--
--   closed NMP + open LID
--   open NMP   + closed LID.
--
-- This is stronger than the cross-homolog 4-PDB reference square because the
-- mixed configurations arise inside one E. coli simulation carrier.  It is also
-- weaker than four experimentally resolved same-sequence structures: the mixed
-- corners are computational configurations, not separate experimental PDB
-- deposits.  Their appearance establishes that the two coarse domain-state
-- coordinates are not locked to the diagonal in this simulation; it does not
-- establish thermodynamic independence, kinetic independence, equilibrium
-- populations, or a unique transition mechanism.
------------------------------------------------------------------------

data DomainGateState : Set where
  domainOpen : DomainGateState
  domainClosed : DomainGateState

data SameSequenceSimulationCluster : Set where
  openOpenCluster : SameSequenceSimulationCluster
  closedClosedCluster : SameSequenceSimulationCluster
  closedNMPOpenLIDCluster : SameSequenceSimulationCluster
  openNMPClosedLIDCluster : SameSequenceSimulationCluster

nmpState : SameSequenceSimulationCluster → DomainGateState
nmpState openOpenCluster = domainOpen
nmpState closedClosedCluster = domainClosed
nmpState closedNMPOpenLIDCluster = domainClosed
nmpState openNMPClosedLIDCluster = domainOpen

lidState : SameSequenceSimulationCluster → DomainGateState
lidState openOpenCluster = domainOpen
lidState closedClosedCluster = domainClosed
lidState closedNMPOpenLIDCluster = domainOpen
lidState openNMPClosedLIDCluster = domainClosed

mixedClosedNMPOpenLIDIsOffDiagonal :
  nmpState closedNMPOpenLIDCluster ≡ lidState closedNMPOpenLIDCluster → ⊥
mixedClosedNMPOpenLIDIsOffDiagonal ()

mixedOpenNMPClosedLIDIsOffDiagonal :
  nmpState openNMPClosedLIDCluster ≡ lidState openNMPClosedLIDCluster → ⊥
mixedOpenNMPClosedLIDIsOffDiagonal ()

-- The same-sequence identity is inherited from the source-paid 4AKE/1AKE pair.
samePrimarySequenceInherited :
  AdK.primarySequence AdK.pdb4AKEState ≡ AdK.primarySequence AdK.pdb1AKEState
samePrimarySequenceInherited = AdK.samePrimarySequence

-- Reuse the measured endpoint residual carrier without claiming that the mixed
-- clusters have exact source-paid numeric coordinates in this owner.
endpointGeometricResidualSurface : Set
endpointGeometricResidualSurface = Geo.AdKGeometricResidual

-- Reuse the NDim selection discipline: keep axes separate and do not promote
-- more coordinates into automatic consumer improvement.
flyNDimDisciplineDonor : FlyNDim.FlyNDimStructureFunctionBoundary
flyNDimDisciplineDonor = FlyNDim.canonicalFlyNDimStructureFunctionBoundary

------------------------------------------------------------------------
-- Snowball attribution.
------------------------------------------------------------------------

record SameSequenceMixedSourceCoordinate : Set where
  constructor same-sequence-mixed-source-coordinate
  field
    label : String
    doi : String
    qid : String
    pdb : String
    uniprot : String
    dewey : String
    directLink : String
    oeis : String
    primaryStatus : String
    sourceRole : String

ping2013SameSequenceMixedClusters : SameSequenceMixedSourceCoordinate
ping2013SameSequenceMixedClusters =
  same-sequence-mixed-source-coordinate
    "Ping et al. 2013 E. coli adenylate-kinase MD mixed-domain clusters"
    "10.1155/2013/628536"
    "source-article QID unresolved; adenylate kinase Q356240"
    "4AKE open endpoint; 1AKE closed endpoint; mixed corners are simulated rather than PDB deposits"
    "P69441"
    "exact article-level Dewey unresolved"
    "https://doi.org/10.1155/2013/628536"
    "not an integer-sequence object; no same-object OEIS coordinate"
    "peer-reviewed computational molecular-dynamics study using experimental E. coli crystal endpoints"
    "reports four major two-distance clusters, including open-LID/closed-NMP and open-NMP/closed-LID configurations"

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record SameSequenceSimulatedMixedBoundary : Set where
  constructor same-sequence-simulated-mixed-boundary
  field
    sameSequenceSimulationCarrierPaid : Bool
    sameSequenceSimulationCarrierPaidIsTrue :
      sameSequenceSimulationCarrierPaid ≡ true

    openOpenObserved : Bool
    openOpenObservedIsTrue : openOpenObserved ≡ true

    closedClosedObserved : Bool
    closedClosedObservedIsTrue : closedClosedObserved ≡ true

    closedNMPOpenLIDObserved : Bool
    closedNMPOpenLIDObservedIsTrue : closedNMPOpenLIDObserved ≡ true

    openNMPClosedLIDObserved : Bool
    openNMPClosedLIDObservedIsTrue : openNMPClosedLIDObserved ≡ true

    offDiagonalSimulationStatesPaid : Bool
    offDiagonalSimulationStatesPaidIsTrue : offDiagonalSimulationStatesPaid ≡ true

    nmpAndLidLockedToSameBinaryStateInSimulation : Bool
    nmpAndLidLockedToSameBinaryStateInSimulationIsFalse :
      nmpAndLidLockedToSameBinaryStateInSimulation ≡ false

    fourSimulationClustersEqualFourExperimentalPDBStates : Bool
    fourSimulationClustersEqualFourExperimentalPDBStatesIsFalse :
      fourSimulationClustersEqualFourExperimentalPDBStates ≡ false

    mixedClustersProveThermodynamicIndependence : Bool
    mixedClustersProveThermodynamicIndependenceIsFalse :
      mixedClustersProveThermodynamicIndependence ≡ false

    mixedClustersProveKineticIndependence : Bool
    mixedClustersProveKineticIndependenceIsFalse :
      mixedClustersProveKineticIndependence ≡ false

    mixedClustersProveUniqueTransitionPath : Bool
    mixedClustersProveUniqueTransitionPathIsFalse :
      mixedClustersProveUniqueTransitionPath ≡ false

    mixedClusterEquilibriumPopulationsPaid : Bool
    mixedClusterEquilibriumPopulationsPaidIsFalse :
      mixedClusterEquilibriumPopulationsPaid ≡ false

    mixedClusterExactNumericCoordinatesPaidHere : Bool
    mixedClusterExactNumericCoordinatesPaidHereIsFalse :
      mixedClusterExactNumericCoordinatesPaidHere ≡ false

    sameSequenceComputationalSquareSupportsAxisRefinement : Bool
    sameSequenceComputationalSquareSupportsAxisRefinementIsTrue :
      sameSequenceComputationalSquareSupportsAxisRefinement ≡ true

canonicalSameSequenceSimulatedMixedBoundary : SameSequenceSimulatedMixedBoundary
canonicalSameSequenceSimulatedMixedBoundary =
  same-sequence-simulated-mixed-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
