module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCouplingResidualExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSameSequenceSimulatedMixedStatesExact as Mixed
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseNDimGeometricResidualExact as Geometry

------------------------------------------------------------------------
-- ADENYLATE-KINASE NMP/LID DYNAMICAL COUPLING RESIDUAL
--
-- Off-diagonal mixed states establish that NMP/LID are not locked to one
-- diagonal open/closed coordinate in the same-sequence simulation carrier.
-- They do not establish independence.  Li, Liu & Ji 2015 provide a stronger
-- dynamical receipt: both closure orders are observed in ligand-free AdK and a
-- source-derived pathway-flux ratio is approximately 5.7 : 1 in favour of the
-- LID-first route.  This owner stores that asymmetry as a coupling residual.
--
-- Ratio is encoded as 57/10 to avoid floating equality in the proof layer.
------------------------------------------------------------------------

data DomainClosureOrder : Set where
  lidThenNmp : DomainClosureOrder
  nmpThenLid : DomainClosureOrder

data CouplingEvidenceKind : Set where
  reachabilityEvidence : CouplingEvidenceKind
  pathwayOrderEvidence : CouplingEvidenceKind
  relativeFluxEvidence : CouplingEvidenceKind
  freeEnergyLandscapeEvidence : CouplingEvidenceKind

record AdKCouplingResidual : Set where
  constructor adk-coupling-residual
  field
    primaryOrder : DomainClosureOrder
    alternativeOrder : DomainClosureOrder
    primaryFluxNumerator : Nat
    primaryFluxDenominator : Nat
    ratioScaleDescription : String
open AdKCouplingResidual public

canonicalCouplingResidual : AdKCouplingResidual
canonicalCouplingResidual =
  adk-coupling-residual
    lidThenNmp
    nmpThenLid
    57
    10
    "source reports approximate relative pathway flux 5.7 : 1; encoded as 57/10"

ordersDiffer : lidThenNmp ≡ nmpThenLid → ⊥
ordersDiffer ()

------------------------------------------------------------------------
-- Existing same-carrier and geometric donors.
------------------------------------------------------------------------

sameSequenceMixedStateDonor : Mixed.SameSequenceSimulatedMixedStateBoundary
sameSequenceMixedStateDonor = Mixed.canonicalSameSequenceSimulatedMixedStateBoundary

geometricResidualDonor : Geometry.AdKNDimGeometricBoundary
geometricResidualDonor = Geometry.canonicalAdKNDimGeometricBoundary

------------------------------------------------------------------------
-- Snowball attribution.
------------------------------------------------------------------------

record CouplingSourceCoordinate : Set where
  constructor coupling-source-coordinate
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

liLiuJi2015DynamicsLandscape : CouplingSourceCoordinate
liLiuJi2015DynamicsLandscape =
  coupling-source-coordinate
    "Li, Liu and Ji 2015, Mapping the Dynamics Landscape of Conformational Transitions in Enzyme: The Adenylate Kinase Case"
    "10.1016/j.bpj.2015.06.059"
    "source-article QID unresolved in inspected sources; adenylate kinase Q356240"
    "4AKE open and 1AKE closed endpoint coordinates"
    "P69441"
    "exact article-level Dewey unresolved"
    "https://doi.org/10.1016/j.bpj.2015.06.059"
    "not an integer-sequence object; no same-object OEIS coordinate"
    "peer-reviewed computational dynamics / free-energy-landscape study"
    "pays observed LID-first and NMP-first ligand-free pathways and approximate relative pathway flux 5.7:1 favouring LID-first closure"

ping2013SameSequenceMixedStates : CouplingSourceCoordinate
ping2013SameSequenceMixedStates =
  coupling-source-coordinate
    "Ping et al. 2013 same-sequence E. coli AdK conformational transitions"
    "10.1155/2013/628536"
    "source-article QID unresolved in inspected sources; adenylate kinase Q356240"
    "4AKE / 1AKE"
    "P69441"
    "exact article-level Dewey unresolved"
    "https://doi.org/10.1155/2013/628536"
    "not an integer-sequence object; no same-object OEIS coordinate"
    "peer-reviewed computational molecular-dynamics study"
    "pays same-sequence simulated mixed-state reachability; does not pay the later 5.7:1 pathway-flux estimate"

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record AdKCouplingBoundary : Set where
  constructor adk-coupling-boundary
  field
    sameSequenceOffDiagonalReachabilityPaid : Bool
    sameSequenceOffDiagonalReachabilityPaidIsTrue :
      sameSequenceOffDiagonalReachabilityPaid ≡ true

    lidFirstPathwayObserved : Bool
    lidFirstPathwayObservedIsTrue : lidFirstPathwayObserved ≡ true

    nmpFirstPathwayObserved : Bool
    nmpFirstPathwayObservedIsTrue : nmpFirstPathwayObserved ≡ true

    relativePathwayFluxSourcePaid : Bool
    relativePathwayFluxSourcePaidIsTrue : relativePathwayFluxSourcePaid ≡ true

    pathwayFluxFavoursLidFirst : Bool
    pathwayFluxFavoursLidFirstIsTrue : pathwayFluxFavoursLidFirst ≡ true

    offDiagonalReachabilityImpliesIndependence : Bool
    offDiagonalReachabilityImpliesIndependenceIsFalse :
      offDiagonalReachabilityImpliesIndependence ≡ false

    fluxRatioIsUniversalRateConstant : Bool
    fluxRatioIsUniversalRateConstantIsFalse :
      fluxRatioIsUniversalRateConstant ≡ false

    computationalPathwayOrderIsExperimentalMechanism : Bool
    computationalPathwayOrderIsExperimentalMechanismIsFalse :
      computationalPathwayOrderIsExperimentalMechanism ≡ false

    pathwayRatioTransfersAcrossLigandConditions : Bool
    pathwayRatioTransfersAcrossLigandConditionsIsFalse :
      pathwayRatioTransfersAcrossLigandConditions ≡ false

    twoAxisCouplingFullyIdentified : Bool
    twoAxisCouplingFullyIdentifiedIsFalse :
      twoAxisCouplingFullyIdentified ≡ false

    equilibriumJointDistributionPaid : Bool
    equilibriumJointDistributionPaidIsFalse :
      equilibriumJointDistributionPaid ≡ false

canonicalAdKCouplingBoundary : AdKCouplingBoundary
canonicalAdKCouplingBoundary =
  adk-coupling-boundary
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
