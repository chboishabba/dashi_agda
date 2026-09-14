module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseWeightedNDimStateGraphExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCouplingResidualExact as Coupling
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSameSequenceSimulatedMixedStatesExact as Mixed

------------------------------------------------------------------------
-- WEIGHTED NDIM STATE GRAPH FOR LIGAND-FREE E. COLI ADENYLATE KINASE
--
-- Li, Liu & Ji 2015 (DOI 10.1016/j.bpj.2015.06.059) map a two-coordinate
-- free-energy landscape using LID--CORE and NMP--CORE angles.  Their equation
-- for pathway flux compares
--
--   alpha -> beta -> gamma -> delta -> xi
--   alpha -> beta -> epsilon -> xi
--
-- at approximately 5.7 : 1 in favour of the first route.  Figure 5 elsewhere
-- labels the crystal closed state zeta.  We retain the equation-level xi target
-- and the figure-level zeta label as distinct source coordinates instead of
-- silently repairing the source notation.
--
-- The graph is weighted at the *path* level by the source-paid relative flux.
-- The paper also reports per-edge Kramers rate constants in Figure 5, but those
-- numerical labels are not transcribed here.  This is therefore a weighted
-- path graph plus a free-energy-surface receipt, not a fully numerically weighted
-- Markov network.
------------------------------------------------------------------------

data AdKLandscapeState : Set where
  alpha : AdKLandscapeState
  beta : AdKLandscapeState
  gamma : AdKLandscapeState
  delta : AdKLandscapeState
  epsilon : AdKLandscapeState
  xiEquationTarget : AdKLandscapeState

data ClosedStateSourceLabel : Set where
  figureZeta : ClosedStateSourceLabel
  equationXi : ClosedStateSourceLabel

figureAndEquationLabelsDiffer : figureZeta ≡ equationXi → ⊥
figureAndEquationLabelsDiffer ()

record DirectedLandscapeEdge : Set where
  constructor directed-landscape-edge
  field
    source : AdKLandscapeState
    target : AdKLandscapeState
open DirectedLandscapeEdge public

alphaBeta : DirectedLandscapeEdge
alphaBeta = directed-landscape-edge alpha beta

betaGamma : DirectedLandscapeEdge
betaGamma = directed-landscape-edge beta gamma

gammaDelta : DirectedLandscapeEdge
gammaDelta = directed-landscape-edge gamma delta

deltaXi : DirectedLandscapeEdge
deltaXi = directed-landscape-edge delta xiEquationTarget

betaEpsilon : DirectedLandscapeEdge
betaEpsilon = directed-landscape-edge beta epsilon

epsilonXi : DirectedLandscapeEdge
epsilonXi = directed-landscape-edge epsilon xiEquationTarget

record LandscapeRoute : Set where
  constructor landscape-route
  field
    label : String
    first : DirectedLandscapeEdge
    second : DirectedLandscapeEdge
    third : DirectedLandscapeEdge
    fourth : DirectedLandscapeEdge
    edgeCount : Nat
open LandscapeRoute public

-- The alternative route has only three source-paid edges.  Its fourth slot is
-- deliberately the terminal epsilon->xi edge repeated as padding; edgeCount
-- remains the authoritative arity.  This keeps the carrier tiny and total while
-- avoiding a second list ontology.
primaryLidFirstRoute : LandscapeRoute
primaryLidFirstRoute =
  landscape-route
    "alpha-beta-gamma-delta-xi; LID-first dominant route"
    alphaBeta betaGamma gammaDelta deltaXi 4

alternativeNmpFirstRoute : LandscapeRoute
alternativeNmpFirstRoute =
  landscape-route
    "alpha-beta-epsilon-xi; NMP-first alternative route"
    alphaBeta betaEpsilon epsilonXi epsilonXi 3

------------------------------------------------------------------------
-- Source-paid path weight.
------------------------------------------------------------------------

record RelativePathFluxWeight : Set where
  constructor relative-path-flux-weight
  field
    primaryPathFluxNumerator : Nat
    primaryPathFluxDenominator : Nat
    primaryRoute : LandscapeRoute
    alternativeRoute : LandscapeRoute
    interpretation : String
open RelativePathFluxWeight public

canonicalPathWeight : RelativePathFluxWeight
canonicalPathWeight =
  relative-path-flux-weight
    57
    10
    primaryLidFirstRoute
    alternativeNmpFirstRoute
    "approximate source ratio 5.7:1 for pathway probability/flux; not a universal rate constant"

------------------------------------------------------------------------
-- Two-dimensional free-energy surface receipt.
------------------------------------------------------------------------

record TwoAngleFreeEnergyReceipt : Set where
  constructor two-angle-free-energy-receipt
  field
    lidCoreOpenDegrees : Nat
    lidCoreClosedDegrees : Nat
    nmpCoreOpenDegrees : Nat
    nmpCoreClosedDegrees : Nat
    gammaReferenceFreeEnergyTenthsKcal : Nat
    gammaIsReferenceMinimum : Bool
    landscapeUnit : String
    perEdgeRateUnit : String
open TwoAngleFreeEnergyReceipt public

canonicalFreeEnergyReceipt : TwoAngleFreeEnergyReceipt
canonicalFreeEnergyReceipt =
  two-angle-free-energy-receipt
    95
    68
    61
    28
    0
    true
    "relative free energy in kcal/mol; gamma set to the zero reference"
    "Figure 5 edge-rate labels are in 10^-2 ns^-1; numerical values not transcribed in this owner"

------------------------------------------------------------------------
-- Reuse the existing coupling / same-sequence receipts.
------------------------------------------------------------------------

couplingResidualDonor : Coupling.AdKCouplingBoundary
couplingResidualDonor = Coupling.canonicalAdKCouplingBoundary

sameSequenceMixedStateDonor : Mixed.SameSequenceSimulatedMixedStateBoundary
sameSequenceMixedStateDonor = Mixed.canonicalSameSequenceSimulatedMixedStateBoundary

------------------------------------------------------------------------
-- Snowball attribution.
------------------------------------------------------------------------

record WeightedGraphSourceCoordinate : Set where
  constructor weighted-graph-source-coordinate
  field
    label : String
    doi : String
    pmid : String
    pmcid : String
    qid : String
    pdb : String
    uniprot : String
    dewey : String
    directLink : String
    oeis : String
    sourceRole : String

liLiuJi2015WeightedGraphSource : WeightedGraphSourceCoordinate
liLiuJi2015WeightedGraphSource =
  weighted-graph-source-coordinate
    "Li, Liu and Ji 2015 adenylate-kinase dynamics/free-energy landscape"
    "10.1016/j.bpj.2015.06.059"
    "26244746"
    "PMC4572606"
    "source-article QID unresolved in inspected sources; adenylate kinase Q356240"
    "4AKE open; 1AKE closed endpoints"
    "P69441"
    "exact article-level Dewey unresolved"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC4572606/"
    "not an integer-sequence object; no same-object OEIS coordinate"
    "pays two-angle ligand-free free-energy landscape, intermediate-state graph, Kramers-rate methodology, and approximate 5.7:1 path-flux comparison"

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record AdKWeightedGraphBoundary : Set where
  constructor adk-weighted-graph-boundary
  field
    sixEquationStatesRetained : Bool
    sixEquationStatesRetainedIsTrue : sixEquationStatesRetained ≡ true

    primaryAndAlternativeRoutesRetained : Bool
    primaryAndAlternativeRoutesRetainedIsTrue :
      primaryAndAlternativeRoutesRetained ≡ true

    pathFluxWeightSourcePaid : Bool
    pathFluxWeightSourcePaidIsTrue : pathFluxWeightSourcePaid ≡ true

    twoAngleFreeEnergySurfaceSourcePaid : Bool
    twoAngleFreeEnergySurfaceSourcePaidIsTrue :
      twoAngleFreeEnergySurfaceSourcePaid ≡ true

    gammaReferenceMinimumRetained : Bool
    gammaReferenceMinimumRetainedIsTrue : gammaReferenceMinimumRetained ≡ true

    numericPerEdgeRatesFullyTranscribed : Bool
    numericPerEdgeRatesFullyTranscribedIsFalse :
      numericPerEdgeRatesFullyTranscribed ≡ false

    figureZetaAndEquationXiSilentlyIdentified : Bool
    figureZetaAndEquationXiSilentlyIdentifiedIsFalse :
      figureZetaAndEquationXiSilentlyIdentified ≡ false

    weightedGraphProvesEquilibriumDistribution : Bool
    weightedGraphProvesEquilibriumDistributionIsFalse :
      weightedGraphProvesEquilibriumDistribution ≡ false

    weightedGraphProvesExperimentalMechanism : Bool
    weightedGraphProvesExperimentalMechanismIsFalse :
      weightedGraphProvesExperimentalMechanism ≡ false

    weightedGraphIsFullyCalibratedMarkovModel : Bool
    weightedGraphIsFullyCalibratedMarkovModelIsFalse :
      weightedGraphIsFullyCalibratedMarkovModel ≡ false

    freeEnergyEqualsFlux : Bool
    freeEnergyEqualsFluxIsFalse : freeEnergyEqualsFlux ≡ false

canonicalAdKWeightedGraphBoundary : AdKWeightedGraphBoundary
canonicalAdKWeightedGraphBoundary =
  adk-weighted-graph-boundary
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
