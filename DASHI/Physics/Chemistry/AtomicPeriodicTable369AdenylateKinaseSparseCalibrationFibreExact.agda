module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseWeightedNDimStateGraphExact as Graph
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePartialStateCoordinateAlignmentExact as Align

------------------------------------------------------------------------
-- SPARSE, PROVENANCE-PRESERVING ADK CALIBRATION FIBRE
--
-- This owner deliberately reuses repository-wide attribution and external-
-- identity machinery.  It adds only the domain calibration carrier required by
-- the AdK consumer.  Every numerical coordinate is either explicitly paid or
-- explicitly missing; missingness is not permission to interpolate, infer from
-- a neighbouring state, or promote a qualitative region into a numeric point.
------------------------------------------------------------------------

liLiuJi2015Source : Attribution.AttributedSource
liLiuJi2015Source =
  Attribution.mkDOISource
    "Li, Liu and Ji"
    "Mapping the Dynamics Landscape of Conformational Transitions in Enzyme: The Adenylate Kinase Case"
    "Biophysical Journal"
    "2015"
    "10.1016/j.bpj.2015.06.059"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC4572606/"
    Attribution.academicArticleSource
    "pays source-bounded AdK collective-variable, free-energy-landscape, named-state, Kramers-methodology and pathway-flux premises only where explicitly acquired; it does not pay DASHI synthesis or experimental kinetics"
    Attribution.publicAttribution

liLiuJiSnowballReceipt : Snowball.SourceRoleSnowballReceipt liLiuJi2015Source
liLiuJiSnowballReceipt = Snowball.canonicalSourceRoleSnowballReceipt liLiuJi2015Source

liLiuJiArticleQid : Identity.ExternalIdentityDemand
liLiuJiArticleQid =
  Identity.mkOptionalIdentityDemand
    "AdK sparse calibration attribution"
    "Li Liu Ji 2015 article Wikidata identity"
    "Mapping the Dynamics Landscape of Conformational Transitions in Enzyme: The Adenylate Kinase Case"
    Identity.wikidataQid
    (Identity.unresolved "article-level QID unresolved in inspected repository sources")

adkQid : Identity.ExternalIdentityDemand
adkQid =
  Identity.mkOptionalIdentityDemand
    "AdK sparse calibration attribution"
    "adenylate kinase entity identity"
    "adenylate kinase"
    Identity.wikidataQid
    (Identity.verified "Wikidata" "Q356240")

uniprotP69441 : Identity.ExternalIdentityDemand
uniprotP69441 =
  Identity.mkOptionalIdentityDemand
    "AdK sparse calibration attribution"
    "E. coli adenylate kinase UniProt identity"
    "KAD_ECOLI"
    Identity.officialIdentifier
    (Identity.verified "UniProt" "P69441")

pdb4AKE : Identity.ExternalIdentityDemand
pdb4AKE =
  Identity.mkOptionalIdentityDemand
    "AdK sparse calibration attribution"
    "open adenylate kinase PDB identity"
    "4AKE"
    Identity.officialIdentifier
    (Identity.verified "Protein Data Bank" "4AKE")

pdb1AKE : Identity.ExternalIdentityDemand
pdb1AKE =
  Identity.mkOptionalIdentityDemand
    "AdK sparse calibration attribution"
    "closed adenylate kinase PDB identity"
    "1AKE"
    Identity.officialIdentifier
    (Identity.verified "Protein Data Bank" "1AKE")

------------------------------------------------------------------------
-- Sparse value carrier.
------------------------------------------------------------------------

data NumericPayment : Set where
  unpaidNumeric : String → NumericPayment
  paidNumeric : Nat → String → NumericPayment

data RateKind : Set where
  kramersDerivedRate : RateKind
  simulationObservedRate : RateKind
  experimentallyMeasuredRate : RateKind
  inferredRate : RateKind
  rateKindUnresolved : RateKind

data CalibrationMethod : Set where
  sourceFigureReadout : CalibrationMethod
  sourceTextReadout : CalibrationMethod
  sourceEquationReadout : CalibrationMethod
  composedSourceFacts : CalibrationMethod
  noMethodBecauseUnpaid : CalibrationMethod

record SparseNumericCoordinate : Set where
  constructor sparse-numeric-coordinate
  field
    value : NumericPayment
    unit : String
    sourceLocator : String
    uncertainty : String
    method : CalibrationMethod
open SparseNumericCoordinate public

missingCoordinate : String → String → SparseNumericCoordinate
missingCoordinate unit locator =
  sparse-numeric-coordinate
    (unpaidNumeric "not acquired at sufficient same-object/source confidence")
    unit locator "unresolved" noMethodBecauseUnpaid

paidCoordinate : Nat → String → String → String → CalibrationMethod → SparseNumericCoordinate
paidCoordinate n unit locator uncertainty method =
  sparse-numeric-coordinate (paidNumeric n locator) unit locator uncertainty method

------------------------------------------------------------------------
-- State-level calibration fibre.
------------------------------------------------------------------------

data CalibrationStateLabel : Set where
  alphaState betaState gammaState deltaState epsilonState zetaState etaState lambdaState : CalibrationStateLabel

record StateCalibrationObservation : Set where
  constructor state-calibration-observation
  field
    stateLabel : CalibrationStateLabel
    thetaOneDegrees : SparseNumericCoordinate
    thetaTwoDegrees : SparseNumericCoordinate
    dLnCoordinate : SparseNumericCoordinate
    relativeFreeEnergyTenthsKcalMol : SparseNumericCoordinate
    stateSource : Attribution.AttributedSource
    sourceRole : String
open StateCalibrationObservation public

stateCalibration : CalibrationStateLabel → StateCalibrationObservation
stateCalibration alphaState =
  state-calibration-observation alphaState
    (paidCoordinate 95 "degrees" "Figure-5/open-endpoint composition" "source-level endpoint coordinate" composedSourceFacts)
    (paidCoordinate 61 "degrees" "Figure-5/open-endpoint composition" "source-level endpoint coordinate" composedSourceFacts)
    (missingCoordinate "source dLN unit" "no per-alpha dLN value acquired")
    (missingCoordinate "0.1 kcal/mol" "no per-alpha relative-free-energy value acquired")
    liLiuJi2015Source
    "alpha/open endpoint; numeric theta coordinates are DASHI composition of separately source-paid endpoint identity and angle values"
stateCalibration betaState =
  state-calibration-observation betaState
    (missingCoordinate "degrees" "beta retained only as semi-open/semi-closed region")
    (missingCoordinate "degrees" "beta retained only as semi-open/semi-closed region")
    (missingCoordinate "source dLN unit" "no per-beta dLN value acquired")
    (missingCoordinate "0.1 kcal/mol" "no per-beta relative-free-energy value acquired")
    liLiuJi2015Source
    "beta qualitative intermediate region only"
stateCalibration gammaState =
  state-calibration-observation gammaState
    (missingCoordinate "degrees" "gamma retained only as semi-open/semi-closed region")
    (missingCoordinate "degrees" "gamma retained only as semi-open/semi-closed region")
    (missingCoordinate "source dLN unit" "no per-gamma dLN value acquired")
    (paidCoordinate 0 "0.1 kcal/mol" "existing canonicalFreeEnergyReceipt gamma zero reference" "reference convention, not absolute thermodynamic free energy" sourceTextReadout)
    liLiuJi2015Source
    "gamma retained as the source/repository zero-reference state for relative free energy"
stateCalibration deltaState =
  state-calibration-observation deltaState
    (missingCoordinate "degrees" "delta retained only as semi-open/semi-closed region")
    (missingCoordinate "degrees" "delta retained only as semi-open/semi-closed region")
    (missingCoordinate "source dLN unit" "no per-delta dLN value acquired")
    (missingCoordinate "0.1 kcal/mol" "no per-delta relative-free-energy value acquired")
    liLiuJi2015Source
    "delta qualitative intermediate region only"
stateCalibration epsilonState =
  state-calibration-observation epsilonState
    (missingCoordinate "degrees" "epsilon retained only as semi-open/semi-closed region")
    (missingCoordinate "degrees" "epsilon retained only as semi-open/semi-closed region")
    (missingCoordinate "source dLN unit" "no per-epsilon dLN value acquired")
    (missingCoordinate "0.1 kcal/mol" "no per-epsilon relative-free-energy value acquired")
    liLiuJi2015Source
    "epsilon qualitative intermediate region only"
stateCalibration zetaState =
  state-calibration-observation zetaState
    (paidCoordinate 68 "degrees" "Figure-5/closed-endpoint composition" "source-level endpoint coordinate" composedSourceFacts)
    (paidCoordinate 28 "degrees" "Figure-5/closed-endpoint composition" "source-level endpoint coordinate" composedSourceFacts)
    (missingCoordinate "source dLN unit" "no per-zeta dLN value acquired")
    (missingCoordinate "0.1 kcal/mol" "no per-zeta relative-free-energy value acquired")
    liLiuJi2015Source
    "zeta/closed endpoint; numeric theta coordinates are DASHI composition of separately source-paid endpoint identity and angle values"
stateCalibration etaState =
  state-calibration-observation etaState
    (missingCoordinate "degrees" "eta retained only as near-closed region")
    (missingCoordinate "degrees" "eta retained only as near-closed region")
    (missingCoordinate "source dLN unit" "no per-eta dLN value acquired")
    (missingCoordinate "0.1 kcal/mol" "no per-eta relative-free-energy value acquired")
    liLiuJi2015Source
    "eta qualitative near-closed region only"
stateCalibration lambdaState =
  state-calibration-observation lambdaState
    (missingCoordinate "degrees" "lambda retained only as near-closed region")
    (missingCoordinate "degrees" "lambda retained only as near-closed region")
    (missingCoordinate "source dLN unit" "no per-lambda dLN value acquired")
    (missingCoordinate "0.1 kcal/mol" "no per-lambda relative-free-energy value acquired")
    liLiuJi2015Source
    "lambda qualitative near-closed region only"

------------------------------------------------------------------------
-- Edge-rate calibration is deliberately sparse.  The source/repository pays
-- that Figure 5 contains Kramers-derived edge rates and their scale, but exact
-- per-edge numeric labels remain unacquired.  The rate kind is nevertheless
-- retained so later acquisition cannot be mistaken for experimental kinetics.
------------------------------------------------------------------------

record EdgeRateCalibration : Set where
  constructor edge-rate-calibration
  field
    edge : Graph.DirectedLandscapeEdge
    rate : SparseNumericCoordinate
    rateKind : RateKind
    source : Attribution.AttributedSource
    interpretation : String
open EdgeRateCalibration public

unpaidKramersRate : Graph.DirectedLandscapeEdge → String → EdgeRateCalibration
unpaidKramersRate edge locator =
  edge-rate-calibration
    edge
    (missingCoordinate "10^-2 ns^-1" locator)
    kramersDerivedRate
    liLiuJi2015Source
    "Figure-5 Kramers-derived rate coordinate exists, but its exact visual numeric label is not transcribed; this is not an experimental rate"

alphaBetaRate : EdgeRateCalibration
alphaBetaRate = unpaidKramersRate Graph.alphaBeta "Figure 5c alpha->beta arrow"
betaGammaRate : EdgeRateCalibration
betaGammaRate = unpaidKramersRate Graph.betaGamma "Figure 5c beta->gamma arrow"
gammaDeltaRate : EdgeRateCalibration
gammaDeltaRate = unpaidKramersRate Graph.gammaDelta "Figure 5c gamma->delta arrow"
deltaXiRate : EdgeRateCalibration
deltaXiRate = unpaidKramersRate Graph.deltaXi "Figure 5c/prose terminal route seam; xi/zeta notation retained separately"
betaEpsilonRate : EdgeRateCalibration
betaEpsilonRate = unpaidKramersRate Graph.betaEpsilon "Figure 5c beta->epsilon arrow"
epsilonXiRate : EdgeRateCalibration
epsilonXiRate = unpaidKramersRate Graph.epsilonXi "Figure 5c/prose terminal route seam; xi/zeta notation retained separately"

------------------------------------------------------------------------
-- Path-flux observation remains a different measurement role from edge rate.
------------------------------------------------------------------------

record PathFluxObservation : Set where
  constructor path-flux-observation
  field
    numerator : Nat
    denominator : Nat
    sourceLocator : String
    source : Attribution.AttributedSource
    interpretation : String
open PathFluxObservation public

primaryToAlternativeFlux : PathFluxObservation
primaryToAlternativeFlux =
  path-flux-observation
    57 10 "Eq. (1) / ligand-free pathway-flux comparison"
    liLiuJi2015Source
    "approximate 5.7:1 primary-to-alternative path flux; not a per-edge rate and not an equilibrium population ratio"

------------------------------------------------------------------------
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

data MissingCoordinateCanBeNeighbourInferred : Set where
data KramersRateIsExperimentalRate : Set where
data RelativeFreeEnergyIsAbsoluteThermodynamicFreeEnergy : Set where
data QidCreatesScientificAuthority : Set where

missingCoordinateCannotBeNeighbourInferred : MissingCoordinateCanBeNeighbourInferred → ⊥
missingCoordinateCannotBeNeighbourInferred ()

kramersDerivedDoesNotBecomeExperimental : KramersRateIsExperimentalRate → ⊥
kramersDerivedDoesNotBecomeExperimental ()

relativePlotEnergyIsNotAbsoluteByCitation : RelativeFreeEnergyIsAbsoluteThermodynamicFreeEnergy → ⊥
relativePlotEnergyIsNotAbsoluteByCitation ()

qidDoesNotCreateScientificAuthority : QidCreatesScientificAuthority → ⊥
qidDoesNotCreateScientificAuthority ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKSparseCalibrationBoundary : Set where
  constructor adk-sparse-calibration-boundary
  field
    alphaThetaOnePaid : Bool
    alphaThetaTwoPaid : Bool
    zetaThetaOnePaid : Bool
    zetaThetaTwoPaid : Bool
    gammaReferenceFreeEnergyPaid : Bool
    namedStateDLnTablePaid : Bool
    perEdgeKramersNumericTablePaid : Bool
    kramersRateEqualsExperimentalRate : Bool
    pathFluxEqualsEdgeRate : Bool
    relativeFreeEnergyEqualsAbsoluteFreeEnergy : Bool
    missingCoordinateMayBeInferredFromNeighbour : Bool
    reusesAttributedSourceCore : Bool
    reusesExternalIdentityAvailability : Bool
    unresolvedArticleQidBlocksCalibration : Bool
    citationCreatesScientificAuthority : Bool

canonicalAdKSparseCalibrationBoundary : AdKSparseCalibrationBoundary
canonicalAdKSparseCalibrationBoundary =
  adk-sparse-calibration-boundary
    true true true true true
    false false false false false false
    true true false false
