module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseRateObserverAdequacyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseWeightedNDimStateGraphExact as Graph
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLigandConditionedLandscapeExact as Context

------------------------------------------------------------------------
-- ADENYLATE-KINASE RATE-OBSERVER ADEQUACY
--
-- The weighted-state-graph owner currently pays route topology, path-level
-- flux asymmetry and the two-angle free-energy surfaces.  Li, Liu & Ji 2015
-- additionally state that Figure 5/6 arrow labels are Kramers transition-rate
-- constants in 10^-2 ns^-1.  The text extraction pays the rate *coordinate* and
-- its calibration method, but not a trustworthy transcription of every visual
-- edge label.
--
-- This owner therefore makes the information boundary exact:
--
--   unweighted topology is adequate for reachability,
--   unweighted topology is NOT adequate for an edge-rate query,
--   topology + retained rate coordinate repairs that loss.
--
-- The collision is finite and generic; it proves the information theorem rather
-- than pretending an unresolved visual number has been acquired.
------------------------------------------------------------------------

data RateWorld : Set where
  apoRateWorld : RateWorld
  boundRateWorld : RateWorld

data TopologyObservation : Set where
  sameRouteTopology : TopologyObservation

data RateQuery : Set where
  reachabilityQuery : RateQuery
  transitionRateQuery : RateQuery

data RateAnswer : Set where
  reachableAnswer : RateAnswer
  apoRateAnswer : RateAnswer
  boundRateAnswer : RateAnswer

topologyProjection : RateWorld → TopologyObservation
topologyProjection world = sameRouteTopology

rateAnswer : RateQuery → RateWorld → RateAnswer
rateAnswer reachabilityQuery world = reachableAnswer
rateAnswer transitionRateQuery apoRateWorld = apoRateAnswer
rateAnswer transitionRateQuery boundRateWorld = boundRateAnswer

rateSemantics : Query.QuerySemantics RateWorld RateQuery RateAnswer
rateSemantics = Query.querySemantics rateAnswer

topologyReachabilityAdequate :
  Query.AdequateFor topologyProjection rateSemantics reachabilityQuery
topologyReachabilityAdequate =
  Query.factorsForQuery
    (λ observation → reachableAnswer)
    (λ { apoRateWorld → refl ; boundRateWorld → refl })

topologyTransitionRateDefect :
  Query.QueryAdequacyDefect topologyProjection rateSemantics transitionRateQuery
topologyTransitionRateDefect =
  Query.queryAdequacyDefect
    apoRateWorld
    boundRateWorld
    refl
    (λ ())

topologyTransitionRateNotAdequate :
  Query.AdequateFor topologyProjection rateSemantics transitionRateQuery → ⊥
topologyTransitionRateNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation topologyTransitionRateDefect

------------------------------------------------------------------------
-- Constructive observer repair.
------------------------------------------------------------------------

data RateCoordinate : Set where
  apoRateCoordinate : RateCoordinate
  boundRateCoordinate : RateCoordinate

record EnrichedRateObservation : Set where
  constructor enriched-rate-observation
  field
    topology : TopologyObservation
    rateCoordinate : RateCoordinate
open EnrichedRateObservation public

enrichedProjection : RateWorld → EnrichedRateObservation
enrichedProjection apoRateWorld =
  enriched-rate-observation sameRouteTopology apoRateCoordinate
enrichedProjection boundRateWorld =
  enriched-rate-observation sameRouteTopology boundRateCoordinate

coarseRateAnswer : EnrichedRateObservation → RateAnswer
coarseRateAnswer (enriched-rate-observation sameRouteTopology apoRateCoordinate) =
  apoRateAnswer
coarseRateAnswer (enriched-rate-observation sameRouteTopology boundRateCoordinate) =
  boundRateAnswer

enrichedTransitionRateAdequate :
  Query.AdequateFor enrichedProjection rateSemantics transitionRateQuery
enrichedTransitionRateAdequate =
  Query.factorsForQuery
    coarseRateAnswer
    (λ { apoRateWorld → refl ; boundRateWorld → refl })

------------------------------------------------------------------------
-- Source-paid Kramers calibration coordinates.
--
-- Figure 5 (apo) states D ~= 4.47 x 10^-3 rad^2/ns.
-- Figure 6 (ligand-bound) states D ~= 5.13 x 10^-4 rad^2/ns.
-- Exact rationals below preserve those printed decimals:
--   447 / 100000   = 0.00447
--   513 / 1000000  = 0.000513
------------------------------------------------------------------------

record KramersCalibration : Set where
  constructor kramers-calibration
  field
    contextLabel : String
    diffusionNumerator : Nat
    diffusionDenominator : Nat
    diffusionUnit : String
    edgeRateUnit : String
    acquisitionStatus : String
open KramersCalibration public

apoKramersCalibration : KramersCalibration
apoKramersCalibration =
  kramers-calibration
    "ligand-free AdK Figure 5"
    447
    100000
    "rad^2/ns"
    "10^-2 ns^-1"
    "diffusion calibration and edge-rate unit source-paid; individual visual edge-rate labels not yet transcribed"

boundKramersCalibration : KramersCalibration
boundKramersCalibration =
  kramers-calibration
    "ligand-bound AdK Figure 6"
    513
    1000000
    "rad^2/ns"
    "10^-2 ns^-1"
    "diffusion calibration and edge-rate unit source-paid; individual visual edge-rate labels not yet transcribed"

------------------------------------------------------------------------
-- Existing graph / context donors.
------------------------------------------------------------------------

weightedGraphDonor : Graph.AdKWeightedGraphBoundary
weightedGraphDonor = Graph.canonicalAdKWeightedGraphBoundary

ligandConditionedDonor : Context.AdKLigandConditionedBoundary
ligandConditionedDonor = Context.canonicalAdKLigandConditionedBoundary

------------------------------------------------------------------------
-- Snowball attribution.
------------------------------------------------------------------------

record RateObserverSourceCoordinate : Set where
  constructor rate-observer-source-coordinate
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

liLiuJi2015KramersRateSource : RateObserverSourceCoordinate
liLiuJi2015KramersRateSource =
  rate-observer-source-coordinate
    "Li, Liu and Ji 2015 Kramers transition-rate calibration for AdK landscapes"
    "10.1016/j.bpj.2015.06.059"
    "26244746"
    "PMC4572606"
    "source-article QID unresolved in inspected sources; adenylate kinase Q356240"
    "4AKE / 1AKE reference endpoints"
    "P69441"
    "exact article-level Dewey unresolved"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC4572606/"
    "not an integer-sequence object; no same-object OEIS coordinate"
    "pays Figure 5/6 Kramers-rate semantics, 10^-2 ns^-1 rate units, apo D~=4.47e-3 rad^2/ns and bound D~=5.13e-4 rad^2/ns; does not by text extraction pay every visual arrow label"

------------------------------------------------------------------------
-- Promotion / acquisition boundary.
------------------------------------------------------------------------

record AdKRateObserverBoundary : Set where
  constructor adk-rate-observer-boundary
  field
    topologyAdequateForReachability : Bool
    topologyAdequateForReachabilityIsTrue :
      topologyAdequateForReachability ≡ true

    topologyAdequateForTransitionRate : Bool
    topologyAdequateForTransitionRateIsFalse :
      topologyAdequateForTransitionRate ≡ false

    enrichedObserverAdequateForTransitionRate : Bool
    enrichedObserverAdequateForTransitionRateIsTrue :
      enrichedObserverAdequateForTransitionRate ≡ true

    rateLabelsPresentInSourceFigures : Bool
    rateLabelsPresentInSourceFiguresIsTrue :
      rateLabelsPresentInSourceFigures ≡ true

    rateUnitSourcePaid : Bool
    rateUnitSourcePaidIsTrue : rateUnitSourcePaid ≡ true

    apoDiffusionCalibrationSourcePaid : Bool
    apoDiffusionCalibrationSourcePaidIsTrue :
      apoDiffusionCalibrationSourcePaid ≡ true

    boundDiffusionCalibrationSourcePaid : Bool
    boundDiffusionCalibrationSourcePaidIsTrue :
      boundDiffusionCalibrationSourcePaid ≡ true

    numericPerEdgeRateTableAcquired : Bool
    numericPerEdgeRateTableAcquiredIsFalse :
      numericPerEdgeRateTableAcquired ≡ false

    topologyDeterminesRates : Bool
    topologyDeterminesRatesIsFalse : topologyDeterminesRates ≡ false

    freeEnergySurfaceDeterminesRatesWithoutCalibration : Bool
    freeEnergySurfaceDeterminesRatesWithoutCalibrationIsFalse :
      freeEnergySurfaceDeterminesRatesWithoutCalibration ≡ false

    kramersCalibrationEqualsExperimentalRateMeasurement : Bool
    kramersCalibrationEqualsExperimentalRateMeasurementIsFalse :
      kramersCalibrationEqualsExperimentalRateMeasurement ≡ false

    ligandFreeCalibrationTransfersToBoundContext : Bool
    ligandFreeCalibrationTransfersToBoundContextIsFalse :
      ligandFreeCalibrationTransfersToBoundContext ≡ false

canonicalAdKRateObserverBoundary : AdKRateObserverBoundary
canonicalAdKRateObserverBoundary =
  adk-rate-observer-boundary
    true refl
    false refl
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
