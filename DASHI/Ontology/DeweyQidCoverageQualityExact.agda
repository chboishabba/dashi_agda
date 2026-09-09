module DASHI.Ontology.DeweyQidCoverageQualityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- DEWEY / DOI / QID COVERAGE QUALITY
--
-- This owner prevents four distinct questions from collapsing:
--
--   1. classification coverage: does every module have a parent Dewey ID?
--   2. subject volume: how much formal material lies in that parent cluster?
--   3. source-addressability: how many modules expose DOI/source identities?
--   4. entity-addressability: how many modules expose Wikidata QIDs?
--
-- A large cluster is not automatically source-rich.  A QID is external
-- identity metadata, not theorem/source authority.  A DOI is bibliographic
-- identity, not proof or correctness.  First-link graph reachability is a
-- separate revision/language/parser-indexed navigation observation.
------------------------------------------------------------------------

data CoverageDimension : Set where
  deweyClassificationCoverage : CoverageDimension
  subjectVolumeCoverage : CoverageDimension
  doiModuleCoverage : CoverageDimension
  qidModuleCoverage : CoverageDimension
  doiQidJointCoverage : CoverageDimension
  firstLinkNavigabilityCoverage : CoverageDimension

data CoverageBand : Set where
  unmeasured : CoverageBand
  sparse : CoverageBand
  developing : CoverageBand
  strong : CoverageBand

record ParentClusterCoverageObservation : Set where
  constructor parent-cluster-coverage-observation
  field
    deweyId : String
    clusterLabel : String
    moduleCount : Nat
    modulesWithDoi : Nat
    distinctDois : Nat
    modulesWithQid : Nat
    distinctQids : Nat
    modulesWithDoiAndQid : Nat
    doiBand : CoverageBand
    qidBand : CoverageBand
    jointBand : CoverageBand
open ParentClusterCoverageObservation public

record RepositoryCoverageHeadline : Set where
  constructor repository-coverage-headline
  field
    agdaModuleCount : Nat
    deweyClassifiedModuleCount : Nat
    modulesWithObservedDoi : Nat
    distinctObservedDois : Nat
    qidCoverageMeasuredRepositoryWide : Bool
open RepositoryCoverageHeadline public

-- Headline values from the repository-wide Dewey projection.  QID coverage is
-- deliberately not fabricated here: the deterministic QID indexer must run on
-- the same checkout/catalog before repository-wide QID density can be stated.
canonicalRepositoryCoverageHeadline : RepositoryCoverageHeadline
canonicalRepositoryCoverageHeadline =
  repository-coverage-headline
    15796
    15796
    3696
    1179
    false

------------------------------------------------------------------------
-- Current high-volume parent clusters from the Dewey projection.
-- These are VOLUME observations only.  Their DOI/QID bands remain unmeasured
-- here until generated cluster joins provide the relevant numerators.
------------------------------------------------------------------------

navierStokesVolume yangMillsVolume pnfVolume biologyVolume lawVolume interopVolume :
  ParentClusterCoverageObservation

navierStokesVolume =
  parent-cluster-coverage-observation
    "532.051" "Navier-Stokes closure" 5218 0 0 0 0 0 unmeasured unmeasured unmeasured

yangMillsVolume =
  parent-cluster-coverage-observation
    "530.144" "Yang-Mills" 2589 0 0 0 0 0 unmeasured unmeasured unmeasured

pnfVolume =
  parent-cluster-coverage-observation
    "153.420" "PNF cognition" 622 0 0 0 0 0 unmeasured unmeasured unmeasured

biologyVolume =
  parent-cluster-coverage-observation
    "570.000" "General biology" 531 0 0 0 0 0 unmeasured unmeasured unmeasured

lawVolume =
  parent-cluster-coverage-observation
    "340.000" "Law" 217 0 0 0 0 0 unmeasured unmeasured unmeasured

interopVolume =
  parent-cluster-coverage-observation
    "004.650" "Interoperability" 201 0 0 0 0 0 unmeasured unmeasured unmeasured

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FullDeweyCoverageImpliesFullDoiCoverage : Set where
data FullDeweyCoverageImpliesFullQidCoverage : Set where
data LargeClusterImpliesStrongSourceCoverage : Set where
data DoiPresenceImpliesTheoremAuthority : Set where
data QidPresenceImpliesSourceTruth : Set where
data FirstLinkReachabilityImpliesConceptualDependence : Set where

fullDeweyDoesNotImplyFullDoi : FullDeweyCoverageImpliesFullDoiCoverage → ⊥
fullDeweyDoesNotImplyFullDoi ()

fullDeweyDoesNotImplyFullQid : FullDeweyCoverageImpliesFullQidCoverage → ⊥
fullDeweyDoesNotImplyFullQid ()

volumeDoesNotImplyMetadataStrength : LargeClusterImpliesStrongSourceCoverage → ⊥
volumeDoesNotImplyMetadataStrength ()

doiDoesNotCreateTheoremAuthority : DoiPresenceImpliesTheoremAuthority → ⊥
doiDoesNotCreateTheoremAuthority ()

qidDoesNotCreateSourceTruth : QidPresenceImpliesSourceTruth → ⊥
qidDoesNotCreateSourceTruth ()

firstLinkDoesNotCreateConceptualDependence :
  FirstLinkReachabilityImpliesConceptualDependence → ⊥
firstLinkDoesNotCreateConceptualDependence ()

record CoverageQualityBoundary : Set where
  constructor coverage-quality-boundary
  field
    classificationSeparateFromVolume : Bool
    volumeSeparateFromSourceDensity : Bool
    sourceDensitySeparateFromEntityDensity : Bool
    qidSeparateFromPublicationIdentity : Bool
    navigationSeparateFromSemanticTruth : Bool
    missingMetadataCreatesNegativeKnowledge : Bool

canonicalCoverageQualityBoundary : CoverageQualityBoundary
canonicalCoverageQualityBoundary =
  coverage-quality-boundary true true true true true false
