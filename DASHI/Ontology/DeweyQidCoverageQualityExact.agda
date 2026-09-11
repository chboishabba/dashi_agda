module DASHI.Ontology.DeweyQidCoverageQualityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

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

canonicalRepositoryCoverageHeadline : RepositoryCoverageHeadline
canonicalRepositoryCoverageHeadline =
  repository-coverage-headline 15796 15796 3696 1179 false

navierStokesVolume yangMillsVolume pnfVolume biologyVolume lawVolume interopVolume : ParentClusterCoverageObservation
navierStokesVolume = parent-cluster-coverage-observation "532.051" "Navier-Stokes closure" 5218 0 0 0 0 0 unmeasured unmeasured unmeasured
yangMillsVolume = parent-cluster-coverage-observation "530.144" "Yang-Mills" 2589 0 0 0 0 0 unmeasured unmeasured unmeasured
pnfVolume = parent-cluster-coverage-observation "153.420" "PNF cognition" 622 0 0 0 0 0 unmeasured unmeasured unmeasured
biologyVolume = parent-cluster-coverage-observation "570.000" "General biology" 531 0 0 0 0 0 unmeasured unmeasured unmeasured
lawVolume = parent-cluster-coverage-observation "340.000" "Law" 217 0 0 0 0 0 unmeasured unmeasured unmeasured
interopVolume = parent-cluster-coverage-observation "004.650" "Interoperability" 201 0 0 0 0 0 unmeasured unmeasured unmeasured

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
firstLinkDoesNotCreateConceptualDependence : FirstLinkReachabilityImpliesConceptualDependence → ⊥
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
