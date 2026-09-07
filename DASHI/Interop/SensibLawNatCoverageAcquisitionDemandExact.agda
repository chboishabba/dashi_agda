module DASHI.Interop.SensibLawNatCoverageAcquisitionDemandExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.ZelphBoundedGraphCoverageExact as Coverage
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- NAT Q/P COVERAGE RESIDUAL -> ACQUISITION DEMAND
--
-- Consumer-side descriptor for the exact property-family coordinate blocking a
-- Nat classification.  It intentionally does not import the #823-only
-- IntrospectiveProofLoopExact until that branch lands on master.
------------------------------------------------------------------------

data NatCoverageCoordinate : Set where
  subjectTypeFamily : NatCoverageCoordinate
  sourcePropertyFamily : NatCoverageCoordinate
  targetPropertyFamily : NatCoverageCoordinate
  qualifierProfileFamily : NatCoverageCoordinate
  referenceFamily : NatCoverageCoordinate
  temporalFamily : NatCoverageCoordinate

producerForCoverageCoordinate : NatCoverageCoordinate → Search.ProducerClass
producerForCoverageCoordinate subjectTypeFamily = Search.identityProducer
producerForCoverageCoordinate sourcePropertyFamily = Search.empiricalEvidenceProducer
producerForCoverageCoordinate targetPropertyFamily = Search.empiricalEvidenceProducer
producerForCoverageCoordinate qualifierProfileFamily = Search.empiricalEvidenceProducer
producerForCoverageCoordinate referenceFamily = Search.propositionSourceProducer
producerForCoverageCoordinate temporalFamily = Search.temporalProducer

record NatCoverageResidual : Set where
  constructor nat-coverage-residual
  field
    subjectQidReference : String
    propertyReference : String
    coverageStatus : Coverage.QueryCoverageStatus
    coordinate : NatCoverageCoordinate
    graphRevisionReference : String
    coveragePolicyReference : String
    consumerReference : String
    residualReference : String
open NatCoverageResidual public

record NatCoverageAcquisitionDemand (residual : NatCoverageResidual) : Set where
  constructor nat-coverage-acquisition-demand
  field
    producer : Search.ProducerClass
    producerMatchesCoordinate : producer ≡ producerForCoverageCoordinate (coordinate residual)
    exactSubjectReference : String
    exactPropertyReference : String
    requiredRepresentationReference : String
    acquisitionReference : String
open NatCoverageAcquisitionDemand public

-- Concrete live example: an uninspected P14143 family cannot be paid by a P31
-- fetch, a peer-item fetch, or a merely successful shard transport.
p14143UninspectedResidual : NatCoverageResidual
p14143UninspectedResidual =
  nat-coverage-residual
    "current Nat subject QID"
    "P14143"
    Coverage.queryCoverageUninspected
    targetPropertyFamily
    "current graph revision"
    "Nat P5991->P14143 coverage policy"
    "Nat migration peer/target-property consumer"
    "P14143 target property family has not been inspected under the current revision/policy"

p14143UninspectedDemand : NatCoverageAcquisitionDemand p14143UninspectedResidual
p14143UninspectedDemand =
  nat-coverage-acquisition-demand
    Search.empiricalEvidenceProducer
    refl
    "the same Nat subject QID"
    "P14143"
    "native statement-family coverage or a certified representation complete for the P14143 query family"
    "acquire exactly the P14143 Q/P family required by the live Nat residual"

------------------------------------------------------------------------
-- Payment is downstream of acquisition.  A returned row, successful transport,
-- or complete coverage for another property does not close this residual.
------------------------------------------------------------------------

data ShardTransportPaysCoverageResidual : Set where
data OtherPropertyCoveragePaysP14143 : Set where
data ReturnedRowPaysCoverageResidual : Set where
data AcquisitionDemandCreatesMigrationAuthority : Set where

data CoverageRecomputationReceipt : Set where
  coverage-recomputed : CoverageRecomputationReceipt

shardTransportDoesNotPayCoverageResidual : ShardTransportPaysCoverageResidual → ⊥
shardTransportDoesNotPayCoverageResidual ()

otherPropertyDoesNotPayP14143Residual : OtherPropertyCoveragePaysP14143 → ⊥
otherPropertyDoesNotPayP14143Residual ()

returnedRowDoesNotPayCoverageResidualByExistence : ReturnedRowPaysCoverageResidual → ⊥
returnedRowDoesNotPayCoverageResidualByExistence ()

acquisitionDemandDoesNotCreateMigrationAuthority : AcquisitionDemandCreatesMigrationAuthority → ⊥
acquisitionDemandDoesNotCreateMigrationAuthority ()

record NatCoverageAcquisitionBoundary : Set where
  constructor nat-coverage-acquisition-boundary
  field
    demandIndexedByExactSubjectPropertyResidual : Bool
    producerDerivedFromMissingCoordinate : Bool
    transportEqualsCoveragePayment : Bool
    anotherPropertyCanPayTargetPropertyResidual : Bool
    returnedRowEqualsCoveragePayment : Bool
    demandCreatesMigrationAuthority : Bool
    recomputationStillRequired : Bool
    pending823WeldExplicit : Bool

canonicalNatCoverageAcquisitionBoundary : NatCoverageAcquisitionBoundary
canonicalNatCoverageAcquisitionBoundary =
  nat-coverage-acquisition-boundary true true false false false false true true
