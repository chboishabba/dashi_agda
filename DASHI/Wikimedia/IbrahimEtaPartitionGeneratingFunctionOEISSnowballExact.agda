module DASHI.Wikimedia.IbrahimEtaPartitionGeneratingFunctionOEISSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimDedekindEtaQPochhammerPentagonalSnowballExact as EtaProduct
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs
import DASHI.Wikimedia.IntegerSequenceRecurrenceTetrationSnowballExact as Recurrence

------------------------------------------------------------------------
-- ETA PRODUCT -> INTEGER PARTITION -> GENERATING FUNCTION -> OEIS
--
-- Public coordinates inspected 2026-09-10:
--   integer partition  Q1082910
--   generating function Q860609, Wikidata oldid 2476634465
--   OEIS A000041 = partition numbers p(n)
--
-- Current EN Integer partition first-body link is Number theory.
-- Current EN Generating function first-body link is Mathematics.
-- These current traversal edges are not backdated to Ibrahim's 2014 graph.
------------------------------------------------------------------------

integerPartitionQid : Identity.ExternalIdentityDemand
integerPartitionQid = Identity.mkOptionalIdentityDemand
  "eta/partition snowball"
  "integer partition external identity"
  "integer partition"
  Identity.wikidataQid
  (Identity.verified "Q1082910" "Wikidata inspected 2026-09-10")

generatingFunctionQid : Identity.ExternalIdentityDemand
generatingFunctionQid = Identity.mkOptionalIdentityDemand
  "eta/partition snowball"
  "generating function external identity"
  "generating function"
  Identity.wikidataQid
  (Identity.verified "Q860609" "Wikidata oldid 2476634465 inspected 2026-09-10")

record OEISCoordinate : Set where
  constructor oeis-coordinate
  field
    oeisId : String
    subject : String
    exactSequenceIdentity : Bool
    analyticConvergenceCreated : Bool
open OEISCoordinate public

partitionNumbersOEIS : OEISCoordinate
partitionNumbersOEIS = oeis-coordinate
  "A000041"
  "partition numbers p(n): number of integer partitions of n"
  true false

data EdgeRole : Set where
  currentFirstBody combinatorialDefinition generatingFunctionRelation oeisIdentifier analyticProductRelation : EdgeRole

record TypedEdge : Set where
  constructor typed-edge
  field
    source : String
    target : String
    role : EdgeRole
    evidence : String
    createsFormalProof : Bool
    equalsHistoricalIbrahim2014Edge : Bool
open TypedEdge public

integerPartitionToNumberTheory : TypedEdge
integerPartitionToNumberTheory = typed-edge
  "Integer partition/Q1082910"
  "Number theory/Q12479"
  currentFirstBody
  "Current EN lead begins 'In number theory and combinatorics'; Number theory is the first body link"
  false false

generatingFunctionToMathematics : TypedEdge
generatingFunctionToMathematics = typed-edge
  "Generating function/Q860609"
  "Mathematics/Q395"
  currentFirstBody
  "Current EN lead begins 'In mathematics'; Mathematics is the first body link"
  false false

integerPartitionToPartitionNumbers : TypedEdge
integerPartitionToPartitionNumbers = typed-edge
  "Integer partition/Q1082910"
  "partition function p(n) / OEIS A000041"
  combinatorialDefinition
  "p(n) counts integer partitions of n; OEIS A000041 is the partition-number sequence"
  false false

partitionNumbersToGeneratingFunction : TypedEdge
partitionNumbersToGeneratingFunction = typed-edge
  "A000041 partition numbers"
  "ordinary generating function/Q860609"
  generatingFunctionRelation
  "partition numbers admit the classical Euler product generating function"
  false false

etaProductToPartitionGeneratingFunction : TypedEdge
etaProductToPartitionGeneratingFunction = typed-edge
  "(q;q)_infinity from Dedekind eta"
  "partition generating function 1/(q;q)_infinity"
  analyticProductRelation
  "same q-product syntax appears reciprocally in partition generating functions; this is a structural relation, not identity of analytic obligations"
  false false

record PartitionGeneratingFunctionProjection : Set where
  constructor partition-generating-function-projection
  field
    coefficientQueryMayFactorThroughGeneratingSeries : Bool
    combinatorialCountMayFactorThroughA000041 : Bool
    formalPowerSeriesRequiresAnalyticConvergence : Bool
    analyticEtaNonvanishingFactorsThroughPartitionCounts : Bool
    sharedQPochhammerExpressionCreatesSameObject : Bool
    recurrenceEqualsTetration : Bool
    failedAnalyticFactorisationMaySnowballConvergenceAxis : Bool
open PartitionGeneratingFunctionProjection public

canonicalPartitionGeneratingFunctionProjection : PartitionGeneratingFunctionProjection
canonicalPartitionGeneratingFunctionProjection = partition-generating-function-projection
  true true false false false false true

data FormalGeneratingSeriesCreatesAnalyticConvergence : Set where
data PartitionCountsCreateEtaZeroFree : Set where
data SharedProductCreatesSameAnalyticObject : Set where
data IntegerPartitionEqualsSetPartition : Set where
data CurrentTraversalCreatesHistoricalEdge : Set where

formalSeriesDoesNotCreateConvergence : FormalGeneratingSeriesCreatesAnalyticConvergence → ⊥
formalSeriesDoesNotCreateConvergence ()

partitionCountsDoNotCreateEtaZeroFree : PartitionCountsCreateEtaZeroFree → ⊥
partitionCountsDoNotCreateEtaZeroFree ()

sharedProductDoesNotCreateSameAnalyticObject : SharedProductCreatesSameAnalyticObject → ⊥
sharedProductDoesNotCreateSameAnalyticObject ()

integerPartitionDoesNotEqualSetPartition : IntegerPartitionEqualsSetPartition → ⊥
integerPartitionDoesNotEqualSetPartition ()

currentTraversalDoesNotBackdate : CurrentTraversalCreatesHistoricalEdge → ⊥
currentTraversalDoesNotBackdate ()

etaProductBoundary : EtaProduct.EtaProductSnowballBoundary
etaProductBoundary = EtaProduct.canonicalEtaProductSnowballBoundary

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary

recurrenceBoundary : Recurrence.SequenceTetrationSnowballBoundary
recurrenceBoundary = Recurrence.canonicalSequenceTetrationSnowballBoundary
