module DASHI.Wikimedia.IbrahimPartitionSymmetricGroupRepresentationSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimEtaPartitionGeneratingFunctionOEISSnowballExact as Partition
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs
import DASHI.Moonshine.GradedRepresentation as GR

------------------------------------------------------------------------
-- INTEGER PARTITION -> SYMMETRIC GROUP / REPRESENTATION SNOWBALL
--
-- External coordinates inspected 2026-09-11:
--   integer partition                  Q1082910
--   symmetric group                    Q849512
--   abstract algebra                   Q159943
--   group representation               Q1055807
--   character of a group representation Q600043
--   Young tableau / Young diagram      Q2166280
--   OEIS A000041                       partition numbers p(n)
--
-- Current English Symmetric group begins "In abstract algebra..." and its
-- first main-body hyperlink is Abstract algebra.  Its body separately treats
-- conjugacy classes and representation theory.  OEIS A000041 records p(n) as
-- the partition-number sequence and also as the count of conjugacy classes /
-- irreducible complex representations of S_n.  These are typed relations, not
-- claims that the combinatorial partition object equals a representation.
------------------------------------------------------------------------

symmetricGroupQid : Identity.ExternalIdentityDemand
symmetricGroupQid = Identity.mkOptionalIdentityDemand
  "partition/symmetric-group Ibrahim snowball"
  "symmetric group external identity"
  "symmetric group"
  Identity.wikidataQid
  (Identity.verified "Q849512" "Wikidata inspected 2026-09-11")

abstractAlgebraQid : Identity.ExternalIdentityDemand
abstractAlgebraQid = Identity.mkOptionalIdentityDemand
  "symmetric-group current first-link target"
  "abstract algebra external identity"
  "abstract algebra"
  Identity.wikidataQid
  (Identity.verified "Q159943" "Wikidata oldid 2509231927 inspected 2026-09-11")

groupRepresentationQid : Identity.ExternalIdentityDemand
groupRepresentationQid = Identity.mkOptionalIdentityDemand
  "partition/symmetric-group representation snowball"
  "group representation external identity"
  "group representation"
  Identity.wikidataQid
  (Identity.verified "Q1055807" "Wikidata inspected 2026-09-11")

groupCharacterQid : Identity.ExternalIdentityDemand
groupCharacterQid = Identity.mkOptionalIdentityDemand
  "partition/symmetric-group representation snowball"
  "character external identity"
  "character of a group representation"
  Identity.wikidataQid
  (Identity.verified "Q600043" "Wikidata inspected 2026-09-11")

youngTableauQid : Identity.ExternalIdentityDemand
youngTableauQid = Identity.mkOptionalIdentityDemand
  "partition/symmetric-group representation snowball"
  "Young tableau / Young diagram external identity"
  "Young tableau"
  Identity.wikidataQid
  (Identity.verified "Q2166280" "Wikidata oldid 2440388593 inspected 2026-09-11")

------------------------------------------------------------------------
-- Typed navigation / mathematical roles.
------------------------------------------------------------------------

data EdgeRole : Set where
  currentFirstBody combinatorialIndexing conjugacyClassIndexing
  irreducibleRepresentationIndexing representationCharacter
  genericRepositorySubstrate : EdgeRole

record TypedEdge : Set where
  constructor typed-edge
  field
    source : String
    target : String
    role : EdgeRole
    evidence : String
    createsSameObject : Bool
    createsFormalProof : Bool
    equalsHistoricalIbrahim2014Edge : Bool
open TypedEdge public

symmetricGroupToAbstractAlgebra : TypedEdge
symmetricGroupToAbstractAlgebra = typed-edge
  "Symmetric group/Q849512"
  "Abstract algebra/Q159943"
  currentFirstBody
  "Current EN Symmetric group lead begins 'In abstract algebra'; Abstract algebra is the first body hyperlink"
  false false false

partitionToConjugacyClasses : TypedEdge
partitionToConjugacyClasses = typed-edge
  "integer partitions of n / A000041"
  "conjugacy classes of S_n"
  conjugacyClassIndexing
  "conjugacy classes of S_n are indexed by integer partitions of n via cycle type"
  false false false

partitionToIrreducibles : TypedEdge
partitionToIrreducibles = typed-edge
  "integer partitions of n / A000041"
  "irreducible complex representations of S_n"
  irreducibleRepresentationIndexing
  "irreducible complex representations/characters of S_n are indexed by partitions of n"
  false false false

youngTableauToRepresentation : TypedEdge
youngTableauToRepresentation = typed-edge
  "Young tableau/Q2166280"
  "group representation/Q1055807"
  combinatorialIndexing
  "Young diagrams/tableaux are combinatorial objects used in symmetric-group representation theory; hook-length dimension formula is externally recorded"
  false false false

characterToRepresentation : TypedEdge
characterToRepresentation = typed-edge
  "character/Q600043"
  "group representation/Q1055807"
  representationCharacter
  "Wikidata defines the character as the trace class-function attached to a representation"
  false false false

repoGenericRepresentationAPI : TypedEdge
repoGenericRepresentationAPI = typed-edge
  "DASHI.Moonshine.GradedRepresentation"
  "group representation/Q1055807"
  genericRepositorySubstrate
  "repo already has action-first finite-dimensional representation API with group action and trace"
  false false false

------------------------------------------------------------------------
-- Explicit repository reuse: we reuse the generic API shape, but do not
-- manufacture an S_n carrier, partition-indexed irreducible family, Specht
-- module, or character table.
------------------------------------------------------------------------

record SymmetricRepresentationFrontier : Set where
  constructor symmetric-representation-frontier
  field
    genericGroupAPIExists : Bool
    genericFiniteDimensionalRepresentationAPIExists : Bool
    genericTraceCharacterSubstrateExists : Bool
    symmetricGroupCarrierConstructed : Bool
    permutationActionConstructed : Bool
    partitionCycleTypeBijectionConstructed : Bool
    partitionIndexedIrreduciblesConstructed : Bool
    YoungDiagramCarrierConstructed : Bool
    SpechtModuleConstructionConstructed : Bool
    symmetricCharacterTableConstructed : Bool
    a000041CountIdentityRetained : Bool
    architectureStillMissing : Bool
    nextResidual : String
open SymmetricRepresentationFrontier public

currentSymmetricRepresentationFrontier : SymmetricRepresentationFrontier
currentSymmetricRepresentationFrontier = symmetric-representation-frontier
  true true true
  false false false false false false false
  true true
  "specialize the existing finite-group representation API to S_n: construct permutations/group law, prove conjugacy classes are indexed by cycle-type partitions, then add partition/Young-diagram indexed irreducibles; do not infer any of these from the equality of counts alone"

------------------------------------------------------------------------
-- All-pairs / FactorsThrough consequences.
------------------------------------------------------------------------

record PartitionRepresentationProjection : Set where
  constructor partition-representation-projection
  field
    countingQueryMayFactorThroughA000041 : Bool
    conjugacyClassIdentityFactorsThroughCountAlone : Bool
    irreducibleRepresentationIdentityFactorsThroughCountAlone : Bool
    partitionShapeMayCarryMoreInformationThanCount : Bool
    YoungDiagramMayCarryMoreInformationThanPartitionNumber : Bool
    MonsterCharacterAPIImpliesSymmetricSpecificConstruction : Bool
    failedCountFactorisationMaySnowballIndexingAxis : Bool
open PartitionRepresentationProjection public

canonicalPartitionRepresentationProjection : PartitionRepresentationProjection
canonicalPartitionRepresentationProjection = partition-representation-projection
  true false false true true false true

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SameCountCreatesSameObjects : Set where
data PartitionCreatesRepresentationWithoutConstruction : Set where
data GenericCharacterAPICreatesSymmetricCharacterTable : Set where
data YoungDiagramEqualsRepresentation : Set where
data CurrentFirstLinkCreatesHistoricalEdge : Set where

sameCountDoesNotCreateSameObjects : SameCountCreatesSameObjects → ⊥
sameCountDoesNotCreateSameObjects ()

partitionDoesNotCreateRepresentation : PartitionCreatesRepresentationWithoutConstruction → ⊥
partitionDoesNotCreateRepresentation ()

genericAPIDoesNotCreateSymmetricTable : GenericCharacterAPICreatesSymmetricCharacterTable → ⊥
genericAPIDoesNotCreateSymmetricTable ()

youngDiagramDoesNotEqualRepresentation : YoungDiagramEqualsRepresentation → ⊥
youngDiagramDoesNotEqualRepresentation ()

currentFirstLinkDoesNotBackdate : CurrentFirstLinkCreatesHistoricalEdge → ⊥
currentFirstLinkDoesNotBackdate ()

partitionBoundary : Partition.PartitionGeneratingFunctionProjection
partitionBoundary = Partition.canonicalPartitionGeneratingFunctionProjection

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary
