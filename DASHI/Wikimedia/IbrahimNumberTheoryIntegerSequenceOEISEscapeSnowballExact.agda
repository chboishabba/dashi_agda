module DASHI.Wikimedia.IbrahimNumberTheoryIntegerSequenceOEISEscapeSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimMathematicsNumberTheoryOEISCycleSnowballExact as Cycle
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs

------------------------------------------------------------------------
-- CYCLE-PRESERVING SNOWBALL ESCAPE
--
-- The current first-link graph contains Mathematics <-> Number theory. We keep
-- that two-cycle intact. Further exploration uses separately typed secondary
-- body/Wikidata relations; these are NOT relabelled as first-link edges.
--
-- Current/source coordinates inspected 2026-09-10:
--   integer          Q12503, enwiki oldid 1349888421
--   integer sequence Q2297602, enwiki oldid 1359229061
--   OEIS             Q728415
--
-- Number theory's lead identifies integers as its primary subject. Integer's
-- current first body link is Number. Integer sequence's current first body link
-- is Mathematics and its body explicitly links OEIS examples.
------------------------------------------------------------------------

integerQid : Identity.ExternalIdentityDemand
integerQid = Identity.mkOptionalIdentityDemand
  "Ibrahim cycle-escape snowball"
  "integer external identity"
  "integer"
  Identity.wikidataQid
  (Identity.verified "Q12503" "Wikidata inspected 2026-09-10")

integerWikipedia : Identity.ExternalIdentityDemand
integerWikipedia = Identity.mkOptionalIdentityDemand
  "Ibrahim cycle-escape snowball"
  "integer exact Wikipedia revision"
  "Integer"
  Identity.wikimediaReferenceUrl
  (Identity.verified
    "https://en.wikipedia.org/w/index.php?title=Integer&oldid=1349888421"
    "enwiki retrieved current revision inspected 2026-09-10")

integerSequenceQid : Identity.ExternalIdentityDemand
integerSequenceQid = Identity.mkOptionalIdentityDemand
  "Ibrahim cycle-escape snowball"
  "integer sequence external identity"
  "integer sequence"
  Identity.wikidataQid
  (Identity.verified "Q2297602" "Wikidata oldid 2456443862 inspected 2026-09-10")

integerSequenceWikipedia : Identity.ExternalIdentityDemand
integerSequenceWikipedia = Identity.mkOptionalIdentityDemand
  "Ibrahim cycle-escape snowball"
  "integer sequence exact Wikipedia revision"
  "Integer sequence"
  Identity.wikimediaReferenceUrl
  (Identity.verified
    "https://en.wikipedia.org/w/index.php?title=Integer_sequence&oldid=1359229061"
    "enwiki retrieved current revision inspected 2026-09-10")

oeisQid : Identity.ExternalIdentityDemand
oeisQid = Identity.mkOptionalIdentityDemand
  "Ibrahim cycle-escape snowball"
  "OEIS database identity"
  "On-Line Encyclopedia of Integer Sequences"
  Identity.wikidataQid
  (Identity.verified "Q728415" "Wikidata inspected 2026-09-10")

------------------------------------------------------------------------
-- Edge roles remain distinct.
------------------------------------------------------------------------

data NavigationRole : Set where
  firstBodyEdge secondaryBodyEdge wikidataStudyRelation explicitArticleCrosslink : NavigationRole

record TypedNavigationEdge : Set where
  constructor typed-navigation-edge
  field
    source : String
    target : String
    role : NavigationRole
    evidenceReference : String
    currentObservation : Bool
    isIbrahim2014Edge : Bool
open TypedNavigationEdge public

numberTheoryToIntegerSubject : TypedNavigationEdge
numberTheoryToIntegerSubject = typed-navigation-edge
  "Number theory/Q12479"
  "Integer/Q12503"
  wikidataStudyRelation
  "Q12479 is-the-study-of integer; Number theory lead says devoted primarily to integers"
  true false

integerToNumber : TypedNavigationEdge
integerToNumber = typed-navigation-edge
  "Integer/Q12503"
  "Number/Q11563"
  firstBodyEdge
  "Integer oldid 1349888421: first body link in 'An integer is the number zero...' is Number"
  true false

integerToIntegerSequence : TypedNavigationEdge
integerToIntegerSequence = typed-navigation-edge
  "Integer/Q12503"
  "Integer sequence/Q2297602"
  secondaryBodyEdge
  "Integer oldid 1349888421 See also contains Integer sequence"
  true false

integerSequenceToMathematics : TypedNavigationEdge
integerSequenceToMathematics = typed-navigation-edge
  "Integer sequence/Q2297602"
  "Mathematics/Q395"
  firstBodyEdge
  "Integer sequence oldid 1359229061 begins 'In mathematics...'"
  true false

integerSequenceToOEIS : TypedNavigationEdge
integerSequenceToOEIS = typed-navigation-edge
  "Integer sequence/Q2297602"
  "OEIS/Q728415"
  explicitArticleCrosslink
  "Integer sequence oldid 1359229061 links OEIS in examples and See also"
  true false

------------------------------------------------------------------------
-- Snowball interpretation: preserve cycle, branch through explicit edge roles.
------------------------------------------------------------------------

record CycleEscapeProjection : Set where
  constructor cycle-escape-projection
  field
    firstLinkCycleRetained : Bool
    secondaryEdgesMayContinueSnowball : Bool
    secondaryEdgesRelabelledAsFirstLink : Bool
    integerSequenceCreatesOEISAuthority : Bool
    integerCarrierMayMeetRepoZ3 : Bool
    oeisSequenceIdsMayEnterAllPairs : Bool
    failedSequenceMatchMayCreateNewAxis : Bool
open CycleEscapeProjection public

canonicalCycleEscapeProjection : CycleEscapeProjection
canonicalCycleEscapeProjection = cycle-escape-projection
  true true false false true true true

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SecondaryEdgeCreatesIbrahimEdge : Set where
data OEISDatabaseCreatesSequenceTruth : Set where
data IntegerQidCreatesZ3FourierPhysics : Set where
data SameIntegerSequenceValueCreatesSameSequence : Set where

secondaryDoesNotBecomeFirstLink : SecondaryEdgeCreatesIbrahimEdge → ⊥
secondaryDoesNotBecomeFirstLink ()

oeisDatabaseIdentityDoesNotCreateTruth : OEISDatabaseCreatesSequenceTruth → ⊥
oeisDatabaseIdentityDoesNotCreateTruth ()

integerIdentityDoesNotCreateFourierPhysics : IntegerQidCreatesZ3FourierPhysics → ⊥
integerIdentityDoesNotCreateFourierPhysics ()

sharedValueDoesNotCreateSameSequence : SameIntegerSequenceValueCreatesSameSequence → ⊥
sharedValueDoesNotCreateSameSequence ()

cycleBoundary : Cycle.MathematicsNumberTheoryOEISBoundary
cycleBoundary = Cycle.canonicalMathematicsNumberTheoryOEISBoundary

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary
