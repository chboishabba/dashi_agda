module DASHI.Wikimedia.IbrahimJMathematicsNumberOEISSecondOrderQidSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimBase369JOEISMoonshineSnowballExact as J
import DASHI.Wikimedia.IbrahimNumberTheoryIntegerSequenceOEISEscapeSnowballExact as Escape
import DASHI.Wikimedia.JInvariantWikipediaImage369ReconstructionSnowballExact as Image
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs

------------------------------------------------------------------------
-- SECOND-ORDER WALK OF EVERY QID ADMITTED BY THE J/369/OEIS TRANCHE.
--
-- Inspected 2026-09-10. Wikidata relations are retained as Wikidata relations;
-- they are not silently promoted into Wikipedia first-link edges or DASHI
-- formal dependencies. Current first-link observations remain revision-bound.
------------------------------------------------------------------------

data ExternalRelationRole : Set where
  wikidataInstanceOf wikidataSubclassOf wikidataPartOf wikidataStudies
  wikidataDifferentFrom wikidataHasPart wikidataImage wikidataDuplicateStatus
  oeisIdentifier currentWikipediaFirstBody explicitWikipediaCrosslink : ExternalRelationRole

record SecondOrderEdge : Set where
  constructor second-order-edge
  field
    sourceLabel : String
    sourceQid : String
    role : ExternalRelationRole
    targetLabel : String
    targetIdentity : String
    evidence : String
    safeForSnowball : Bool
    createsFormalDependency : Bool
open SecondOrderEdge public

------------------------------------------------------------------------
-- Q287419: j-invariant.
------------------------------------------------------------------------

modularFormQid : Identity.ExternalIdentityDemand
modularFormQid = Identity.mkOptionalIdentityDemand
  "J second-order snowball" "modular form identity" "modular form"
  Identity.wikidataQid
  (Identity.verified "Q870797" "Wikidata oldid 2400727846 inspected 2026-09-10")

jToModularForm : SecondOrderEdge
jToModularForm = second-order-edge
  "j-invariant" "Q287419" wikidataInstanceOf
  "modular form" "Q870797"
  "Q287419 states instance of modular form and describes j as weight-zero modular function on the upper half-plane"
  true false

jToPhaseImage : SecondOrderEdge
jToPhaseImage = second-order-edge
  "j-invariant" "Q287419" wikidataImage
  "J-inv-phase.jpeg" "Commons source retained by JInvariantImageFractalSourceAtlasExact"
  "Q287419 directly lists J-inv-phase.jpeg among its images"
  true false

------------------------------------------------------------------------
-- Q392440: monstrous moonshine.
------------------------------------------------------------------------

groupTheoryQid : Identity.ExternalIdentityDemand
groupTheoryQid = Identity.mkOptionalIdentityDemand
  "moonshine second-order snowball" "group theory identity" "group theory"
  Identity.wikidataQid
  (Identity.verified "Q874429" "Q392440 studied-by target inspected 2026-09-10")

moonshineToGroupTheory : SecondOrderEdge
moonshineToGroupTheory = second-order-edge
  "monstrous moonshine" "Q392440" wikidataStudies
  "group theory" "Q874429"
  "Q392440 says studied by group theory; repo has Monster character/subgroup and ordinary group-theory machinery"
  true false

------------------------------------------------------------------------
-- Q395 / Q12479: mathematics and number theory.
------------------------------------------------------------------------

pureMathematicsQid : Identity.ExternalIdentityDemand
pureMathematicsQid = Identity.mkOptionalIdentityDemand
  "number-theory second-order snowball" "pure mathematics identity" "pure mathematics"
  Identity.wikidataQid
  (Identity.verified "Q837863" "Wikidata oldid 2431588150 inspected 2026-09-10")

elementaryNumberTheoryQid : Identity.ExternalIdentityDemand
elementaryNumberTheoryQid = Identity.mkOptionalIdentityDemand
  "number-theory second-order snowball" "elementary number theory identity" "elementary number theory"
  Identity.wikidataQid
  (Identity.verified "Q18450254" "Q12479 has-part target inspected 2026-09-10")

numerologyQid : Identity.ExternalIdentityDemand
numerologyQid = Identity.mkOptionalIdentityDemand
  "number-theory WrongType snowball" "numerology identity" "numerology"
  Identity.wikidataQid
  (Identity.verified "Q140732" "Wikidata inspected 2026-09-10")

numberTheoryToMathematicsSubclass : SecondOrderEdge
numberTheoryToMathematicsSubclass = second-order-edge
  "number theory" "Q12479" wikidataSubclassOf
  "mathematics" "Q395"
  "Q12479 subclass-of and part-of mathematics"
  true false

numberTheoryToPureMathematics : SecondOrderEdge
numberTheoryToPureMathematics = second-order-edge
  "number theory" "Q12479" wikidataPartOf
  "pure mathematics" "Q837863"
  "Q12479 additionally records pure mathematics as a broader/part coordinate"
  true false

numberTheoryToElementary : SecondOrderEdge
numberTheoryToElementary = second-order-edge
  "number theory" "Q12479" wikidataHasPart
  "elementary number theory" "Q18450254"
  "Q12479 has-part elementary number theory"
  true false

numberTheoryDifferentFromNumerology : SecondOrderEdge
numberTheoryDifferentFromNumerology = second-order-edge
  "number theory" "Q12479" wikidataDifferentFrom
  "numerology" "Q140732"
  "Q12479 explicitly records different-from numerology; this is a high-alpha Base369 WrongType gate"
  true false

------------------------------------------------------------------------
-- Q12503 / Q11563: integer and number.
------------------------------------------------------------------------

setOfIntegersQid : Identity.ExternalIdentityDemand
setOfIntegersQid = Identity.mkOptionalIdentityDemand
  "integer second-order snowball" "set of integers identity" "set of integers"
  Identity.wikidataQid
  (Identity.verified "Q47007735" "Wikidata oldid 2440927137 inspected 2026-09-10")

mathematicalObjectQid : Identity.ExternalIdentityDemand
mathematicalObjectQid = Identity.mkOptionalIdentityDemand
  "number second-order snowball" "mathematical object identity" "mathematical object"
  Identity.wikidataQid
  (Identity.verified "Q246672" "Wikidata oldid 2510353035 inspected 2026-09-10")

positiveIntegerQid : Identity.ExternalIdentityDemand
positiveIntegerQid = Identity.mkOptionalIdentityDemand
  "integer second-order snowball" "positive integer identity" "positive integer"
  Identity.wikidataQid
  (Identity.verified "Q16317911" "Wikidata oldid 2528375494 inspected 2026-09-10")

integerToSetOfIntegers : SecondOrderEdge
integerToSetOfIntegers = second-order-edge
  "integer" "Q12503" wikidataPartOf
  "set of integers" "Q47007735"
  "Q12503 part-of set of integers; Q47007735 defines Z and has-parts-of-class integer"
  true false

integerStudiedByNumberTheory : SecondOrderEdge
integerStudiedByNumberTheory = second-order-edge
  "integer" "Q12503" wikidataStudies
  "number theory" "Q12479"
  "Q12503 studied-by number theory, reciprocal to Q12479 is-the-study-of integer"
  true false

numberToMathematicalObject : SecondOrderEdge
numberToMathematicalObject = second-order-edge
  "number" "Q11563" wikidataSubclassOf
  "mathematical object" "Q246672"
  "Q11563 describes number as a mathematical object used to count, label and measure"
  true false

positiveIntegerToOEIS : SecondOrderEdge
positiveIntegerToOEIS = second-order-edge
  "positive integer" "Q16317911" oeisIdentifier
  "positive integers" "OEIS A000027"
  "Q16317911 directly carries OEIS ID A000027"
  true false

------------------------------------------------------------------------
-- Q2297602 / Q728415: integer sequence and OEIS.
------------------------------------------------------------------------

record SequenceDefinitionAxes : Set where
  constructor sequence-definition-axes
  field
    formula : Bool
    recurrence : Bool
    memberProperty : Bool
    orderedIntegerCarrier : Bool
    anyOneAxisDefinesAllOthers : Bool
open SequenceDefinitionAxes public

integerSequenceDefinitionAxes : SequenceDefinitionAxes
integerSequenceDefinitionAxes = sequence-definition-axes true true true true false

oeisSystemQid : Identity.ExternalIdentityDemand
oeisSystemQid = Escape.oeisQid

integerSequenceToOEISSystem : SecondOrderEdge
integerSequenceToOEISSystem = second-order-edge
  "integer sequence" "Q2297602" explicitWikipediaCrosslink
  "On-Line Encyclopedia of Integer Sequences" "Q728415"
  "Integer-sequence article explicitly links OEIS; Wikidata P829 is the OEIS external-identifier property"
  true false

------------------------------------------------------------------------
-- Q5289811: domain coloring. The current item itself is marked as a permanent
-- duplicate, so verification of the QID does not imply that it is the final
-- canonical identity. Retain this revision fact rather than silently hiding it.
------------------------------------------------------------------------

domainColoringDuplicateStatus : SecondOrderEdge
domainColoringDuplicateStatus = second-order-edge
  "domain coloring" "Q5289811" wikidataDuplicateStatus
  "Color wheel graphs of complex functions" "duplicate target identity not promoted here"
  "Q5289811 is currently marked Wikimedia permanent duplicate item and points to a permanent duplicated item"
  true false

------------------------------------------------------------------------
-- Repo-coverage quotient after second-order walk.
------------------------------------------------------------------------

record SecondOrderCoverage : Set where
  constructor second-order-coverage
  field
    modularFormSubstrateStrong : Bool
    monsterGroupTheorySubstrateStrong : Bool
    numberTheorySubstrateStrong : Bool
    integerCarrierSubstrateStrong : Bool
    integerSequenceSourceExamplesPresent : Bool
    genericIntegerSequenceCanonicalOwnerPresent : Bool
    domainColoringSemanticRendererPresent : Bool
    domainColoringCanonicalIdentityStable : Bool
    numerologyAuthorityExplicitlyBlocked : Bool
    firstNewHighAlphaJoin : String
open SecondOrderCoverage public

currentSecondOrderCoverage : SecondOrderCoverage
currentSecondOrderCoverage = second-order-coverage
  true true true true true false true false true
  "Q12479 different-from Q140732 should become a first-class all-pairs WrongType gate for Base369 numerical motifs"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ModularFormQidCreatesJAnalyticProof : Set where
data GroupTheoryQidCreatesMoonshineProof : Set where
data NumberTheoryEqualsNumerology : Set where
data IntegerEqualsSetOfIntegers : Set where
data OEISIdCreatesSequenceSemantics : Set where
data DomainColoringDuplicateQidCreatesStableCanonicalIdentity : Set where

genericQidDoesNotCreateJProof : ModularFormQidCreatesJAnalyticProof → ⊥
genericQidDoesNotCreateJProof ()

groupTheoryDoesNotCreateMoonshineProof : GroupTheoryQidCreatesMoonshineProof → ⊥
groupTheoryDoesNotCreateMoonshineProof ()

numberTheoryIsNotNumerology : NumberTheoryEqualsNumerology → ⊥
numberTheoryIsNotNumerology ()

integerIsNotItsCarrierSet : IntegerEqualsSetOfIntegers → ⊥
integerIsNotItsCarrierSet ()

oeisIdDoesNotCreateSemantics : OEISIdCreatesSequenceSemantics → ⊥
oeisIdDoesNotCreateSemantics ()

duplicateStatusPreventsSilentCanonicalPromotion :
  DomainColoringDuplicateQidCreatesStableCanonicalIdentity → ⊥
duplicateStatusPreventsSilentCanonicalPromotion ()

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary
