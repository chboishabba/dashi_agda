module DASHI.Wikimedia.IbrahimMathematicsNumberTheoryOEISCycleSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimBase369JOEISMoonshineSnowballExact as J
import DASHI.Wikimedia.Base369OEISWikidataTeslaSnowballExact as Base369OEIS
import DASHI.Wikimedia.Base369Z3TriadOEISRegressionSnowballExact as TriadOEIS
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs

------------------------------------------------------------------------
-- CURRENT MATHEMATICS <-> NUMBER THEORY FIRST-LINK TWO-CYCLE
--
-- Ibrahim et al. study first-main-body-link traversal on the November 2014
-- English Wikipedia snapshot. Current English pages inspected 2026-09-10 show:
--
--   Mathematics   -> Number theory
--   Number theory -> Mathematics
--
-- On Mathematics the first lead sentence contains no hyperlink; the first
-- actual main-body hyperlink occurs in the next sentence and is Number theory.
-- Number theory's first body hyperlink is Mathematics.
--
-- Exact current revision IDs remain acquisition debt here. Observation date is
-- not promoted into a WikipediaRevisionReceipt and these current edges are not
-- backdated into Ibrahim's 2014 graph.
------------------------------------------------------------------------

mathematicsQid : Identity.ExternalIdentityDemand
mathematicsQid = Identity.mkOptionalIdentityDemand
  "Ibrahim Mathematics/Number theory cycle"
  "mathematics external identity"
  "mathematics"
  Identity.wikidataQid
  (Identity.verified "Q395" "Wikidata inspected 2026-09-10")

numberTheoryQid : Identity.ExternalIdentityDemand
numberTheoryQid = Identity.mkOptionalIdentityDemand
  "Ibrahim Mathematics/Number theory cycle"
  "number theory external identity"
  "number theory"
  Identity.wikidataQid
  (Identity.verified "Q12479" "Wikidata oldid 2508995335 inspected 2026-09-10")

mathematicsRevision : Identity.ExternalIdentityDemand
mathematicsRevision = Identity.mkOptionalIdentityDemand
  "Ibrahim Mathematics/Number theory cycle"
  "exact current Mathematics Wikipedia revision"
  "Mathematics"
  Identity.wikimediaReferenceUrl
  (Identity.unresolved "current page inspected 2026-09-10; exact permanent revision not yet retained")

numberTheoryRevision : Identity.ExternalIdentityDemand
numberTheoryRevision = Identity.mkOptionalIdentityDemand
  "Ibrahim Mathematics/Number theory cycle"
  "exact current Number theory Wikipedia revision"
  "Number theory"
  Identity.wikimediaReferenceUrl
  (Identity.unresolved "current page inspected 2026-09-10; exact permanent revision not yet retained")

record CurrentFirstLinkEdge : Set where
  constructor current-first-link-edge
  field
    sourceArticle : String
    sourceQid : String
    targetArticle : String
    targetQid : String
    observationDate : String
    bodyPolicy : String
    exactRevisionPaid : Bool
    equalsHistoricalIbrahim2014Edge : Bool
open CurrentFirstLinkEdge public

mathematicsToNumberTheory : CurrentFirstLinkEdge
mathematicsToNumberTheory = current-first-link-edge
  "Mathematics" "Q395" "Number theory" "Q12479" "2026-09-10"
  "first actual hyperlink in main-body lead; preceding first sentence has no link"
  false false

numberTheoryToMathematics : CurrentFirstLinkEdge
numberTheoryToMathematics = current-first-link-edge
  "Number theory" "Q12479" "Mathematics" "Q395" "2026-09-10"
  "first hyperlink in main-body lead"
  false false

record CurrentTwoCycleReceipt : Set where
  constructor current-two-cycle-receipt
  field
    leftToRight : CurrentFirstLinkEdge
    rightToLeft : CurrentFirstLinkEdge
    reciprocalCurrentNavigation : Bool
    semanticEquivalenceCreated : Bool
    formalDependencyCycleCreated : Bool
    historicalIbrahimCycleEstablished : Bool
open CurrentTwoCycleReceipt public

currentMathematicsNumberTheoryCycle : CurrentTwoCycleReceipt
currentMathematicsNumberTheoryCycle = current-two-cycle-receipt
  mathematicsToNumberTheory numberTheoryToMathematics
  true false false false

------------------------------------------------------------------------
-- OEIS / Base369 snowball through the number-theory fibre.
------------------------------------------------------------------------

data ArithmeticRole : Set where
  powerSequence coefficientSequence representationDegreeSequence divisorSequence
  incidenceCountSequence localStageAddress modularFunctionCoefficient otherArithmeticRole : ArithmeticRole

record SequenceRoleBridge : Set where
  constructor sequence-role-bridge
  field
    externalId : String
    role : ArithmeticRole
    repoObject : String
    exactNumericalIdentity : Bool
    exactSemanticIdentity : Bool
    mayEnterAllPairs : Bool
open SequenceRoleBridge public

powersOfThreeBridge : SequenceRoleBridge
powersOfThreeBridge = sequence-role-bridge
  "OEIS A000244" powerSequence
  "Base369 powers 3,9,27 and 3^9=19683"
  true false true

powersOfSevenBridge : SequenceRoleBridge
powersOfSevenBridge = sequence-role-bridge
  "OEIS A000420" incidenceCountSequence
  "cutoff-one ternary Z^3 raw triad count 343=7^3"
  true false true

modularJCoefficientBridge : SequenceRoleBridge
modularJCoefficientBridge = sequence-role-bridge
  "OEIS A000521" modularFunctionCoefficient
  "modular j coefficient 196884"
  true false true

monsterDegreeBridge : SequenceRoleBridge
monsterDegreeBridge = sequence-role-bridge
  "OEIS A001379" representationDegreeSequence
  "Monster irreducible representation degree 196883"
  true false true

monsterDivisorBridge : SequenceRoleBridge
monsterDivisorBridge = sequence-role-bridge
  "OEIS A309510" divisorSequence
  "divisors/factorisation of 196883"
  true false true

------------------------------------------------------------------------
-- Deliberately dangerous 27 collision.
--
-- The standard j-invariant formula contains a literal factor 27 in its
-- discriminant denominator. Base369 also has a genuine 27-state ternary cube.
-- Global all-pairs search must admit this numerical collision, but the number
-- alone does not furnish a map between elliptic/modular invariants and the
-- Base369 hypervoxel carrier.
------------------------------------------------------------------------

record NumericalCollisionCandidate : Set where
  constructor numerical-collision-candidate
  field
    numeral : String
    leftContext : String
    rightContext : String
    pairAdmissibleForInspection : Bool
    sameCarrierPaid : Bool
    factorsThroughNumeralAlone : Bool
    failedFactorisationMaySnowballContextAxis : Bool
open NumericalCollisionCandidate public

jFormula27VsBase36927 : NumericalCollisionCandidate
jFormula27VsBase36927 = numerical-collision-candidate
  "27"
  "j-invariant formula coefficient multiplying g3^2"
  "Base369 3x3x3 ternary hypervoxel state count"
  true false false true

------------------------------------------------------------------------
-- Firewalls / all-pairs behaviour.
------------------------------------------------------------------------

data CurrentTwoCycleCreatesSemanticEquivalence : Set where
data NumberTheoryParentCreatesOEISAuthority : Set where
data SameIntegerCreatesSameMathematicalObject : Set where
data LiteralTwentySevenCreatesCarrierIdentity : Set where
data CurrentCycleCreatesHistoricalCycle : Set where

cycleDoesNotCreateSemanticEquivalence : CurrentTwoCycleCreatesSemanticEquivalence → ⊥
cycleDoesNotCreateSemanticEquivalence ()

numberTheoryDoesNotCreateOEISAuthority : NumberTheoryParentCreatesOEISAuthority → ⊥
numberTheoryDoesNotCreateOEISAuthority ()

sameIntegerDoesNotCreateSameObject : SameIntegerCreatesSameMathematicalObject → ⊥
sameIntegerDoesNotCreateSameObject ()

twentySevenDoesNotCreateCarrierIdentity : LiteralTwentySevenCreatesCarrierIdentity → ⊥
twentySevenDoesNotCreateCarrierIdentity ()

currentCycleDoesNotBackdate : CurrentCycleCreatesHistoricalCycle → ⊥
currentCycleDoesNotBackdate ()

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary

record MathematicsNumberTheoryOEISBoundary : Set where
  constructor mathematics-number-theory-oeis-boundary
  field
    currentReciprocalNavigationRecorded : Bool
    exactQidsRecorded : Bool
    exactWikipediaRevisionsStillOpen : Bool
    oeisRolesRemainTyped : Bool
    everySequencePairGloballyEligible : Bool
    sameNumberDoesNotCollapseRoles : Bool
    failedNumericalFactorisationCanSnowball : Bool
    historicalIbrahimIdentityNotAssumed : Bool
open MathematicsNumberTheoryOEISBoundary public

canonicalMathematicsNumberTheoryOEISBoundary : MathematicsNumberTheoryOEISBoundary
canonicalMathematicsNumberTheoryOEISBoundary =
  mathematics-number-theory-oeis-boundary true true true true true true true true
