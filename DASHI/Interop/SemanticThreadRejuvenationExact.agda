{-# OPTIONS --safe #-}
module DASHI.Interop.SemanticThreadRejuvenationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

-- A typed protocol model, not a claim that the Python runtime is verified.
-- A stage carries its predecessor and evidence of its transition.
record Thread : Set where
  constructor thread
  field identifier : String

record PNF (source : Thread) : Set where
  constructor pnf
  field factorCount : Nat

record World (source : Thread) (factors : PNF source) : Set where
  constructor world
  field registeredCount : Nat

record WorldRelative (source : Thread) (factors : PNF source)
                     (registered : World source factors) : Set where
  constructor relative
  field capsule : String

record Rejuvenated (source : Thread) (factors : PNF source)
                   (registered : World source factors)
                   (relativeState : WorldRelative source factors registered) : Set where
  constructor rejuvenated
  field child : Thread
        lineageRecorded : Bool
        lineageRecordedTrue : lineageRecorded ≡ true
        proofPromotionByEnrichment : Bool
        proofPromotionByEnrichmentFalse : proofPromotionByEnrichment ≡ false

lineagePreserved :
  {t : Thread} {p : PNF t} {w : World t p}
  {r : WorldRelative t p w} →
  (result : Rejuvenated t p w r) →
  Rejuvenated.lineageRecorded result ≡ true
lineagePreserved = Rejuvenated.lineageRecordedTrue

enrichmentCannotPromoteProof :
  {t : Thread} {p : PNF t} {w : World t p}
  {r : WorldRelative t p w} →
  (result : Rejuvenated t p w r) →
  Rejuvenated.proofPromotionByEnrichment result ≡ false
enrichmentCannotPromoteProof = Rejuvenated.proofPromotionByEnrichmentFalse

-- Storage authority is a protocol-level invariant.
data Database : Set where
  postgresql : Database

record CommittedWorld (source : Thread) (factors : PNF source) : Set where
  constructor committed
  field store : Database
        registered : World source factors

soleStore : {t : Thread} {p : PNF t} →
  (committedWorld : CommittedWorld t p) →
  CommittedWorld.store committedWorld ≡ postgresql
soleStore _ = refl

-- Topic-label operations are syntax, not an assertion of semantic equivalence.
-- Preserve the distinction between a property collapse and temporal expansion.
data TopicOperation : Set where
  collapseProperty : String → TopicOperation
  expandTemporal : String → TopicOperation

record TopicOnePlan : Set where
  constructor topicOnePlan
  field autoCollapse : TopicOperation
        lastCollapse : TopicOperation
        nowExpansion : TopicOperation

canonicalTopicOne : TopicOnePlan
canonicalTopicOne = topicOnePlan
  (collapseProperty "auto")
  (collapseProperty "last")
  (expandTemporal "now")

topicOneAutoPreserved : TopicOnePlan.autoCollapse canonicalTopicOne ≡ collapseProperty "auto"
topicOneAutoPreserved = refl

topicOneLastPreserved : TopicOnePlan.lastCollapse canonicalTopicOne ≡ collapseProperty "last"
topicOneLastPreserved = refl

topicOneNowPreserved : TopicOnePlan.nowExpansion canonicalTopicOne ≡ expandTemporal "now"
topicOneNowPreserved = refl

-- Worker 01: the lexical sub-motif is retained without assuming that
-- comparative 'rather/than' and a 'change' event are equivalent.
data ComparativeChangeMotif : Set where
  ratherThan : String → String → ComparativeChangeMotif
  change : String → ComparativeChangeMotif

record Worker01Motif : Set where
  constructor worker01Motif
  field comparison : ComparativeChangeMotif
        mutation : ComparativeChangeMotif

canonicalWorker01 : Worker01Motif
canonicalWorker01 = worker01Motif (ratherThan "rather" "than") (change "change")

worker01ComparisonPreserved :
  Worker01Motif.comparison canonicalWorker01 ≡ ratherThan "rather" "than"
worker01ComparisonPreserved = refl

worker01ChangePreserved :
  Worker01Motif.mutation canonicalWorker01 ≡ change "change"
worker01ChangePreserved = refl

-- Worker 06: parsed text is an explicit input, not a parsing correctness claim.
-- Collapsing an auto node changes only the visibility bit; its text is retained.
record ParsedAutoNode : Set where
  constructor parsedAutoNode
  field
    parsedText : String
    expanded : Bool

collapseAuto : ParsedAutoNode → ParsedAutoNode
collapseAuto node = parsedAutoNode (ParsedAutoNode.parsedText node) false

collapseAutoPreservesText : (node : ParsedAutoNode) →
  ParsedAutoNode.parsedText (collapseAuto node) ≡ ParsedAutoNode.parsedText node
collapseAutoPreservesText node = refl

collapseAutoHides : (node : ParsedAutoNode) →
  ParsedAutoNode.expanded (collapseAuto node) ≡ false
collapseAutoHides node = refl

collapseAutoIdempotent : (node : ParsedAutoNode) →
  collapseAuto (collapseAuto node) ≡ collapseAuto node
collapseAutoIdempotent (parsedAutoNode text true) = refl
collapseAutoIdempotent (parsedAutoNode text false) = refl

-- Worker 08: a text fixture is assessed by an explicit expected result.
-- A self-declared test receipt is not evidence that a runtime test executed.
record TextTestCase : Set where
  constructor textTestCase
  field
    inputText : String
    expectedText : String

record TextTestResult : Set where
  constructor textTestResult
  field
    testCase : TextTestCase
    observedText : String
    matchesExpected : observedText ≡ TextTestCase.expectedText testCase

canonicalTextTest : (text : String) → TextTestResult
canonicalTextTest text = textTestResult (textTestCase text text) text refl

canonicalTextTestMatches : (text : String) →
  TextTestResult.observedText (canonicalTextTest text) ≡ text
canonicalTextTestMatches text = refl

-- Worker 09: packaging an already witnessed test preserves its witness.
-- It does not establish that a real test runner executed the test.
record AssessedPackage : Set where
  constructor assessedPackage
  field
    packageLabel : String
    packagedResult : TextTestResult

packageSatisfied : String → TextTestResult → AssessedPackage
packageSatisfied label result = assessedPackage label result

packagePreservesObserved : (label : String) (result : TextTestResult) →
  TextTestResult.observedText
    (AssessedPackage.packagedResult (packageSatisfied label result)) ≡
  TextTestResult.observedText result
packagePreservesObserved label result = refl

packagePreservesExpected : (label : String) (result : TextTestResult) →
  TextTestCase.expectedText
    (TextTestResult.testCase
      (AssessedPackage.packagedResult (packageSatisfied label result))) ≡
  TextTestCase.expectedText (TextTestResult.testCase result)
packagePreservesExpected label result = refl

-- Worker 11: the comparative phrase and the selected state remain distinct.
-- This does not assert that the phrase was parsed or interpreted correctly.
record ComparativeState : Set where
  constructor comparativeState
  field
    phrase : ComparativeChangeMotif
    selected : String

chooseRather : String → String → ComparativeState
chooseRather preferred alternative =
  comparativeState (ratherThan preferred alternative) preferred

chooseRatherPreservesPhrase : (preferred alternative : String) →
  ComparativeState.phrase (chooseRather preferred alternative) ≡
  ratherThan preferred alternative
chooseRatherPreservesPhrase preferred alternative = refl

chooseRatherSelectsPreferred : (preferred alternative : String) →
  ComparativeState.selected (chooseRather preferred alternative) ≡ preferred
chooseRatherSelectsPreferred preferred alternative = refl
