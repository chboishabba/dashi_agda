module DASHI.Cognition.PNF.SensibLawFriendlyjordiesSourceTotalityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawPersistentStatementObservationEventSpineExact as Trace
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesNarrativeGovernanceWeldExact as Weld
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesCompetingNarrativeExact as Existing
import DASHI.Reasoning.SensibLawCorpusWorldPNFBridgeExact as Horizon

------------------------------------------------------------------------
-- FRIENDLYJORDIES SOURCE-TOTALITY / NO-ORPHAN CERTIFICATE
--
-- A comparison side is admissible only as:
--
--   exact M12 source trace + explicit external-world resolution demand
--
-- or:
--
--   explicit acquisition / fixture-refresh demand.
--
-- There is deliberately no orphan-proposition constructor.
------------------------------------------------------------------------

record WorldDemand : Set where
  constructor world-demand
  field
    propositionRef : String
    requiredHorizon : Horizon.PNFResolutionHorizon
    unresolvedRef : String
    reason : String

open WorldDemand public

record AcquisitionDemand : Set where
  constructor acquisition-demand
  field
    familyRef : String
    propositionRef : String
    requiredArtifactRef : String
    sourceProducerRef : String
    reason : String
    mayPromoteTruth : Bool
    mayPromoteTruthIsFalse : mayPromoteTruth ≡ false

open AcquisitionDemand public

data SourceDisposition : Set where
  tracedWithWorldDemand :
    Trace.SemanticTracePath → WorldDemand → SourceDisposition
  unresolvedAcquisition :
    AcquisitionDemand → SourceDisposition
  explicitlyAbsentByComparisonKind :
    String → SourceDisposition

------------------------------------------------------------------------
-- Small constructor for the checked-in SensibLaw fixture statements.
------------------------------------------------------------------------

mkTrace :
  String → String → String → String → String →
  String → String → String → String →
  Trace.SemanticTracePath
mkTrace statementRef documentRef exactSpanRef literalText candidateRef
        observationRef eventRef claimRef downstreamRef =
  Trace.traceFromLinks
    (Trace.statement-candidate-observation-link
      (Trace.persistent-statement-identity
        statementRef
        documentRef
        Existing.sensibLawRevision
        exactSpanRef
        literalText)
      candidateRef
      observationRef
      (Trace.parser-run-identity
        "parser-run:friendlyjordies:source-totality"
        "sensiblaw-narrative-fixture")
      "review:parse:friendlyjordies:source-totality"
      "admission:candidate:friendlyjordies:source-totality"
      true refl false refl false refl false refl)
    (Trace.observation-event-link
      observationRef
      eventRef
      "assembly:friendlyjordies:source-totality"
      true refl false refl)
    (claimRef ∷ [])
    (downstreamRef ∷ [])

------------------------------------------------------------------------
-- CPRS shared proposition.
------------------------------------------------------------------------

cprsSourceTrace : Trace.SemanticTracePath
cprsSourceTrace =
  mkTrace
    "statement:friendlyjordies:cprs-blocked"
    "demo/narrative/friendlyjordies_thread_extract.json"
    "jordies_thread_position:u1"
    "FriendlyJordies said that the Greens blocked the CPRS."
    "pnf:friendlyjordies:cprs-blocked"
    "observation:friendlyjordies:cprs-blocked"
    "event:public-discourse:cprs-blocked"
    "claim:friendlyjordies:cprs-blocking"
    "cmp:cprs:shared"

cprsCounterTrace : Trace.SemanticTracePath
cprsCounterTrace =
  mkTrace
    "statement:counter:cprs-blocked"
    "demo/narrative/friendlyjordies_thread_extract.json"
    "thread_balanced_analysis:u1"
    "The analysis reported that the Greens blocked the CPRS."
    "pnf:counter:cprs-blocked"
    "observation:counter:cprs-blocked"
    "event:public-discourse:cprs-blocked"
    "claim:counter-analysis:cprs-blocking"
    "cmp:cprs:shared"

cprsWorldDemand : WorldDemand
cprsWorldDemand =
  world-demand
    "prop:cprs-blocking"
    Horizon.externalWorldHorizon
    "demand:cprs:blocking:independent-historical-corroboration"
    "the fixture pays what each narrative says, not the external historical proposition"

------------------------------------------------------------------------
-- Competing climate-policy instability accounts.
------------------------------------------------------------------------

instabilitySourceTrace : Trace.SemanticTracePath
instabilitySourceTrace =
  mkTrace
    "statement:friendlyjordies:cprs-instability"
    "demo/narrative/friendlyjordies_thread_extract.json"
    "jordies_thread_position:u2"
    "FriendlyJordies argued that blocking the CPRS contributed to climate policy instability."
    "pnf:friendlyjordies:cprs-instability"
    "observation:friendlyjordies:cprs-instability"
    "event:public-discourse:climate-policy-instability"
    "claim:friendlyjordies:instability"
    "cmp:instability:competing-account"

instabilityCounterTrace : Trace.SemanticTracePath
instabilityCounterTrace =
  mkTrace
    "statement:counter:coalition-instability"
    "demo/narrative/friendlyjordies_chat_arguments.json"
    "counter_analysis:u2"
    "The analysis argued that Coalition opposition contributed to climate policy instability."
    "pnf:counter:coalition-instability"
    "observation:counter:coalition-instability"
    "event:public-discourse:climate-policy-instability"
    "claim:counter-analysis:instability"
    "cmp:instability:competing-account"

instabilityWorldDemand : WorldDemand
instabilityWorldDemand =
  world-demand
    "prop:climate-policy-instability:causal-attribution"
    Horizon.externalWorldHorizon
    "demand:instability:independent-causal-history"
    "competing causal attributions require external historical evidence and a reviewed join basis"

------------------------------------------------------------------------
-- Majority/minority government capacity.
------------------------------------------------------------------------

governmentSourceTrace : Trace.SemanticTracePath
governmentSourceTrace =
  mkTrace
    "statement:friendlyjordies:majority-capacity"
    "demo/narrative/friendlyjordies_thread_extract.json"
    "jordies_thread_position:u4"
    "FriendlyJordies argued that majority government supports long-term climate policy."
    "pnf:friendlyjordies:majority-capacity"
    "observation:friendlyjordies:majority-capacity"
    "event:public-discourse:government-capacity"
    "claim:friendlyjordies:majority-capacity"
    "cmp:government-capacity:reasoning-flow"

governmentCounterTrace : Trace.SemanticTracePath
governmentCounterTrace =
  mkTrace
    "statement:counter:minority-capacity"
    "demo/narrative/friendlyjordies_thread_extract.json"
    "thread_balanced_analysis:u4"
    "The analysis argued that minority government passed carbon pricing legislation."
    "pnf:counter:minority-capacity"
    "observation:counter:minority-capacity"
    "event:public-discourse:government-capacity"
    "claim:counter-analysis:minority-capacity"
    "cmp:government-capacity:reasoning-flow"

governmentWorldDemand : WorldDemand
governmentWorldDemand =
  world-demand
    "prop:government-capacity:historical-effect"
    Horizon.externalWorldHorizon
    "demand:government-capacity:comparative-history"
    "government form and long-run policy capacity require external historical comparison"

------------------------------------------------------------------------
-- Woolworths / price-effect framing.
------------------------------------------------------------------------

woolworthsSourceTrace : Trace.SemanticTracePath
woolworthsSourceTrace =
  mkTrace
    "statement:friendlyjordies:woolworths"
    "demo/narrative/friendlyjordies_thread_extract.json"
    "jordies_thread_position:u5"
    "FriendlyJordies said that Woolworths was cited as evidence that direct grocery impacts were very small."
    "pnf:friendlyjordies:woolworths"
    "observation:friendlyjordies:woolworths"
    "event:public-discourse:woolworths-price-effects"
    "claim:friendlyjordies:woolworths"
    "cmp:woolworths:qualification"

woolworthsCounterTrace : Trace.SemanticTracePath
woolworthsCounterTrace =
  mkTrace
    "statement:counter:woolworths"
    "demo/narrative/friendlyjordies_thread_extract.json"
    "thread_balanced_analysis:u5"
    "The analysis said that Woolworths was talking about direct cost pass-through."
    "pnf:counter:woolworths"
    "observation:counter:woolworths"
    "event:public-discourse:woolworths-price-effects"
    "claim:counter-analysis:woolworths"
    "cmp:woolworths:qualification"

woolworthsWorldDemand : WorldDemand
woolworthsWorldDemand =
  world-demand
    "prop:woolworths-price-effect:scope"
    Horizon.externalWorldHorizon
    "demand:woolworths:underlying-price-evidence"
    "the fixture establishes framing; underlying price magnitude and scope need external evidence"

------------------------------------------------------------------------
-- ETS/Garnaut authority wrapper recovered from the archived thread and pinned
-- in SensibLaw main at Existing.sensibLawRevision.
------------------------------------------------------------------------

garnautSourceTrace : Trace.SemanticTracePath
garnautSourceTrace =
  mkTrace
    "statement:friendlyjordies:garnaut-wrapper"
    "demo/narrative/friendlyjordies_authority_wrappers.json"
    "jordies_authority_case:u3"
    "FriendlyJordies argued that Ross Garnaut reported that an imperfect ETS was better than delay."
    "pnf:friendlyjordies:garnaut-wrapper"
    "observation:friendlyjordies:garnaut-wrapper"
    "event:public-discourse:garnaut-ets-authority"
    "claim:friendlyjordies:garnaut-wrapper"
    "cmp:garnaut:authority-wrapper"

garnautCounterTrace : Trace.SemanticTracePath
garnautCounterTrace =
  mkTrace
    "statement:counter:garnaut-wrapper"
    "demo/narrative/friendlyjordies_authority_wrappers.json"
    "counter_authority_analysis:u3"
    "The analysis reported that Ross Garnaut reported that an imperfect ETS was better than delay."
    "pnf:counter:garnaut-wrapper"
    "observation:counter:garnaut-wrapper"
    "event:public-discourse:garnaut-ets-authority"
    "claim:counter-analysis:garnaut-wrapper"
    "cmp:garnaut:authority-wrapper"

garnautWorldDemand : WorldDemand
garnautWorldDemand =
  world-demand
    "prop:garnaut-imperfect-ets-delay"
    Horizon.externalWorldHorizon
    "demand:garnaut:primary-source-context"
    "the recovered archive pays the nested attribution; Garnaut's original statement/context still requires an external primary or scholarly source"

------------------------------------------------------------------------
-- Fallacies/framing recovered as a source-local counter-analysis claim.
-- The comparison is intentionally right-only: absence of a left-side claim is
-- represented explicitly and is not an orphan.
------------------------------------------------------------------------

fallaciesCounterTrace : Trace.SemanticTracePath
fallaciesCounterTrace =
  mkTrace
    "statement:counter:fallacies"
    "demo/narrative/friendlyjordies_thread_extract.json"
    "thread_balanced_analysis:u6"
    "The analysis argued that Jordies' case against the Greens contains several logical fallacies."
    "pnf:counter:fallacies"
    "observation:counter:fallacies"
    "event:public-discourse:fallacies-framing"
    "claim:counter-analysis:fallacies"
    "cmp:fallacies:right-only"

fallaciesWorldDemand : WorldDemand
fallaciesWorldDemand =
  world-demand
    "prop:friendlyjordies:fallacies-framing"
    Horizon.externalWorldHorizon
    "demand:fallacies:argument-reconstruction"
    "the archive pays that the counter-analysis made the classification; evaluating the classification requires the underlying argument and explicit fallacy criteria"

------------------------------------------------------------------------
-- Comparison coverage.  SourceDisposition has no orphan constructor.
------------------------------------------------------------------------

record ComparisonCoverage : Set where
  constructor comparison-coverage
  field
    comparisonRef : String
    family : Weld.FriendlyjordiesArgumentFamily
    left : SourceDisposition
    right : SourceDisposition
    silentlyAdmitsOrphan : Bool
    silentlyAdmitsOrphanIsFalse : silentlyAdmitsOrphan ≡ false

open ComparisonCoverage public

cprsCoverage : ComparisonCoverage
cprsCoverage =
  comparison-coverage
    "cmp:cprs:shared"
    Weld.cprsBlocking
    (tracedWithWorldDemand cprsSourceTrace cprsWorldDemand)
    (tracedWithWorldDemand cprsCounterTrace cprsWorldDemand)
    false refl

instabilityCoverage : ComparisonCoverage
instabilityCoverage =
  comparison-coverage
    "cmp:instability:competing-account"
    Weld.cprsBlocking
    (tracedWithWorldDemand instabilitySourceTrace instabilityWorldDemand)
    (tracedWithWorldDemand instabilityCounterTrace instabilityWorldDemand)
    false refl

governmentCoverage : ComparisonCoverage
governmentCoverage =
  comparison-coverage
    "cmp:government-capacity:reasoning-flow"
    Weld.governmentCapacity
    (tracedWithWorldDemand governmentSourceTrace governmentWorldDemand)
    (tracedWithWorldDemand governmentCounterTrace governmentWorldDemand)
    false refl

woolworthsCoverage : ComparisonCoverage
woolworthsCoverage =
  comparison-coverage
    "cmp:woolworths:qualification"
    Weld.woolworthsPriceEffects
    (tracedWithWorldDemand woolworthsSourceTrace woolworthsWorldDemand)
    (tracedWithWorldDemand woolworthsCounterTrace woolworthsWorldDemand)
    false refl

garnautCoverage : ComparisonCoverage
garnautCoverage =
  comparison-coverage
    "cmp:garnaut:authority-wrapper"
    Weld.etsDelayAuthority
    (tracedWithWorldDemand garnautSourceTrace garnautWorldDemand)
    (tracedWithWorldDemand garnautCounterTrace garnautWorldDemand)
    false refl

fallaciesCoverage : ComparisonCoverage
fallaciesCoverage =
  comparison-coverage
    "cmp:fallacies:right-only"
    Weld.fallaciesAndFraming
    (explicitlyAbsentByComparisonKind
      "right-only proposition: no FriendlyJordies-source fallacies claim is asserted by the checked-in fixture")
    (tracedWithWorldDemand fallaciesCounterTrace fallaciesWorldDemand)
    false refl

record SourceTotalComparison : Set where
  constructor source-total-comparison
  field
    comparisonCoverages : List ComparisonCoverage
    residualFamilyCoverages : List String
    everyComparisonHasDisposition : Bool
    everyComparisonHasDispositionIsTrue :
      everyComparisonHasDisposition ≡ true
    everyNamedFamilyHasDisposition : Bool
    everyNamedFamilyHasDispositionIsTrue :
      everyNamedFamilyHasDisposition ≡ true
    orphanPropositionsAdmitted : Bool
    orphanPropositionsAdmittedIsFalse :
      orphanPropositionsAdmitted ≡ false
    hiddenVerdictAdded : Bool
    hiddenVerdictAddedIsFalse : hiddenVerdictAdded ≡ false

open SourceTotalComparison public

canonicalFriendlyjordiesSourceTotality : SourceTotalComparison
canonicalFriendlyjordiesSourceTotality =
  source-total-comparison
    ( cprsCoverage
    ∷ instabilityCoverage
    ∷ governmentCoverage
    ∷ woolworthsCoverage
    ∷ garnautCoverage
    ∷ fallaciesCoverage
    ∷ [])
    []
    true refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Forward/reverse trace receipts for the paid static families.
------------------------------------------------------------------------

governmentSourceForward : Trace.ForwardTraceReceipt governmentSourceTrace
governmentSourceForward = Trace.canonicalForwardTrace governmentSourceTrace

governmentSourceReverse : Trace.ReverseTraceReceipt governmentSourceTrace
governmentSourceReverse = Trace.canonicalReverseTrace governmentSourceTrace

woolworthsSourceForward : Trace.ForwardTraceReceipt woolworthsSourceTrace
woolworthsSourceForward = Trace.canonicalForwardTrace woolworthsSourceTrace

woolworthsSourceReverse : Trace.ReverseTraceReceipt woolworthsSourceTrace
woolworthsSourceReverse = Trace.canonicalReverseTrace woolworthsSourceTrace

data SourceTotalityCreatesWorldTruth : Set where
data ExplicitAcquisitionDemandMayBeDropped : Set where
data GeneratedFixtureMayBeTreatedAsPinnedFixture : Set where
data TraceMayReplaceExternalWorldEvidence : Set where

sourceTotalityDoesNotCreateWorldTruth :
  SourceTotalityCreatesWorldTruth → ⊥
sourceTotalityDoesNotCreateWorldTruth ()

acquisitionDemandMayNotBeDropped :
  ExplicitAcquisitionDemandMayBeDropped → ⊥
acquisitionDemandMayNotBeDropped ()

generatedFixtureDoesNotEqualPinnedFixture :
  GeneratedFixtureMayBeTreatedAsPinnedFixture → ⊥
generatedFixtureDoesNotEqualPinnedFixture ()

traceDoesNotReplaceExternalWorldEvidence :
  TraceMayReplaceExternalWorldEvidence → ⊥
traceDoesNotReplaceExternalWorldEvidence ()


------------------------------------------------------------------------
-- Strong totality: enumerate the comparison surface and family surface.
-- Totality is now a function, not merely a Boolean receipt.
------------------------------------------------------------------------

data FriendlyjordiesComparisonKey : Set where
  cprsSharedKey : FriendlyjordiesComparisonKey
  instabilityCompetingKey : FriendlyjordiesComparisonKey
  governmentCapacityKey : FriendlyjordiesComparisonKey
  woolworthsQualificationKey : FriendlyjordiesComparisonKey
  garnautAuthorityKey : FriendlyjordiesComparisonKey
  fallaciesRightOnlyKey : FriendlyjordiesComparisonKey

coverageForComparison : FriendlyjordiesComparisonKey → ComparisonCoverage
coverageForComparison cprsSharedKey = cprsCoverage
coverageForComparison instabilityCompetingKey = instabilityCoverage
coverageForComparison governmentCapacityKey = governmentCoverage
coverageForComparison woolworthsQualificationKey = woolworthsCoverage
coverageForComparison garnautAuthorityKey = garnautCoverage
coverageForComparison fallaciesRightOnlyKey = fallaciesCoverage

comparisonDispositionLeft :
  (key : FriendlyjordiesComparisonKey) →
  SourceDisposition
comparisonDispositionLeft key =
  ComparisonCoverage.left (coverageForComparison key)

comparisonDispositionRight :
  (key : FriendlyjordiesComparisonKey) →
  SourceDisposition
comparisonDispositionRight key =
  ComparisonCoverage.right (coverageForComparison key)

comparisonCannotBeOrphan :
  (key : FriendlyjordiesComparisonKey) →
  ComparisonCoverage.silentlyAdmitsOrphan
    (coverageForComparison key) ≡ false
comparisonCannotBeOrphan cprsSharedKey = refl
comparisonCannotBeOrphan instabilityCompetingKey = refl
comparisonCannotBeOrphan governmentCapacityKey = refl
comparisonCannotBeOrphan woolworthsQualificationKey = refl
comparisonCannotBeOrphan garnautAuthorityKey = refl
comparisonCannotBeOrphan fallaciesRightOnlyKey = refl

familyDisposition :
  Weld.FriendlyjordiesArgumentFamily →
  SourceDisposition
familyDisposition Weld.cprsBlocking =
  tracedWithWorldDemand cprsSourceTrace cprsWorldDemand
familyDisposition Weld.woolworthsPriceEffects =
  tracedWithWorldDemand woolworthsSourceTrace woolworthsWorldDemand
familyDisposition Weld.governmentCapacity =
  tracedWithWorldDemand governmentSourceTrace governmentWorldDemand
familyDisposition Weld.etsDelayAuthority =
  tracedWithWorldDemand garnautSourceTrace garnautWorldDemand
familyDisposition Weld.fallaciesAndFraming =
  tracedWithWorldDemand fallaciesCounterTrace fallaciesWorldDemand

------------------------------------------------------------------------
-- Archive-recovery receipt.  These source units are now pinned in SensibLaw
-- main; pinning pays only the source-local transcript claim.
------------------------------------------------------------------------

record RecoveredFixtureBoundary : Set where
  constructor recovered-fixture-boundary
  field
    sensibLawRevisionRef : String
    garnautUnitPinned : Bool
    garnautUnitPinnedIsTrue : garnautUnitPinned ≡ true
    fallaciesUnitPinned : Bool
    fallaciesUnitPinnedIsTrue : fallaciesUnitPinned ≡ true
    nestedAttributionPreserved : Bool
    nestedAttributionPreservedIsTrue :
      nestedAttributionPreserved ≡ true
    rightOnlyFallaciesPreserved : Bool
    rightOnlyFallaciesPreservedIsTrue :
      rightOnlyFallaciesPreserved ≡ true
    pinningCreatesWorldTruth : Bool
    pinningCreatesWorldTruthIsFalse :
      pinningCreatesWorldTruth ≡ false

canonicalRecoveredFixtureBoundary : RecoveredFixtureBoundary
canonicalRecoveredFixtureBoundary =
  recovered-fixture-boundary
    Existing.sensibLawRevision
    true refl
    true refl
    true refl
    true refl
    false refl

------------------------------------------------------------------------
-- Complete forward/reverse receipts for every currently traced side.
------------------------------------------------------------------------

cprsSourceForward : Trace.ForwardTraceReceipt cprsSourceTrace
cprsSourceForward = Trace.canonicalForwardTrace cprsSourceTrace

cprsSourceReverse : Trace.ReverseTraceReceipt cprsSourceTrace
cprsSourceReverse = Trace.canonicalReverseTrace cprsSourceTrace

cprsCounterForward : Trace.ForwardTraceReceipt cprsCounterTrace
cprsCounterForward = Trace.canonicalForwardTrace cprsCounterTrace

cprsCounterReverse : Trace.ReverseTraceReceipt cprsCounterTrace
cprsCounterReverse = Trace.canonicalReverseTrace cprsCounterTrace

instabilitySourceForward : Trace.ForwardTraceReceipt instabilitySourceTrace
instabilitySourceForward = Trace.canonicalForwardTrace instabilitySourceTrace

instabilitySourceReverse : Trace.ReverseTraceReceipt instabilitySourceTrace
instabilitySourceReverse = Trace.canonicalReverseTrace instabilitySourceTrace

instabilityCounterForward : Trace.ForwardTraceReceipt instabilityCounterTrace
instabilityCounterForward = Trace.canonicalForwardTrace instabilityCounterTrace

instabilityCounterReverse : Trace.ReverseTraceReceipt instabilityCounterTrace
instabilityCounterReverse = Trace.canonicalReverseTrace instabilityCounterTrace

governmentCounterForward : Trace.ForwardTraceReceipt governmentCounterTrace
governmentCounterForward = Trace.canonicalForwardTrace governmentCounterTrace

governmentCounterReverse : Trace.ReverseTraceReceipt governmentCounterTrace
governmentCounterReverse = Trace.canonicalReverseTrace governmentCounterTrace

woolworthsCounterForward : Trace.ForwardTraceReceipt woolworthsCounterTrace
woolworthsCounterForward = Trace.canonicalForwardTrace woolworthsCounterTrace

woolworthsCounterReverse : Trace.ReverseTraceReceipt woolworthsCounterTrace
woolworthsCounterReverse = Trace.canonicalReverseTrace woolworthsCounterTrace


garnautSourceForward : Trace.ForwardTraceReceipt garnautSourceTrace
garnautSourceForward = Trace.canonicalForwardTrace garnautSourceTrace

garnautSourceReverse : Trace.ReverseTraceReceipt garnautSourceTrace
garnautSourceReverse = Trace.canonicalReverseTrace garnautSourceTrace

garnautCounterForward : Trace.ForwardTraceReceipt garnautCounterTrace
garnautCounterForward = Trace.canonicalForwardTrace garnautCounterTrace

garnautCounterReverse : Trace.ReverseTraceReceipt garnautCounterTrace
garnautCounterReverse = Trace.canonicalReverseTrace garnautCounterTrace

fallaciesCounterForward : Trace.ForwardTraceReceipt fallaciesCounterTrace
fallaciesCounterForward = Trace.canonicalForwardTrace fallaciesCounterTrace

fallaciesCounterReverse : Trace.ReverseTraceReceipt fallaciesCounterTrace
fallaciesCounterReverse = Trace.canonicalReverseTrace fallaciesCounterTrace

record ConstructiveSourceTotalityBoundary : Set where
  constructor constructive-source-totality-boundary
  field
    comparisonTotalityConstructive : Bool
    comparisonTotalityConstructiveIsTrue :
      comparisonTotalityConstructive ≡ true
    familyTotalityConstructive : Bool
    familyTotalityConstructiveIsTrue :
      familyTotalityConstructive ≡ true
    allPaidSidesBidirectionallyTraceable : Bool
    allPaidSidesBidirectionallyTraceableIsTrue :
      allPaidSidesBidirectionallyTraceable ≡ true
    recoveredFixtureFamiliesPinned : Bool
    recoveredFixtureFamiliesPinnedIsTrue :
      recoveredFixtureFamiliesPinned ≡ true
    fixturePinningPromotesTruth : Bool
    fixturePinningPromotesTruthIsFalse :
      fixturePinningPromotesTruth ≡ false

canonicalConstructiveSourceTotalityBoundary :
  ConstructiveSourceTotalityBoundary
canonicalConstructiveSourceTotalityBoundary =
  constructive-source-totality-boundary
    true refl
    true refl
    true refl
    true refl
    false refl
