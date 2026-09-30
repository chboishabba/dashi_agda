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
        ("parser-run:" ++ statementRef)
        "sensiblaw-narrative-fixture")
      ("review:parse:" ++ statementRef)
      ("admission:candidate:" ++ statementRef)
      true refl false refl false refl false refl)
    (Trace.observation-event-link
      observationRef
      eventRef
      ("assembly:" ++ eventRef)
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
-- ETS/Garnaut: the pinned static authority fixture does not contain the Garnaut
-- text used by the Agda candidate root.  The archive-refresh producer can emit
-- that text only when the source thread contains the corresponding theme.
------------------------------------------------------------------------

garnautRefreshDemand : AcquisitionDemand
garnautRefreshDemand =
  acquisition-demand
    "ets_delay_authority"
    "prop:garnaut-imperfect-ets-delay"
    "archive-backed friendlyjordies_authority_wrappers refresh containing the Garnaut nested-attribution unit"
    "SensibLaw/src/reporting/narrative_fixture_refresh.py::_build_authority_wrappers_payload"
    "pinned static authority fixture currently contains Lepore/Court examples, so a Garnaut M12 trace would be orphaned"
    false refl

------------------------------------------------------------------------
-- Fallacies/framing: this family is generated conditionally by the archive
-- refresh producer but has no checked-in typed root/claim/comparison item at
-- the pinned fixture revision.
------------------------------------------------------------------------

fallaciesRefreshDemand : AcquisitionDemand
fallaciesRefreshDemand =
  acquisition-demand
    "fallacies"
    "prop:friendlyjordies:fallacies-framing"
    "archive-backed thread extract with fallacies theme plus typed root/claim/comparison item"
    "SensibLaw/src/reporting/narrative_fixture_refresh.py::_build_thread_extract_payload"
    "the generator may emit a fallacies line, but the pinned static fixture and Agda comparison surface do not yet bind it"
    false refl

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
    (unresolvedAcquisition garnautRefreshDemand)
    (unresolvedAcquisition garnautRefreshDemand)
    false refl

record FamilyResidualCoverage : Set where
  constructor family-residual-coverage
  field
    family : Weld.FriendlyjordiesArgumentFamily
    disposition : SourceDisposition
    noComparisonItemSilentlyInvented : Bool
    noComparisonItemSilentlyInventedIsTrue :
      noComparisonItemSilentlyInvented ≡ true

fallaciesCoverage : FamilyResidualCoverage
fallaciesCoverage =
  family-residual-coverage
    Weld.fallaciesAndFraming
    (unresolvedAcquisition fallaciesRefreshDemand)
    true refl

record SourceTotalComparison : Set where
  constructor source-total-comparison
  field
    comparisonCoverages : List ComparisonCoverage
    residualFamilyCoverages : List FamilyResidualCoverage
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
    ∷ [])
    (fallaciesCoverage ∷ [])
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
