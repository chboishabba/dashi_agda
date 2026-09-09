module DASHI.Wikimedia.SensibLawNatClimateSLRFixtureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.SourceProvenanceExact as Source
import DASHI.Wikimedia.SensibLawSourceUnitReviewHandoffExact as Handoff
import DASHI.Wikimedia.SensibLawNatClimateReviewHandoffExact as Climate
import DASHI.Wikimedia.SLRWikimediaHandoffABIExact as SLR

------------------------------------------------------------------------
-- CONCRETE REVISION-LOCKED NAT SOURCE-UNIT / REVIEW / SLR FIXTURE
------------------------------------------------------------------------

natSandboxQid : Id.ItemId
natSandboxQid = Id.itemId "Q10884"

natSourceReceipt : Source.SourceReceipt
natSourceReceipt =
  Source.sourceReceipt
    Source.dashiReconstructionLayer
    "chboishabba/SensibLaw tests/fixtures/wikidata/wiki_revision_nat_wdu_sandbox_p5991_p14143_20260401.json"
    "sl.source_unit.v1:unit:wikidata_user_sandbox:nat_wdu:p5991_p14143:2026-04-01"
    "SensibLaw/main d25cddf73540bdbb313777bbf566280f4e34313b"
    "fixture-content-hash-not-pinned-in-this-agda-owner"
    "typed DASHI reconstruction of a revision-locked SensibLaw source-unit fixture"

natRevision : Handoff.SourceRevision
natRevision =
  Handoff.source-revision
    (Handoff.textualRevisionId "provided_snapshot_2026-04-01")
    "2026-04-01T00:00:00+10:00"
    Handoff.wikiRevision

natOrigin : Handoff.SourceOrigin
natOrigin =
  Handoff.source-origin
    Handoff.wikiSource
    (Handoff.presentText "https://www.wikidata.org/wiki/User:Nat_(WDU)/Sandbox/Fossil_fuel_industries/Migrate_from_carbon_footprint_to_GHG_emissions")
    (Handoff.presentText "User:Nat (WDU)/Sandbox/Fossil fuel industries/Migrate from carbon footprint to GHG emissions")

natContent : Handoff.SourceContent
natContent =
  Handoff.source-content
    Handoff.textFormat
    "Since the cretion of P14143 I have to migrate most of the P5991 statements with their references and qualifiers to use this new property (This has been discussed in the property proposal and documented in Wikiproject climate change).\n\ntasks\ndone\n\n- is there any documentation or protocol on how to make this kind of migrations? Asked Jan and Wikiproject onthology\n- get the units wip query\n\nto do\n\n- evaluate migration for 22514 statements on items that are instances of business (Q4830453), 7138 instances of enterprise (Q6881511) and 7913 instances of public company (Q891723)\n- capture all \"extra\" qualifiers wip: for these 3 \"instance of\" we are capturing all the qualifiers we can find: determination method or standard (P459), object of statement has role (P3831), point in time (P585), start time (P580), end time (P582), applies to part (P518), reason for preferred rank (P7452)\n- check if there really are not extra qualifiers within the items that are instances of instance of empresa, negocio, banco, biopharmaceutical company, compañía, empresa de capital abierto, institución financiera)\n- capture the references. the first set (things that are instance of empresa, negocio, banco, biopharmaceutical company, compañía, empresa de capital abierto, institución financiera) we found only the following reference properties: reference URL (P854), archive URL (P1065), retrieved (P813), title (P1476), archive date (P2960)\n- is it necesary to add the rank?\n- evaluate migration for all other reconciled \"instance of\"\n- look for any unexpected qualifiers\n- capture references\n- evaluate migrations of statements cuyo determination method no es GHG protocol (otro determination method o no tiene el determination method)\n- evaluate migration for 1395 statements cuyo sujeto no tiene un \"instance of\"\n- look for any unexpected qualifiers\n- capture references\n- evaluar migración para 142 declaraciones cuyo sujeto tiene un instance of que no pudo ser reconciliado\n- look for any unexpected qualifiers\n- capture references\n\nqueries\n\n- https://w.wiki/KR5d all carbon footprint statements. 57835 results on march 27th"

natAnchors : List Handoff.SourceAnchor
natAnchors =
  Handoff.source-anchor "goal" 0 257 (Handoff.presentText "migration_goal")
  ∷ Handoff.source-anchor "cohort_business_family" 408 585 (Handoff.presentText "cohort_business_family")
  ∷ Handoff.source-anchor "qualifier_family" 588 847 (Handoff.presentText "expected_qualifier_family")
  ∷ Handoff.source-anchor "reference_family" 1047 1289 (Handoff.presentText "expected_reference_family")
  ∷ Handoff.source-anchor "query_anchor" 1655 1737 (Handoff.presentText "query_anchor")
  ∷ []

natSourceUnit : Handoff.SensibLawSourceUnit
natSourceUnit =
  Handoff.sensiblaw-source-unit
    "wikidata_user_sandbox:nat_wdu:p5991_p14143:provided_snapshot:2026-04-01"
    natSandboxQid
    "unit:wikidata_user_sandbox:nat_wdu:p5991_p14143:2026-04-01"
    natRevision
    natOrigin
    natContent
    natAnchors
    "metadata: migration P5991 -> P14143; proposal_scope=migration_cohort_and_constraint_surface"
    natSourceReceipt
    "SensibLaw sl.source_unit.v1 fixture; revision-locked source input only"

natSplitContext : Handoff.SplitReviewContext
natSplitContext =
  Handoff.split-review-context
    "nat:p5991-p14143:split-heavy-review"
    "P5991-source-slot"
    []
    ("scope" ∷ "time" ∷ "determination-method" ∷ "reference-transfer" ∷ [])
    Handoff.reviewOnlyTypedHold
    Handoff.splitRequired
    "preserve source bundle; reviewer resolves decomposition before any export"

natParsedSignals : Handoff.ParsedPageSignals
natParsedSignals =
  Handoff.parsed-page-signals
    ("https://w.wiki/KR5d" ∷ [])
    []
    ("migration equivalence remains unresolved per statement" ∷
     "reference transfer must be reviewed" ∷ [])
    Climate.expectedNatQualifiers
    Climate.expectedNatReferences
    "bounded deterministic parsing of the pinned Nat source unit"

natFollowReceipts : List Handoff.FollowReceipt
natFollowReceipts =
  Handoff.follow-receipt
    "https://w.wiki/KR5d"
    "bounded query-link follow candidate from the Nat source-unit query anchor"
    "candidate-discovery surface only"
    "query results do not determine migration safety or source authority"
  ∷ []

natReviewerView : Handoff.ReviewerView
natReviewerView =
  Handoff.reviewer-view
    ("split axes" ∷ "qualifier preservation" ∷ "reference transfer" ∷ [])
    ("semantic equivalence unresolved" ∷ "no checked-safe subset in current bounded state" ∷ [])
    "review split-heavy rows; do not widen blind direct-rewrite passes"

natReviewPacket : Handoff.SensibLawReviewPacket
natReviewPacket =
  Handoff.sensiblaw-review-packet
    "nat:p5991-p14143:review-packet:agda-fixture"
    natSourceUnit
    natSplitContext
    natParsedSignals
    natFollowReceipts
    natReviewerView
    true refl
    true refl
    "Agda formalisation of the SensibLaw Nat reviewer-packet handoff contract"

natSlrHandoff : Handoff.RuntimeHandoffReceipt
natSlrHandoff = SLR.handoffToSlr natReviewPacket

natSlrPreservesSourceUnit :
  Handoff.sourceUnitReference natSlrHandoff
  ≡ "unit:wikidata_user_sandbox:nat_wdu:p5991_p14143:2026-04-01"
natSlrPreservesSourceUnit = refl

natSlrDoesNotOwnSourceAuthority :
  Handoff.runtimeOwnsSourceAuthority natSlrHandoff ≡ false
natSlrDoesNotOwnSourceAuthority = refl

natPacketStaysSplitRequired :
  Handoff.disposition (Handoff.splitContext natReviewPacket) ≡ Handoff.splitRequired
natPacketStaysSplitRequired = refl

data ExpectedReferenceMeansVerifiedReference : Set where
data ReviewPacketMeansMigrationApproved : Set where

expectedReferenceDoesNotMeanVerified : ExpectedReferenceMeansVerifiedReference → ⊥
expectedReferenceDoesNotMeanVerified ()

reviewPacketDoesNotMeanMigrationApproved : ReviewPacketMeansMigrationApproved → ⊥
reviewPacketDoesNotMeanMigrationApproved ()
