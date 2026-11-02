# Kitzerow BH4 pathway: ITIR/SensibLaw/Wikidata repair user-story max-cut

Date: 2026-11-02. Scope: source-level consumer adapter on DASHI Agda #1454.
Status: **candidate-only, no live SLR/ITIR/GO-CAM/SBML or Dioxus execution**.

## Existing owners read before extending

- ITIR-suite docs/user_stories.md:
  ITIR-US-01 (context), ITIR-US-02 (known then/later/unknown), ITIR-US-10
  (text-first proof inspection), ITIR-US-17 (revision-locked wiki/source follow),
  WIKI-US-01/SL-US-38 (strict review packets), WIKI-US-02/SL-US-39 (tool profiles),
  WIKI-US-03/SL-US-40 (disjointness and typed repair diagnostics),
  WIKI-US-04/SL-US-41 (source-class separation and evidence reconciliation).
- ITIR-suite docs/planning/user_story_alignment_and_reprioritization_20260402.md
  (later correction: Dioxus owns new GUI; Svelte remains historical fixture).
- ITIR-suite docs/planning/progressive_proof_explanation_workbench_20260915.md:
  Orient -> Project -> Why? -> Source -> Meaning -> Follow -> Next unresolved;
  exact-source reopening first, world graph opt-in.
- DASHI/Cognition/PNF/WikidataRepairProposal.agda:
  split/underspecify/repair/hold operations are proposal-only.
- DASHI/Ontology/WikidataRepairReopeningExact.agda:
  source -> transcription -> alignment -> diagnostic -> candidate remains
  reopenable; the illustrative bit carrier is not a proof of full biology source parity.
- DASHI/Ontology/WikidataConsumerResidualRefinementExact.agda:
  source, alignment, target-graph, and missing-evidence failures are different
  consumer-relevant origins; a Boolean pass/fail loses distinction.
- DASHI/Wikimedia/WikidataOntologyDiagnosticS29BridgeExact.agda:
  full statement vs truthy rank, checker source vs executed checker and
  modeled repair vs actual public edit remain separate.
- DASHI/Wikimedia/WikidataPNFPredicateBridgeExact.agda:
  Wikidata statement property -> PNF role requires separate reviewed reading;
  property ID never creates causal semantics.
- SensibLaw docs/wikidata/README.md, docs/ontology_diagnostic_taxonomy_wikidata_v0_1.md,
  docs/wikidata_ontology_issue_review_20260306.md: versioned review bundles,
  wrong-order/SCC/metaclass/qualifier/negative constraint diagnostics and
  review-only ChangeReviewPacket; no automatic rewriting of source.
- Related unmerged lanes: DASHI #1143 (Rosario, OCTF, SSSOM crosswalk);
  DASHI #1447, ITIR #70, SLR #76 (Roszkowski source/consensus/role/closure
  governance). Reuse after exact-head reconciliation, not by copying their
  private or unverified state into Kitzerow.

## Executed source-writing cut: no new ontology or storage engine

1. Existing BH4 output (source-attributed Rhea/ChEBI/UniProt + xPollenation,
   candidate Kitzerow claims, 29x12 matrix) is the input authority.
2. scripts/build_bh4_pathway_review.py emits deterministic
   dashi.bh4-pathway-review-worklist.v1 with typed diagnostic origins, exact
   source/revision/receipt handles, a required witness, and an appropriate next
   source-inspection action. No source body or source parser is fabricated.
3. Agda owner BH4PathwayReviewInteropExact imports the existing Wikidata
   candidate repair, source reopening, consumer-residual, S29 diagnostic and
   reading-trail types. Its typed obligations and closed empty promotion
   permissions are *source-written*. They are not Agda kernel-verified on
   this PR head.
4. The existing Phase-4 runner writes a review worklist in addition to the
   canonical ontology JSON/JSON-LD, never the user's SLR PostgreSQL DB.
5. A focused deterministic fixture checks held candidate status, source refs,
   ontology-crosswalk uncertainty, flux nulls, nonfinite chemistry, no live
   Wikidata writes and private-source export suppression.

## Review worklist shape and status

Every worklist entry has an immutable ID derived from owner/diagnostic/intent;
kind; originating typed coordinate; source reopening refs; diagnostic origin;
required exact witness; next action; role of source; and held, nonpromoting
disposition. A source supplied by a caller must include source ID, revision,
content digest, locator, and visibility. The exporter does **not** independently
authenticate that receipt. Public locators may be included; restricted/internal
locators are represented only by opaque source handles in export.

All entries stay active-missing-evidence; the worklist cannot auto-complete
payments. It deliberately does not construct S29 IDs or attest to PostgreSQL
review transactions. If a downstream consumer receives a packet, that consumer
must do its own S30 matter/actor/purpose/scope admission and source validation.

The output has a readable-first orientation summary; the complete obligations
are available under an explicit deep-inspection step. This is a **data contract**,
not a claim that the Dioxus UI already renders it.

## What is a repair candidate here?

Only a *request for review*, for example:

- An unparsed Rhea KEGG/MetaCyc annotation needs source-versioned target
  mapping. This is **not** evidence of a broken ontology.
- A Rhea-to-GO or Rhea-to-Reactome link needs typed cross-ontology
  relation (equivalent/broader/narrower/overlap/disjoint/bridge/abstain), taxon,
  isoform and context. Shared labels are not exact same-object evidence.
- A 2024 Kitzerow claim lacks its exact primary-source span/page. This is a
  source-authentication/passage-mapping obligation, not a reputational verdict.
- An apparent deficiency in exchange rates or molecular representation is
  missing *physical evidence*, not a false ontology statement.
- Inferred class/instance, inverse/parthood, P31/P279, P2738 or negative
  constraints cannot be transplanted from Wikidata to biological GO-CAM
  without independent compatible typing and a reviewed mapping proof.

The reviewer may inspect, abstain, ask for evidence, qualify or request an
external specialist. This PR never issues a Wikidata QuickStatements action,
edits a public biology ontology, promotes a claim or changes the SLR review
store.

## Corpus and product ownership

DASHI Agda: formal/golden constraints. The pre-existing biology owners retain
physical pool and open-system balances; the Wikidata owners retain PNF/reopening/
consumer residuals. No ESD surfaces are edited.

SLR: canonical source-preserving Rust/PG INGEST-1, native S29 evidence and
consumer-relative review; later physical integration should consume the
worklist only after validating source scope and mapping to existing S29 fields.

ITIR MCP: bounded read-only operation/handoff and exact artifact resolution;
no second dispatcher or semantic DB; CID proves bytes, not biological meaning.

Dioxus: production readable-first inspector. The local feature should display
a concise "what is known / unknown" panel and progressive Why/Source/Meaning/
Follow, show exact status distinction (unknown, unavailable, restricted,
abstained), and never expose source private locators in public projections.

SensibLaw Python (historical): user stories and Wikidata repair/PNF examples;
**not** a second production semantic engine. No new ITIR Svelte UI.

## Source ownership and attribution

Original synthesis: Kimberly Kitzerow, ResearchGate January 2024 DOI
10.13140/RG.2.2.23124.37761/1, August 2024 ResearchGate 383021907, July 2025
DOI 10.13140/RG.2.2.30248.89606. Original paper passage pins remain open.

Earlier BH4/NOS/AAAH/AGMO biology and the primary researchers who established
individual reactions and experiments remain independently credited. Rhea,
ChEBI, UniProt, GO, Reactome and their named curators own their database
assertions. DASHI owns this transposition, review worklist, and candidate
interpretive/repair conclusions. JMD's original finite-KB Lean theorem is not
rebranded as a DASHI Agda proof. Roszkowski's work motivates governance
architecture; new software is local, not attributed to his paper as a theorem.
No claim of copying or attribution breach follows from temporal order,
scientific overlap, or public contact assertions alone.

## Exact remaining lanes

KPO-13 (worklist source admission): take genuine source-revision bytes/spans
and official ontology releases into the existing SLR INGEST-1 reviewer;
return explicit verified/unverified/unavailable and scope distinctions.
No hardcoded source authenticity from a digest string.

KPO-14 (SLR S29): map the candidate review worklist to the existing S29
OntologyDiagnostic and reviewed source and historical context in PostgreSQL,
with scoped replay and separate same-object/causality/payment proof.
No new S29 status enum or unrelated persistence table.

KPO-15 (Dioxus): add the worklist as an opt-in read-only selected-object
inspector to the existing M10 workbench/fleet cockpit, retaining the seven
step reading trail and source-context privacy protection. No Svelte branch.

KPO-16 (Wikidata ontology repair): migrate only compatible diagnostic
classification and typed correspondence through the existing PNF/SSSOM,
OCTF and JMD owner, without conflating GO/Molecular Function, a Rhea
reaction, a Wiki QID, a causal transition or a clinical phenotype.
Reviewers retain hold/split/abstain and no-publish defaults.

KPO-17 (physical quantitative closure): require real same-object
compartment/tissue/time and enzyme/transport magnitude before admitting any
REACTION_FLUX or EXCHANGE interval. A complete ontology does not imply a
complete physical model.

KPO-18 (branch reconciliation/verifier): merge/rebase #1159 -> #1226 ->
#1454 against master, and reconcile #1227, ITIR #22, #70, SLR #76 and
DASHI #1447 only through verified matching contracts. Run exact-head Agda
and Python checks and record first-implementation, check, and merge dates
separately.

## Commands

    python3 scripts/check_bh4_pathway_ontology.py
    python3 scripts/check_bh4_pathway_review.py
    python3 scripts/check_kitzerow_bh4_priority_all.py
    scripts/run_agda29_parallel_check.sh DASHI/Biology/BH4PathwayReviewInteropExact.agda

Network, PostgreSQL, native S29, GUI and exact-head Agda checks have not been
executed by this connector workflow.
