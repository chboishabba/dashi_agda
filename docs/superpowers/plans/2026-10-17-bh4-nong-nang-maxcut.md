# BH4 / NONG-NANG Nitrogen-Oxide Max-Cut Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Turn the external-biology ontology in PR #1159 into a concrete BH4/NOS system-state model, populate a reproducible protein panel, and cross-pollinate it with the existing Nongin refinement machinery while keeping nitric oxide (NO) distinct from nitrous oxide (N2O / “nangs”).

**Architecture:** Add a BH4 pool/demand/flux owner, an NOS-coupling and nitrogen-oxide-species owner, a Nongin coarse/fine chemical refinement bridge, and a bounded N2O metabolic-evidence lane. Extend the existing acquisition script so the full Kitzerow/BH4 protein panel can be acquired as exact certificates. Finish with a max-cut bridge that records which system edges are paid by database/reaction evidence and which remain compartment/flux/causal residuals.

**Tech Stack:** Agda; Python 3 standard library; UniProt REST certificates; existing `DASHI.Core.NonginOnePointOneArmyRefinementExact`, `DASHI.Biology.ExternalBiology*`, and PR #1159 Kitzerow evidence owners.

**Spec:** Conversation-approved design immediately preceding this plan: shared BH4 carrier/state, separate chemistry/cofactor/mechanism claims, typed NOS coupling, protein graph population, N2O/NO anti-conflation via Nongin refinement, and explicit mechanistic residuals.

## Global Constraints

- Reuse existing repo-wide provenance and consumer-admission owners; do not create a second authority ontology.
- `NO` and `N2O` must never be definitionally identified.
- User genealogy may record `nong = nang = nitrous oxide`, but that lexical/genealogical alias must not become a biochemical identity with nitric oxide.
- UniProt/Rhea/PDB/AlphaFold annotations may pay identity/reaction/geometry obligations only at their admitted consumer grade.
- Whole-model, disease-mechanism, clinical, priority, contact, and attribution promotion remain blocked unless separately paid.
- Acquisition outputs must remain reproducible and byte-hashed.

## Review Focus

- Coarse “nitrogen oxide” observations must fail for a consumer that distinguishes NO from N2O.
- NOS uncoupling must not be inferred from NOS protein presence alone.
- N2O cobalamin/methionine-synthase evidence must not be promoted into a BH4/NOS mechanism without a separate bridge.
- A complete panel acquisition must tolerate one accession failing without silently treating the whole panel as acquired.
- Node/reaction support must remain insufficient for the complete Kitzerow causal graph.

---

### Task 1: Regression surface first

**Files:**
- Create: `DASHI/Biology/BH4NongNangMaxCutRegression.agda`

**Interfaces:**
- Consumes: planned owners from Tasks 2–5.
- Produces: compile-time regression witnesses for chemical distinction, Nongin non-descent, coupling boundaries, and whole-graph non-promotion.

- [ ] Write imports and theorem signatures before production modules exist.
- [ ] Verify this is intentionally RED until those modules are added.

### Task 2: BH4 state / flux owner

**Files:**
- Create: `DASHI/Biology/BH4SystemStateExact.agda`

**Interfaces:**
- Consumes: `DASHI.Core.Prelude`, external-biology protein references.
- Produces: `BH4PoolState`, `EnzymeDemand`, `BH4SystemState`, `FluxBalanceWitness`, and residual boundaries.

- [ ] Represent BH4/BH2, compartment, synthesis, regeneration, oxidation, demand, storage change, and a Nat-valued balance equation.
- [ ] Prove that isolated protein/reaction annotations do not instantiate a whole-system flux witness.

### Task 3: NOS coupling and N2O evidence lane

**Files:**
- Create: `DASHI/Biology/NitrogenOxideSpeciesCouplingExact.agda`
- Create: `DASHI/Biology/NitrousOxideMetabolismEvidenceExact.agda`

**Interfaces:**
- Produces: distinct `nitricOxide`, `nitrousOxide`, `superoxide`, `peroxynitrite`; typed `NOSCouplingState`; bounded coupling-transition witnesses; N2O cobalamin/methionine-synthase evidence boundary.

- [ ] Make `nitricOxide ≡ nitrousOxide -> ⊥` explicit.
- [ ] Require a measured/declared biochemical-state witness for coupling-state promotion.
- [ ] Record N2O → cobalamin oxidation / methionine-synthase inhibition as a separate bounded lane.

### Task 4: Nongin chemical-refinement cross-pollination

**Files:**
- Create: `DASHI/Biology/NonginNangNitrogenOxideRefinementExact.agda`

**Interfaces:**
- Consumes: `NonginOnePointOneArmyRefinementExact`, Task 3 species.
- Produces: coarse `nitrogenOxide` base + NO/N2O frame refinement, frame-sensitive biochemical consumer, non-descent theorem, and genealogy boundary for `nong = nang = N2O`.

- [ ] Instantiate `OnePointOneCarrier` with a coarse nitrogen-oxide base and chemical-species frame.
- [ ] Prove the coarse carrier cannot serve the fine chemical consumer.
- [ ] Keep the lexical/genealogy alias non-authoritative for biochemical identity.

### Task 5: Protein panel acquisition and max-cut bridge

**Files:**
- Modify: `scripts/acquire_uniprot_bio_certificate.py`
- Create: `DASHI/Biology/KitzerowBH4SystemNongNangMaxCutExact.agda`
- Modify: `DASHI/Biology/ExternalBiologyEverything.agda`
- Modify: `DASHI/Biology/KitzerowBH4EvidenceEverything.agda`
- Modify: `scripts/check_kitzerow_bh4_priority.py`

**Interfaces:**
- Produces: named acquisition panel for GCH1/GCHFR/PTS/SPR/PCBD1/QDPR/NOS1/NOS2/NOS3/PAH/TH/TPH1/TPH2/AGMO/TSC2/MTOR; edge-payment matrix; explicit compartment/flux/causal residuals.

- [ ] Add batch/panel mode without weakening single-accession certificate behavior.
- [ ] Map isolated biochemical support to existing `RelationTarget` values while keeping whole-model confirmation false.
- [ ] Import all new owners through focused roots and extend regression token checks.
- [ ] Re-run syntax/compile/regression commands where the environment permits and report exact residual verification gaps.
