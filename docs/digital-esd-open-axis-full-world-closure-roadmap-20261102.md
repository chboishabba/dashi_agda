# Digital-ESD full hyperfabric max-cut: open n-axis study-part / SLR / PNF closure

**Date:** 2 November 2026. **Status:** source-written interface plus runtime validator; no corpus-level review promotion. Stacked on PR #1455, whose existing source registry, proof-pilot and cross-corpus genealogy receipts remain inherited. Source-specific research authors retain all original claims. Dashi owners retain their separately attributed formal proofs. No Fleet/TOE/ESD cross-domain empirical promotion.

## 0. Research objective and coauthor scope

Alice Brown's 13 and 28 October correspondence and the working paper set **two public-facing contributions**: (1) retrospective source-bound examination of what digital/higher-education scholarship can establish under independent EfS/ESD questions, including omitted voices, context, non-factorability and the *sustainability of digital systems themselves*; (2) prospective redesign of study questions, participants, methods, decision power, lifecycle measures and temporal follow-up. The repository's **five internal ManuscriptResearchQuestion** constructors refine those two directions into ESD capacity, transformation, reflexive sustainability, participant governance and time/durability. Neither five questions nor seven principles are a complete world ontology.

The research paper is an **integrative conceptual review plus source-specific methodological demonstrations**, not a verified pooled-effect meta-analysis. A title and optional editor-enquiry abstract around 6 November 2026 are proposed team milestones; the journal's full-submission deadline is separately recorded as 30 August 2027.

## 1. Canonical owners found before implementing

| Owner | Actual capability | Integration limit |
|---|---|---|
| `Reasoning/TypedHyperfabricCore` | Arbitrary vertex/edge stalk, incidence, restriction, compatibility and obstructions | Does not itself enumerate actual scholarly study parts |
| `Core/NDimParetoHyperfabricExact` | Application-declared `Axis : Set`; arbitrary n; projection is not full dominance | Cost axis is not per-part study evidence |
| `Core/IntersectionalNonFactorability` | `FactorsThrough` and actual flattening obstruction | Generic theorem is not measured EfS interaction |
| `Education/DigitalESDSourceAuditHyperfabricExact` | Source-indexed observations/admissibility/intersections/tensions | Source-level lists can omit some study parts/axes |
| `Education/DigitalESDSourceAuditAdmissionExact` | Ten core audit axes and domain boundary | The legacy `mkSourceAuditAdmission` supplies some Boolean `true` gates; those flags do not prove a complete dynamic per-part/axis ledger |
| `Education/DigitalESDStudyParseInteropExact` | Candidate-only 19-coordinate SLR extraction overlay | The 19 coordinates are a projection, not the complete n-axis context |
| `Education/DigitalESDSLRSourceReviewBridgeExact` | Full-text hash/revision → candidate source units → reviewed observation → distinct admission | Actual reviewed packet and same-source membership still required |
| `Interop/SLRCanonicalEvidenceSubstrateExact` | SLR manifestation/revision/span/observation ABI, no claim truth promotion | Agda mirror must be checked against the current SLR production head |
| `Education/DigitalESDStudyProcessingCensusExact` | Metadata/retained/full-text/parse/review/admission stage bookkeeping | Runtime stage ledger is not a claim–observation–axis world |
| `Education/DigitalESDERICStudyExecutionExact` | 46,597 real ERIC query occurrences → 43,996 distinct metadata records | Not 43,996 full text or completed studies |
| `Education/DigitalESDResearchWorldCorpusCensusExact` | 25 source/candidate records plus 14 additional profile *occurrences* and 13 PNF audit records | Not deduplicated universe and not complete per-part source review |
| `Education/DigitalESDAllSourceSupportHyperedgesExact` | 16 candidate source genealogies, 55 original support incidences | Not 55 empirically established joints |
| `Education/DigitalESDCrossCorpusIntersectionalMemoryLensExact` | Reuses intersectional/feminist/trauma/learning donors in five candidate pairs | Attaching canonical donors does not test the particular study parts |

## 2. New exact cut on this branch

- `DigitalESDOpenAxisStudyPartWorldExact.agda` supplies an **application-declared Study, Part(study), Axis** family with exhaustive registered study/part/axis membership, total `accounting : (study)(part)(axis) → PartAxisAccounting`, six distinguishable answer states, source-specific `ReviewedPartAxisEvidence` requiring reviewed packet membership, source revision, canonical span, admission-hyperfabric observation membership and a reviewer-supplied **part/axis relevance** proof. There is deliberately **no generic constructor** for that reviewed evidence.
- A relation may involve any finite list of study parts and axes, with an independently chosen scalar or balanced-ternary **presentation**, not a fixed 3/9/27-dimensional research world. Higher-order interaction meaning, source attribution, context and conflicting evidence remain separate coordinates. Existing `TypedHyperfabric` remains the compatible global-section/obstruction owner; this branch provides only a thin research projection and does **not** force a global section.
- `DigitalESDOpenAxisGapTransportExact.agda` requires an **actual unmeasured accounting value** before recording another study as a gap-informing donor. It does not create a retroactive participant observation. It also carries explicit axis-extension witnesses, a non-vacuous arbitrary-arity relation interface, and preserves the real-ERIC metadata/PNF parsing-vs-reviewed distinction.
- `DigitalESDOpenAxisWorldRegression.agda` instantiates the interface with the attributed Taimur–Onuki source *identity* and a three-part synthetic fixture. The returned status is explicitly unmeasured, not reviewed. A fourth axis extension preserves the three old axis names. This test does **not** measure Taimur–Onuki.
- `interop_scripts/digital_esd/audit_open_axis_study_world.py` validates **every declared study part × every registered axis**, exact study revision, six status-specific receipts, arbitrary-arity relation participants, independent epistemic state, source-context provenance and graph components. The output is candidate-only and explicitly **cannot independently verify human review or provenance completeness**. `tests/test_digital_esd_open_axis_world.py` tests nonpromotion, arbitrary arity and adding an axis requiring re-accounting.

**Important distinction:** The new proof interface enforces totality **relative to a supplied study decomposition and axis registry**. It does NOT verify that this decomposition includes every actual source passage or that a reviewer chose every consumer-relevant axis. Those are the next source-specific work and corpus-review gates, and must not be replaced with a `refl` equality or synthetic fixture.

## 3. Runbook: existing ~45k acquisition / processing / SLR / PNF

**The canonical source is the persistent SLR/Postgres world; do not create a second corpus database.** Existing entrypoint: `python3 interop_scripts/digital_esd/run_world.py`, with SLR checkout at `SLR_REPO_ROOT` and artifacts at `DIGITAL_ESD_ARTIFACT_ROOT` if nonstandard. Runtime stages:

1. Exact old ERIC data receipts: **46,597 raw query occurrences, 43,996 unique metadata/abstract records**. This is a metadata universe, separate from included studies.
2. Execute the **remaining four declared databases** and reconcile search versions, exports and cross-database duplicate hypotheses. ERIC-only completeness does not pay this.
3. Obtain reviewer-authoritative title/abstract screening decisions. Candidate assessment, Pareto queue and study-family hypotheses do not create decisions. `run_screen_review_retrieve_parse_loop.py` requires actual completed-decision input.
4. For included/probable or explicitly screening-resolution cases, acquire and verify the real full-text bytes. `prepare_slr_source_units.py` validates content SHA and source identity before `run_slr_source_unit_parse.py`; `compile_study_extraction_packets.py` nominates candidates for the **existing 19 extraction coordinates**; parser output creates neither truth nor admission.
5. Build the actual source-sensitive decomposition **question, theory, method, sample/eligibility/nonparticipants, observation, measurements, claim, limitation, omissions, researcher/governance position, history/recomposition**; preserve true source revision and passage spans. Use existing PNF/study method/claim ceiling owners.
6. Declare a versioned **open n-axis registry**. For **every** study part and every declared axis, provide either reviewed evidence with source packet + same-source proof, a conditionally inferred hypothesis, contested readings, explicit unmeasured gap, inaccessibility or justified inapplicability. Unknown is not zero and N/A is not evidence of absence.
7. Audit all source-specific higher-order interactions and consumer relative projections; use `FactorsThrough` when a projection is adequate and a genuine obstruction where not. Do not force combinatorial materialisation of all axis subsets; record required sparse interactions and every unexamined consumer-relevant interaction.
8. Use cross-study gap pointers/method suggestions to direct independent evidence collection; **do not transplant** source B's observations into source A's participants. For any proposed real cross-study inference require independently reviewed population/context/method/source authority and explicit transfer conditions.
9. Reconcile historical revisions via existing Alice dependency-derived selective invalidation and candidate-world world-revision owners. Preserve original source fibres and incompatible observations.
10. Present **two actually reviewed manuscript demonstrations** (retrospective and prospective) only to the extent of real source receipts and coauthor adjudication.

### Required local worker commands (not executed in this GitHub-only authoring pass)

```bash
scripts/run_agda29_parallel_check.sh DASHI/Education/DigitalESDOpenAxisWorldRegression.agda
scripts/run_agda29_parallel_check.sh DASHI/EverythingDigitalESDReciprocalBraid.agda
python3 -m unittest tests.test_digital_esd_open_axis_world
python3 interop_scripts/digital_esd/run_world.py
# After actual reviewed study decompositions / axis-status manifest is exported:
python3 interop_scripts/digital_esd/audit_open_axis_study_world.py --input /path/to/study-world.json --output /path/to/open-axis-audit.json
```

The runtime validator is read-only, and a successful exit only establishes **structural ledger totality over explicitly declared parts/axes**. It does not certify reviewed observation membership, study decomposition completeness or full corpus world closure. No zero-flag world run or Agda compiler check has been executed here.

## 4. Exact max-cut obligations (do not mark paid by import count)

| Gate | Predicate / obligation | Status |
|---|---|---|
| NX00 | Combined #1448/#1449/#1451/#1453/#1455 owner graph, exact-head Agda & regressions | **source-written integration, kernel OPEN** |
| NX01 | Real five-database, versioned provenance and dedup; exact 43,996-row ERIC processing ledger | **ERIC metadata performed historically; remaining databases and current world execution OPEN** |
| NX02 | Every in-scope source has verified text, exact version and complete decomposed research parts | **OPEN**, 39 occurrences != full universe |
| NX03 | Every part has every declared n-axis status; justified missing/inaccessible/N/A and re-account when adding an axis | **generic source-written contract / validator; actual corpus OPEN** |
| NX04 | Direct evidence cells have real packet, span, revision, per-part relevance, observation membership and source audit | **contract source-written, actual reviewed inhabitants OPEN** |
| NX05 | Actual arbitrary-arity interactions and consumer-specific sufficiency/nonfactorability audited for every relevant study question | **generic formalism exists; ESD source-specific runs OPEN** |
| NX06 | Cross-study gap/transport evidence and independent review; no source/patient/population auto-filling | **candidate routing source-written; reviewed transfers OPEN** |
| NX07 | Historical dependency changes, selective invalidation, conflicting local sections and epistemic reflexivity on actual evidence | **existing synthetic/methodological donors; observed ESD revision OPEN** |
| NX08 | Complete verified world components, independent review/adjudication and manuscript findings | **OPEN** |

### Attribution requirements

Cite original paper authors/DOIs, distinguish paper claims from Dashi reconstructions, Dashi proofs and runtime checks, and never promote a synthetic test, structurally validated JSON, conceptual donor or source genealogy to a reviewed scientific finding. Apply specific cultural/participant authority boundaries, including Two-Eyed Seeing, rather than using them as convenient ontology labels.
