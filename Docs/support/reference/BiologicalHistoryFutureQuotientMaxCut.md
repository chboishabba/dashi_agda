# Biology, phenotype and future-observation max-cut — 6 November 2026

## Scope and authority

This programme follows the accompanying genotype–phenotype/Levin/ontology/world-model
research brief.  Its target is **which differences in sequence, molecular state,
local tissue geometry, systemic context and developmental history survive into
specified future physical or phenotypic observations under interventions**.

Wolfram-style cellular automata/multiway rewriting are *one optional computational
presentation* alongside reaction–diffusion, stochastic chemistry, electrodiffusion,
control, graph rewriting, developmental bioelectricity and molecular mechanics.
They are not the organising theory and cannot be substituted for measured biology.

The canonical mathematics remains in Golden Agda, with related numerical work in
dashitest, dashifine, dashiBRAIN and dashiQ, and provenance in ITIR/PNF.  Existing
`DASHI.Programmes.ResearchProgrammeExact` is the repository registry.  No second
repo or source-truth registry is proposed.

## The new concrete finite theorem package

Owner: `DASHI/Biology/Physical/BiologicalHistoryFutureQuotientExact.agda`.
Cumulative root: `DASHI/EverythingBiologicalHistoryFutureRound23.agda`.

Selected **abstract** state is
`(genomeCompetence, chromatinMarker, retainedMemory, junctionPresent,
environmentalSupport, visibleMorphology)`, all Boolean.  The marker is inert
*only in this chosen fixture*: this asserts nothing about real chromatin biology.

Interventions are `signal`, `wound`, `connect`, `restoreMemory`, and
`provideEnvironment`.  The future-sufficient code forgets the inert marker
while retaining the other five coordinates.  Proven in Agda source:

- `projectionCommutes`: every action commutes with fine-to-coarse projection.
- `projectionAfterTrace`: this holds for every finite action trace.
- `futureSufficientCodeIsSafe`: equal coarse codes entail equal complete
  deterministic future observation languages, reusing the original canonical
  future-equivalence theorem.
- `sameGenome`, `samePresentPhenotype`, `memoryDifference`, and
  `sameSignalDistinguishesFuture`: same genome competence and current
  morphology but different memory can lead to distinct future morphology.
- `morphologyOnlyNotFutureSafe` and
  `memoryBlindProjectionNotFutureSafe`: no future-safe projection can merge
  the exhibited pair under the stated interventions.
- `markerActuallyDiffers` and `markerStatesAreFutureEquivalent`: a concrete
  noninjective safe quotient in the selected finite model.
- `spatialProjectionCommutes` and `localEdgeResponseSurvivesProjection`:
  pointwise and actual nearest-neighbour response projections on the existing
  nonperiodic `P3 × P3 × P3` geometric carrier.
- `oneAdjacentJunctionChangesSourceResponse`: an adjacent +x junction
  change alters a source's local response while the source itself is fixed.

This **is not** a calibrated interpretation of any genome, signalling pathway,
bioelectric voltage, chromatin effect, cell type, or whole-organism attractor.

The second owner provides a distinct **synthetic mechanism/evidence feedback**
regression.  It reuses the existing `PhenomenonEvidenceFibreOverTimeExact`
instead of introducing another evidence governance system:

- `syntheticObservationRefinesModelFamily`: a distinguishing observed
  response removes the memory-blind candidate from the admitted family;
- `memoryBlindMisfitsSyntheticObservation`: the model predicts a
  conflicting result for the selected fixture;
- `withdrawalReopensModelCandidate`: reanalysis/withdrawal can re-admit the
  rejected candidate without rewriting the history;
- `SourceCalibratedMechanism` makes provenance, the ontology-to-reaction
  join, valid units, original observation and prediction match **separate
  proof-relevant obligations**.  No instance is fabricated.

This demonstrates feedback logic, **not** GO-CAM ingestion, SBML parsing, an
identified reaction mechanism or an empirical discrimination result.

The mathematical condition is the commuting diagram

`project(step a x) = coarseStep a (project x)`

for every selected action, lifted to finite intervention traces.  The retained
code therefore preserves morphology responses under the fixture.  Current
morphology alone does not.

Existing donors reused (not replicated): `FutureObservationLanguageQuotientExact`,
`GenericFuturePartitionRefinementExact`,
`StablePartitionCanonicalFutureBridgeExact`,
`DynamicTopologyFutureDefectExact`,
`DynamicTopologyObserverRefinementExact`,
`FiniteMorphogeneticBasinControlExact`,
`PlanarianControlCalibrationExact`, and
`Base369Ternary27HypervoxelFabricGeometryExact`.

## Read-only GO-CAM and SBML evidence intake

`scripts/biological_gocam_sbml_receipt_intake.py` now supplies a concrete
**source-intake**, separate from the Golden mathematical and physics owners.
It reads local GO-CAM LinkML-style JSON and SBML Level-3 XML, retaining file
SHA-256, original model/activity/reaction identifiers, causal predicates,
source evidence terms, SBML parameter units, and kinetic-law presence.

It rejects duplicate activity/species/reaction/parameter IDs, missing causal
edge endpoints within the selected model, nonexistent crosswalk endpoints, and
join assertions without an evidence reference. No label-based or silent
gene-name matching is permitted. Every crosswalk join remains `trusted=false`;
the output is a read-only unpromoted JSON receipt, not an ITIR/PNF write.

Example:

```bash
python3 scripts/biological_gocam_sbml_receipt_intake.py --self-test

python3 scripts/biological_gocam_sbml_receipt_intake.py \
  --gocam source-gocam.json --sbml source-model.xml \
  --crosswalk explicitly-evidenced-crosswalk.json \
  --output unpromoted-biological-intake.json
```

The optional crosswalk file is a JSON object with a `joins` array containing
`gocam_activity`, `sbml_reaction` and `evidence_reference` fields.
A provided crosswalk is a *source-asserted candidate*, not an established
biochemical equivalence.

This adapter deliberately **does not** validate the full GO-CAM LinkML schema,
implement libSBML semantic or unit analysis, interpret MathML kinetics, execute
a simulation, estimate parameters, calibrate an assay, or write to PNF.
Production promotion needs the official
[GO-CAM gocam-py model](https://geneontology.github.io/gocam-py/) and
[SBML Level-3 specification](https://sbml.org/documents/specifications/)
plus the original experimental provenance, units and result receipts.

## Round-23 P0–P5 implementation delta and exact remaining max-cut

This tranche *implements* finite theorem owners, live source-intake and
evaluation executables, while refusing to manufacture missing biological
observations or trusted checker receipts.  An executable research pipeline is
not the same as a source-validated scientific result.

| Gate | New implementation | Exact unresolved acceptance |
|---|---|---|
| P0 — biological carrier | `SourceIndexedBiologicalCarrierExact` assembles the original `CellStateAttractor` genome/chromatin/RNA/proteome/metabolism/membrane/environment/history carrier with a typed phenotype observation, experimental time/history, and the exact Grodstein–Levin source-observation anchor. | **P0.PHYSICAL-INSTANCE:** original sequence/assay/context-specific physical state and source-qualified history evolution, with actual observational readouts; the Boolean fixture is not a physiological cell. |
| P1 — future quotient | `BiologicalFuturePartitionCompilerExact` instantiates `CertifiedPartitionRefiner`, with a rank-bounded depth-zero stable code *relative to the five-coordinate future-sufficient observer*. `BiologicalStochasticFutureLumpingExact` gives a half/half hidden-marker randomized rational Markov operator and an all-horizon lumpability transport. The supplemental finite script computes the morphology-observer partition by refinement without confusing it with the stronger code observer. | **P1.KERNEL:** independent exact-head parallel_checker/Agda acceptance; **P1.PHYSICAL-STOCHASTIC:** experimentally justified stochastic transition rates and source-specific admissibility; **P1.MORPH-MINIMAL:** promote the actual morphology-observer minimal finite partition into the Golden compiler if needed. |
| P2 — spatial dynamics | `BiologicalCoupledTissueCubeExact` provides a synchronous old-field neighbour-coupled update with explicit real 3×3×3 nearest-neighbour witnesses, a concrete nonperiodic x-neighbour schedule for every vertex, arbitrary-trace fine/coarse preservation without function extensionality, and a source-written one-step finite basin/fixed-point result for repeated unchanged signalling. | **P2.ALL-EDGE-PNP:** full 54-edge/36-plaquette flux, physically typed local couplings, conservation/boundary conditions, measured tissue dynamics, and physical basin transport beyond the selected Boolean one-step idempotence. The selected neighbour operator is a finite mathematical model, not tissue physics. |
| P3 — kinetic calibration | `validate_biological_source_models.py` performs fail-closed official gocam-py/libSBML checks when those dependencies are installed. `biological_si_kinetic_calibration.py` fits a declared SI first-order production/decay law on source-scoped training experiments, bootstraps by experiment and reports disjoint held-out performance and identifiability failures. | **P3.ORIGINAL-SI:** original model-specific kinetic parameter values, external SI-unit validation, lawful simulation of selected SBML/SED-ML equations, uncertainty/identifiability controls, measured tissue/chemical trajectories and independent experimental replication. First-order fitting does not validate another biological mechanism by analogy. |
| P4 — ontology / PNF | `biological_gocam_sbml_receipt_intake.py` reads original IDs, predicates, source hashes and explicit candidate crosswalks; `BiologicalEvidenceFeedbackFiniteExact` proves finite evidence-driven rejection and reopening. ITIR-suite draft PR [#72](https://github.com/chboishabba/ITIR-suite/pull/72) adds a source-bound, review-only candidate projection to the canonical world-model boundary with evidence and trust tests. | **P4.CANONICAL-PG:** original schema validation on an identified model, source-span SLR/PNF parser, reviewed candidate reconciliation and actual PostgreSQL authoritative receipts. No parallel persistent store or automatic ontology mutation. |
| P5 — held-out measurements | `prepare_shine_dalgarno_measured.py` is pinned to the 2020 Kuo et al. original dmsC replicate columns as provided by the 2026 `cmarti/shine_dalgarno` reanalysis, with genotype-disjoint train/validation/test splits and no inferred imputation. `biological_measured_genotype_holdout.py` selects additive/pairwise regularized regressions by validation only and reports held-out metrics/bootstrap intervals. `check_biological_spatial_stochastic.py` independently checks the selected finite spatial/stochastic claims. | **P5.ORIGINAL-RUN:** fetch/audit the actual measured CSV and preserve its original SHA/experiment context, reproduce the connector-computed original-data readout in the committed Python code and obtain an independent receipt; **P5.DEVELOPMENT:** longitudinal planarian/Levin control cohorts, prospective morphological basin predictions, independent controls/replication and source-separated effect estimates. A static dmsC translation-efficiency benchmark is *not* a developmental attractor experiment. |

### Source lineage is two-stage

- **Original experiment:** Kuo et al. (2020), *Global fitness landscapes
  of the Shine-Dalgarno sequence*, DOI `10.1101/gr.260182.119`.
  The original assay measured sequence-dependent GFP/translation-efficiency
  responses in multiple mRNA contexts.
- **Reanalysis and reproducible code:** Martí-Gómez et al. (2026),
  *Inference and visualization of complex genotype–phenotype maps*,
  DOI `10.1093/molbev/msag023`.
  The [upstream repository](https://github.com/cmarti/shine_dalgarno)
  contains `data/dmsc.csv`, and `scripts/prep_data/get_mave_data.py`
  specifically reads `Genotype`, `dmsC.1`, `dmsC.2`, `dmsC.3`.
  Our input adapter requires the reviewer to declare the original trait scale.

The upstream reanalysis distinguishes directly measured genotypes from
model-inferred landscape positions. The converter retains observed replicates
and rejects missing values; it never promotes the full `4^9` inferred
landscape as independent measured outcomes.

**Original-data readout obtained.** The GitHub content-file endpoint returned an
empty payload for this large CSV, but the Git *blob SHA* endpoint returned the
entire original source table (262,144 9-mers). The 2026-11-06 in-memory
measured-data analysis contains 257,565 genotypes with at least one dmsC
replicate and 635,085 observed replicate values.

Source-identified report:
`Docs/support/reference/OriginalDmscMeasured20261106.md`.
The report documents a 181,279 / 37,784 / 38,502 genotype-disjoint
train/validation/test split, original measured-data G/C/U count model test
RMSE 0.321043 against baseline 0.364172 (11.8431% improvement), a
600-resample genotype bootstrap 95% interval for improvement of
11.5062%–12.1945%, and measured Hamming-one tolerance-network component
counts at epsilon 0.05, 0.10 and 0.20.

This is a genuine primary-source computational readout, **not** a running
receipt from the newly committed Python reproduction scripts. Those scripts
remain to be executed independently on the pinned CSV, and a source/assay
batch-replication or mechanistic attractor claim still requires more data.

### Exact commands

```bash
bash scripts/check_biological_history_future_round23.sh
# Then run the repository's independent parallel_checker on exact HEAD.

python3 scripts/prepare_shine_dalgarno_measured.py \
  --raw /path/to/upstream/data/dmsc.csv \
  --out /tmp/dmsc-measured-assay.csv \
  --manifest /tmp/dmsc-source-receipt.json \
  --trait-unit 'log[GFP]'

python3 scripts/check_original_dmsc_holdout.py \
  --original-csv /path/to/upstream/data/dmsc.csv \
  --receipt /tmp/dmsc-primary-ols-reproduction.json

python3 scripts/check_original_dmsc_neutral_components.py \
  --original-csv /path/to/upstream/data/dmsc.csv \
  --output /tmp/dmsc-primary-component-reproduction.json

python3 scripts/biological_measured_genotype_holdout.py \
  --assay /tmp/dmsc-measured-assay.csv \
  --output /tmp/dmsc-heldout-receipt.json

python3 scripts/validate_biological_source_models.py \
  --gocam /path/to/real-gocam.json \
  --sbml /path/to/real-model.xml \
  --output /tmp/schema-validated-sources.json
```

The `/tmp` outputs above are **ephemeral reports**, not a replacement
JSON ledger or persistent source-truth store; source-reviewed promotion
belongs only to the canonical PostgreSQL PNF pipeline.

### Acceptance standing

- Source-written: all new Agda owners and source-intake/calibration/evaluation
  scripts are committed in the draft PR.
- Runtime tests: the previous finite Python enumeration passed; this
  session has **no independently executed receipts** for the newly committed
  P0–P5 scripts.
- Agda kernel: **not confirmed**; no exact-head parallel_checker pass.
- Real assays: **not run**, and no model-specific calibration is claimed.
- World model: ITIR PR #72 is a candidate-only bridge, not a canonical PNF
  materialisation or a trusted ontology equivalence.

## Model/observation/ontology feedback must be bidirectional

The scientifically testable architecture is:

1. Source-identified genome, feature annotation, chemistry, molecular mechanism
   and regulatory/cellular context constrain a family of dynamical models.
2. SI-compatible kinetic/transport/electrical/mechanical dynamics predict
   observables under specified intervention histories.
3. Measured time-series and interventions constrain parameters, disqualify or
   reopen causal claims, and change admissible model families.
4. Versioned PNF/ITIR state carries the identity, experimental scope, uncertainty,
   negative evidence, rejected hypotheses and revision path.

GO-CAM activities and causal assertions are **not** themselves rate equations;
BioModels/SBML equations are **not** automatically calibrated truths.  Joins
must be exact, source-grounded and reversible/traceable; approximate identities
need explicit evidence and cannot be promoted solely by textual similarity.

For stochastic cases, the object of future equivalence is the law of observed
trajectories under admissible interventions, not only the set of possible
endpoints.  Observational equivalence at one time is weaker than future
behavioural equivalence.  A tolerance-defined near-equivalence is a pseudometric
or bounded defect, not automatically a transitive quotient.

## Existing quantitative anchors and limits

`PlanarianControlCalibrationExact` records the Grodstein–Levin 2022
155/555 parameter-search count and the 65/35 phenotype proportion for one
reported case.  Neither quantity identifies a unique bioelectric basin, and
the first is **not** a population frequency.

`FiniteMorphogeneticBasinControlExact` supplies a four-state finite control
regression with quantitative intervention costs; it does not measure a
separatrix in biological tissue.  The history-indexed phenotype fibres and
3×3×3 spatial structure are distinct: a tissue can carry a local field of
cubical coordinates through time; one vertex is not the entire organism.

## Regression, acceptance and non-promotion

`scripts/check_biological_history_future_quotient.py` checks the synthetic
state/action census, exact projection laws, selected divergence and 27-point
cube structure; this is supporting computation, not formal or empirical proof.

`scripts/check_biological_history_future_round23.sh` runs that regression,
rejects simple proof escapes, then **requires a working Agda executable** to
check the cumulative Golden root.  It exits nonzero when Agda is missing,
rather than claiming kernel acceptance.

### Acceptance levels

- **Source-written**: Agda code and source connections exist.
- **Computational regression**: Python finite checks pass.
- **Kernel accepted**: exact-commit Agda command exits zero and its receipt is
  retained.
- **Model calibrated**: source-backed parameter estimates, units, uncertainty
  and held-out predictions are independently assessed.
- **Mechanistic finding**: a discrimination test supports a specific biological
  claim against relevant alternatives and controls.

The Golden code remains **source-written, not kernel accepted**. Separately,
the original measured dmsC genotype holdout and tolerance network were
computed in-memory directly from the pinned Git source blob, and the results
are recorded in `OriginalDmscMeasured20261106.md`. Independent Python
execution and `parallel_checker` receipts remain pending. No Agda kernel,
*physically calibrated* SBML kinetics, production ontology/PNF importer, or
independent developmental-attractor validation receipt is claimed. The read-only lexical intake is not
substituted for these gates.

## Remaining decisive implementation order

1. Exact-head Golden Agda and parallel_checker acceptance for all Round-23
   owners, including the original canonical root and transitive imports.
2. Independently reproduce the original measured dmsC in-memory readout
   using the committed Python scripts, preserving source SHA256 and experiment
   provenance; validate neutral tolerance thresholds against assay error.
3. Select original planarian treatment/longitudinal measurements and fit the
   actual bioelectric/chemical model, not a generic surrogate.
4. Complete source-validating GO-CAM/LinkML and SBML/SED-ML adapters,
   then pass through the native reviewed PostgreSQL PNF parser and receipts.
5. Independently test intervention-conditional future equivalence, basin
   boundaries, ecological context and model alternatives.

A failed calibration or disconfirming intervention remains an informative
accepted result; it must not be reclassified as a proof failure or silently
discarded.
