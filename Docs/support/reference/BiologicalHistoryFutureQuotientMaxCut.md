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
| P1 — future quotient | `BiologicalFuturePartitionCompilerExact` instantiates `CertifiedPartitionRefiner`, with a rank-bounded depth-zero stable code *relative to the five-coordinate future-sufficient observer*. `BiologicalStochasticFutureLumpingExact` gives a half/half hidden-marker randomized rational Markov operator and an all-horizon lumpability transport. The supplemental finite script computes the morphology-observer partition by refinement without confusing it with the stronger code observer. | **P1.KERNEL:** independent exact-head parallel_checker/Agda acceptance; **P1.PHYSICAL-STOCHASTIC:** experimentally justified stochastic transition rates and source-specific admissibility; **P1.MORPH-MINIMAL:** the 18-class morphology-observer minimal code now has an explicit source-written Agda exact-future equivalence proof in `BiologicalMinimalMorphologyFutureQuotientExact`; independent Agda/parallel_checker kernel acceptance remains to be obtained. |
| P2 — spatial dynamics | `BiologicalCoupledTissueCubeExact` provides a synchronous old-field neighbour-coupled update with explicit real 3×3×3 nearest-neighbour witnesses, a concrete nonperiodic x-neighbour schedule for every vertex, arbitrary-trace fine/coarse preservation without function extensionality, and a source-written one-step finite basin/fixed-point result for repeated unchanged signalling. | **P2.ALL-EDGE-PNP:** the 54 positive directed bonds and 36 elementary squares now have native source-written incidence/path-closure and projection checks; physically typed flux, conservation and boundary laws, measured mechanics/PNP and biological basin transport remain required. The selected neighbour operator is a finite mathematical model, not tissue physics. |
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


## 2026-11-06 max-cut refinement: minimal quotient, complete cubical incidence, replicate-aware experimental readout

This extension reuses the established owners and source identities.  It does
not introduce a new persistent ontology or assume that a toy Boolean law
describes a tissue.

### P1 — exact minimal morphology-observer quotient

`BiologicalMinimalMorphologyFutureQuotientExact.agda` proves, for the
specified six-Boolean state and five interventions, the stronger equivalence

`minimalProject(x) == minimalProject(y)` **iff**
`FutureObservationEquivalent(deterministicSystem step, observe, x, y)`.

Unlike the previous sufficient five-coordinate code (32 values), the
minimal code has **18 classes**: two genome-incompetent classes distinguished
by current morphology, and 16 genome-competent classes distinguished by the
three causal flags and morphology.  It is *not* safe to erase chromatin or
biological memory in an arbitrary physiological model; this is a
source-written theorem for the explicitly chosen fixture only.

Five experiment words, comprising the empty observation and four controlled
intervention histories, exactly decode the quotient: isolate genome,
memory, junction and environment, with the current phenotype retained.
The Golden proof uses the repository's canonical future-language bridge,
not an independently invented equivalence definition.

`scripts/check_biological_minimal_cube.py` exhaustively enumerates 64
states and independently refines the original morphology observer.  Its
class counts are **2 → 4 → 10 → 16 → 18**, and its final partition is
identical to the explicit diagnostic and minimal-code kernels.

**Acceptance boundary:** source-written proof and a separately computed
finite enumeration; no independent exact-head Agda/parallel_checker receipt.

### P2 — full cubical incidence without physical overclaim

`BiologicalFullCubeIncidenceExact.agda` reuses the native ternary
3×3×3 point and adjacency constructors.  It indexes **54 positive
coordinate-oriented nearest-neighbour bonds** (18 per axis) and
**36 elementary squares** (12 per axis pair).  All source/target edges
carry a native adjacency witness; each square's two two-step
paths have equal initial, intermediate and terminal corners by proofs,
and all bond-junction observations survive the original phenotype
projection.  No cyclic boundary is silently introduced.

This closes the **topological enumeration/incidence slice**, not the
dynamical PNP/chemistry/mechanics slice.  A physically admissible edge
current, flux conservation, boundary conditions, calibrated constitutive
laws and measured basin transport still require original source evidence.

### P0/P5 — original measured two-genotype Agda witness

`OriginalDmscTwoGenotypeMeasuredExact.agda` pins two directly measured
RNA 9-mers from the original upstream dmsC CSV (Git blob
`151cd87272cbdd6bcc2b1e70bdfd2a4ea2933d2c`), preserving
`AAAAAAAAA: 0.256, 0.769, 0.664` and
`AAAAAAAAC: 0.389, 0.908, 0.695`.
Their exact source-scale replicate means are 0.563 and 0.664, encoded
as thousandths.  It proves that the typed genotypes share their first
eight nucleotides but differ at the ninth, and that those two sample
means are arithmetically unequal.  **No statistical significance,
causal substitution effect or regenerative attractor claim follows.**

### P5 — measured replicate-range discrimination

The raw original dmsC Git blob was read directly again and the previously
reported **257,565 measured genotypes, 635,085 measured replicate values,
3,429,837 measured Hamming-one edges** and mean-tolerance edge counts
were independently reproduced in JavaScript double precision.

New `check_original_dmsc_replicate_ranges.py` adds a *fail-closed original
Git-blob checksum* and a separate descriptive classification.  For an
edge between genotypes each with at least two measured replicates:

- **all within** iff the maximum observed across-genotype replicate-pair
  difference is at most the chosen tolerance;
- **all beyond** iff even the minimum possible difference between the two
  observed replicate ranges exceeds the tolerance;
- **mixed** otherwise.

Of the measured Hamming-one edges, 2,721,334 have at least two original
replicates at both ends; 708,503 do not.

| Illustrative tolerance | Mean-difference within | All observed pairs within | All observed pairs beyond | Mixed ranges |
|---|---:|---:|---:|---:|
| 0.05 | 1,004,490 | 928 | 212,967 | 2,507,439 |
| 0.10 | 1,770,810 | 6,240 | 180,506 | 2,534,588 |
| 0.20 | 2,582,535 | 54,368 | 148,222 | 2,518,744 |

These are **not** confidence intervals, hypothesis tests or biologically
validated equivalence margins.  The result exposes how much an endpoint
mean-only tolerance graph conceals within-assay replicate spread.  A
source-calibrated error model, independent batches, prospective controls
and longitudinal organ/tissue measurements remain separate P5 work.

### Updated commands

```bash
python3 scripts/check_biological_minimal_cube.py
python3 scripts/check_original_dmsc_replicate_ranges.py --self-test
python3 scripts/check_original_dmsc_replicate_ranges.py \
  --original-csv /path/to/cmarti/shine_dalgarno/data/dmsc.csv \
  --receipt /tmp/dmsc-replicate-ranges.json
bash scripts/check_biological_history_future_round23.sh
# then run the repository's independent parallel_checker against exact HEAD
```

**Trust:** all appended Agda proof owners remain **source-written pending
kernel acceptance**. The original-data replicate-range census was
independently computed from the pinned upstream blob in this chat; the
new Python reproduction script has no independent execution receipt yet.
P0 whole-cell physiological state, P2 physical flux dynamics, P3 real
organism-specific SI calibration, P4 reviewed PostgreSQL promotion and P5
prospective developmental-attractor discrimination remain open.


### Further P1/P2 source-written advance: the actual observer compiler and every incident bond

**P1: `BiologicalMorphologyPartitionDepth4Exact.agda` now instantiates
`CertifiedPartitionRefiner` starting from the original current-*morphology*
observer**. The finite search has a source-written depth-four fixed-point
certificate (via four-action diagnostic histories), and the canonical
compiler is linked to the true 18-class future quotient. This supersedes
the earlier note that morphology-only compilation was merely a possible
future extension. The proof is Golden-integrated but its exact-head Agda
kernel receipt is still pending.

The previous fixed-operator `BiologicalStochasticFutureLumpingExact.agda`
has an additional `allControlledStochasticHistoriesRemainCoarse` theorem
for an arbitrary finite *mixed* list of interventions, not only repetitions
of one action. The companion finite rational regression enumerates all
64 states and all 156 words of length at most 3 (each probability is
computed as an exact `Fraction`). The transition rates remain synthetic.

**P2: `BiologicalAllNeighbourTissueDynamicsExact.agda` gives a stronger
synchronous tissue update** in which each of the 27 cubical sites reads
junctions at every incident bond of the complete 54-bond nonperiodic
cube. The fine and future-sufficient coarse updates preserve pointwise
equivalence for *all* finite intervention traces. In contrast with the
earlier canonical one-x-neighbour schedule, this update uses the full
undirected adjacency graph; degree distribution is 8 corners of degree
3, 12 edge-centres of degree 4, 6 face-centres of degree 5, and
1 internal site of degree 6. A proper adjacent junction flips the
source response. New independent supporting script
`check_biological_all_neighbours.py` covers 32 seeded 15-action traces.

The source-written all-neighbour rule is still Boolean. It is not yet
a validated mass-conserving ionic flux, experimentally fitted
reaction-diffusion equation, stochastic cellular kinetics,
time-varying tissue graph, or observed planarian attraction basin.

**Updated acceptance slice:** Golden root now imports all added owners;
`scripts/check_biological_history_future_round23.sh` tests all new
Python regressions and fails closed unless Agda is installed.
The project uses the *independent parallel_checker* for actual final
proof acceptance; neither a shell source scan nor the original-data
finite computational readout establishes that acceptance. All
physical calibration and PostgreSQL review gates remain explicit.


### Additional P2 basin and P5 assay-context max-cut (same extension)

The all-neighbour module now also contains
`allNeighbourSignalIdempotentAt`,
`allNeighbourCoarseSignalIdempotentAt`,
`fineResponseUnchangedBySignal`,
`coarseResponseUnchangedBySignal`, and
`fullBasinTargetProjection`. These source-written statements certify
that, under the selected *Boolean synchronous 54-bond* signalling law,
a second identical signal does not change the one-step target pattern,
and that the fine/coarse quotient agrees at that fixed target.
This is an exact **finite selected basin**, not measured
planarian convergence, noise robustness or a physiological separatrix.

Original three-context measurements in the same pinned Kuo et al. CSV
were also inspected. The measured counts are 244,401 Fepb, 259,821
Arti and 257,565 dmsC genotypes. Across the **genotype-disjoint test
split** from the earlier reproducible FNV protocol, source-measured
Pearson correlations are **0.569360 (Fepb/Arti; n=36,300),
0.475965 (Fepb/dmsC; n=36,025),
0.554731 (Arti/dmsC; n=38,268)**. All three values come from
directly measured genotype means, not predicted landscape points.

`check_original_measured_context_transfer.py` independently replays
the source-pinned three-context comparison and rejects an incorrect
source blob. Its same-study held-out contexts demonstrate measured
context dependence, **not** independent-study replication,
mechanism identification, or held-out developmental attraction.
The full methods/counts are recorded in
`Docs/support/reference/OriginalDmscMeasured20261106.md`.

**No production physiological P3 parameter claim or P4 authoritative
PNF mutation was introduced.** Both require source-specific review and
physical data; fitting arbitrary trajectories or promoting ontology
labels would violate the source-trust boundary.
