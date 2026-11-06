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

## Exact P0–P5 status / remaining max-cut

| Gate | Completed or already reusable | Remaining named decisive obligation |
|---|---|---|
| P0 — phenotype carrier and histories | `CellStateAttractor` coupled-cell carrier; Levin geometry; generic `IndexedBiologicalPhenotype`; new finite `BiologicalState` | **P0.BIO-CARRIER**: instantiate actual genome/regulation/chemistry/cell/tissue carriers and admissible history-indexed fibres with source-backed observations, rather than just finite flags |
| P1 — future equivalence | New safe/unsafe projection, trace commutation, concrete nonfactorability; existing general future language quotient and finite compiler | **P1.FINITE-COMPILER**: give this biological finite transition system an accepted `CertifiedPartitionRefiner`, rank bound and stable partition; **P1.STOCHASTIC**: compare distributions using measured/admissible stochastic transition kernels |
| P2 — cubical spatial field | Existing 27-vertex, 54-edge, 36-plaquette, 8-cube geometry; new pointwise and one-hop adjacency-gated response/projection proofs | **P2.COUPLED-FIELD**: construct a simultaneous neighbourhood-coupled state evolution, prove all-edge/plaquette and boundary compatibility, and transport the biology quotient through it |
| P3 — physical calibration | Existing finite chemical master generator, electrodiffusion, SI bioelectric adapter, B-DNA SE(3), finite basin and planarian source count observations | **P3.SBML-SI**: versioned SBML/SED-ML model/parameter ingestion, unit-checked original molecular state laws, identifiability analysis, trajectory error/uncertainty, held-out calibration and exact provenance receipts |
| P4 — ontology/world model | Existing PNF/ITIR evidence/history governance; new finite source/model refinement and reopening theorems with an uninhabited calibrated join contract; canonical programme registry | **P4.ONTOLOGY-WELD**: versioned GO-CAM/ontology/Cell Ontology/uPheno/SBML identity graph with evidence-qualified causal edges, source-safe joins, rejected hypotheses and bidirectional model revision |
| P5 — empirical discrimination | Explicit fine-vs-coarse intervention tests in finite fixture; existing dashitest/dashifine numerical machinery and planarian observations | **P5.HELDOUT**: source-separated measurements, held-out predictions, uncertainty intervals, neutral-component census, local/global perturbation sensitivity and prospective predictions that can distinguish candidate attractor models |

No gate P0–P5 is legitimately globally closed for *real biology* by the
new finite proof alone.  The direct deterministic finite part of P1, and the
selected finite spatial-response part of P2, are source-written pending Agda
acceptance.  P3–P5 require external model and experimental data, not tautological
proof fields. The P4 finite feedback regression is source-written, but no
production ontology or world-model importer has been accepted.

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

Only the first level has been established in this branch before a compiler run.
A separate local Python enumeration passed the synthetic finite checks; it is
not a receipt for a run of the exact committed script or an Agda kernel pass.
No Agda kernel, SBML ingestion, ontology importer, or held-out biological
validation receipt has been claimed by this document.

## Next prioritized max-cut

1. P1.FINITE-COMPILER + P0.BIO-CARRIER on the real genotype/phenotype domain.
2. P2.COUPLED-FIELD with actual local interactions and meaningful boundary laws.
3. P3.SBML-SI and P4.ONTOLOGY-WELD as an evidence/physics feedback pair.
4. P5.HELDOUT including a deliberately selected distinguishing perturbation.

Useful first measured comparison, subject to retrieval and provenance audit:
the attachment's Shine–Dalgarno landscape or yeast promoter-expression data,
followed by planarian regenerative perturbation histories.  Model accuracy,
mechanism identification and evolutionary interpretation remain separate claims.
