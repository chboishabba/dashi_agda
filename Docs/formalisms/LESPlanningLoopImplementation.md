# LES spatial, quantitative, calibrated planning loop

This tranche extends the merged latent-ecology spine into a finite and auditable
planning loop.  It remains a formal contract surface: external GIS data,
numerical model runs, ecological observations, prices, and regulatory facts are
not certified merely because they inhabit these types.

## Implemented modules

### `DASHI.Environment.DepthTruncation`

* variable-depth trit streams;
* exact truncation;
* truncation is a prefix;
* idempotence;
* a shallower truncation is a prefix of a deeper truncation;
* cylinder membership by equal finite truncation;
* depth-refinement and residual-depth decision receipts.

This is the finite bridge needed before any continuous or learned envelope is
used.  Residual improvement may justify considering deeper analysis, but does
not by itself mandate or promote that analysis.

### `DASHI.Environment.SpatialTransport`

* GIS cells, parcels, catchments, waterbodies, reaches, groundwater zones,
  roads, habitat patches, and intervention footprints;
* separate directed media for water, groundwater, sediment, nitrogen,
  phosphorus, pollen, animals, seeds, machinery, and people;
* compositional path and reachability witnesses;
* spatial-support, timing, attenuation, and provenance receipts;
* machinery profile and route constraints.

Map adjacency is explicitly not treated as proof of physical transport.

### `DASHI.Environment.QuantitiesConservation`

* unit-indexed quantities for money, labour, machinery, fuel, water,
  earthworks, rainfall, N/P/C/sediment, habitat, crop yield, and emissions;
* resource ledgers;
* water, nitrogen, phosphorus, carbon, and sediment balance receipts;
* bounded, disclosed unaccounted residuals.

The type of addition prevents the formal operator from adding unlike units.
Runtime numeric scale and conversion remain explicit adapter responsibilities.

### `DASHI.Environment.SurrogateCalibration`

* authoritative model identity and version;
* declared input domain and exclusions;
* training and held-out coverage;
* output and unit contract;
* latent encoder/predictor/uncertainty interface;
* held-out error bound;
* conservation bundle;
* runtime support, residual, uncertainty, conservation, and policy assessment;
* fail-closed Path A/B/C escalation receipt.

The receipt claims calibrated behaviour only within the declared validation and
support contract.  It does not assert universal surrogate correctness.

### `DASHI.Environment.EcologicalEvidenceGates`

Replaces recommendation-level booleans with evidence carriers for:

* host/fungal compatibility;
* pH and moisture ranges;
* native/introduced status;
* pathogen screening;
* inoculant provenance and chain of custody;
* current regulation;
* geographic transfer;
* local field evidence;
* threatened-species expert and community review.

### `DASHI.Environment.ParetoPlanning`

* finite objective vectors with direction, unit, and provenance;
* componentwise no-worse relation;
* strict improvement on at least one objective;
* dominance only between hard-constraint-admissible plans;
* non-dominance and bounded finite-population result carriers;
* explicit separation of MDL model selection from Pareto plan selection.

### `DASHI.Environment.SpringfieldPondGoldenScenario`

A synthetic, non-deployment fixture records:

* upper-catchment -> stormwater reach -> pond phosphorus transport;
* an upstream nutrient-loss source hypothesis;
* floating planted wetland, riparian buffer, and mechanical-removal options;
* a combined intervention plan and a mechanical-only comparison;
* conservation receipts;
* policy-critical escalation from latent exploration to authoritative analysis;
* GIS output and provenance contracts.

Real use requires audited Springfield datasets and local ecological,
engineering, regulatory, custodian/community, and operational review.

### Knowledge, governance, and runtime boundary

* `EcologicalKnowledge` types versioned regional trait, phenology,
  pollinator, habitat, crop, grazing, remediation, envelope, invasive, and
  biosecurity knowledge.
* `ValidationGovernance` types hindcasts, pollution reconstructions, expert
  comparisons, counterfactuals, sensitivity tests, community constraints, and
  deployment gates.
* `LESRuntimeBoundary` keeps the repository boundary explicit:
  `dashi_agda` owns contracts, invariants, receipts, and promotion gates;
  Living Environment System owns GIS ingestion, numerical execution,
  calibration, optimisation, map generation, and scenario orchestration.
* `PlanningLoopRegression` imports the complete tranche and records canonical
  finite witnesses.

## Remaining empirical work

The formal spine is now ready to consume, but does not manufacture:

1. an audited Springfield GIS/data package;
2. calibrated catchment and pond process models;
3. locally validated ecological knowledge entries;
4. measured resource and price scenarios;
5. runtime-generated Pareto populations;
6. formal receipts serialised from the LES runtime;
7. independent hindcast and policy review results.

Those are intentionally runtime and evidence tasks rather than postulated Agda
theorems.
