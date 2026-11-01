# LES cross-pollinated latent ecology formalism

## Status

This document records a **candidate-only, fail-closed bridge** between the Living Environment System (LES) planning architecture and the existing DASHI trit, Base369, depth-address, ultrametric, receipt, and promotion-boundary machinery.

It does **not** claim that DASHI currently proves ecological, agronomic, hydrological, economic, conservation, or pollution-attribution results. It provides typed carriers and escalation contracts for implementations and future proofs.

## Existing DASHI content reused

The implementation deliberately references existing repo content rather than creating a parallel formalism:

- `DASHI.Foundations.SSPTritCarrier`
  - canonical typed values `-1`, `0`, `+1`
  - bridges to `DASHI.Algebra.Trit` and `Base369.TriTruth`
- `DASHI.Geometry.SSP369Ultrametric`
  - finite depth-indexed addresses
  - agreement depth, prefix witnesses, and checked ultrametric
- the repo-wide canonical / experimental / validation and fail-closed receipt pattern

The ecological reading is therefore a consumer of the existing formal spine, not a promotion of ecology into that spine.

## Implemented modules

### `DASHI.Environment.LatentDepthFormalism`

Defines:

- finite balanced-trit depth states
- a total bridge from SSP trits into the checked `Digit369` address carrier
- agreement depth, depth distance, and cylinder witnesses inherited from the existing ultrametric module
- model lanes:
  - **Path A**: deterministic screening and cheap invariant checks
  - **Path B**: learned latent or surrogate exploration trained from authoritative simulations or observations
  - **Path C**: finite mechanistic or otherwise authoritative analysis
- explicit escalation gates for:
  - out-of-support inputs
  - excessive residual
  - excessive uncertainty
  - conservation failure
  - policy-critical use
- an MDL-style cost carrier separating residual, structural, and authoritative-model invocation costs
- an external `EnvelopeContract` that requires implementations to supply evidence for depth weighting, first-difference distance control, injectivity regime, support declaration, and uncertainty calibration

The continuous map

`Phi(d) = sum_k d_k lambda^k`

is not falsely reconstructed as an Agda real-analysis theorem here. The exact finite prefix geometry is proved; the continuous or learned numerical envelope is an evidence-bearing boundary contract.

### `DASHI.Environment.FunctionalEcology`

Defines:

- functional groups and functional roles
- context-gated signed interactions
- ecological guilds
- optional species-level refinements
- threatened-species objectives with a no-net-harm gate for native guilds
- explicit fungal guilds:
  - arbuscular mycorrhizal
  - ectomycorrhizal
  - ericoid mycorrhizal
  - saprotrophic
  - endophytic
  - pathogenic
- whole-system intervention primitives:
  - planting
  - grazing regime
  - fungal inoculation
  - soil remediation
  - contour earthworks
  - dams and wetlands
  - floating planters
  - riparian buffers
  - habitat corridors
  - access tracks
  - irrigation
  - nutrient-source control
  - mechanical removal
- operational context for machinery, labour, fuel, water, capital, prices, law, and cultural constraints
- biosecurity- and provenance-gated mycorrhizal candidate selection

An ecological trit is only a **context-indexed observable**: negative, negligible/neutral, or positive relative to a declared target. It is not a universal species label or causal proof.

### `DASHI.Environment.InversePlanning`

Defines:

- measured observations with evidence depth and uncertainty
- auditable source hypotheses with spatial, temporal, transport, and mechanism fields
- explanations costed by residual, transport, and complexity
- ranked explanations with an explicit “hypothesis, not blame” boundary
- multi-objective plans across water, erosion, nutrients, habitat, threatened species, pollination, native pollinators, soil carbon, yield, profit, labour, machinery, fuel, and climate resilience
- hard and soft constraints
- planning receipts carrying provenance, assumptions, exclusions, escalation evidence, and mandatory human approval

This supports the intended inverse workflow:

1. observe a downstream residual, such as nutrient loading, eutrophication, pondweed, salinity, erosion, or habitat decline;
2. enumerate spatially and temporally plausible source hypotheses;
3. evaluate transport and process compatibility using Path A or Path B;
4. escalate policy-critical or poorly supported candidates to Path C;
5. rank explanations by fit plus structural cost while disclosing uncertainty and missing-source risk.

It is not a legal-attribution engine.

### `DASHI.Environment.LatentEcologyRegression`

Provides small canonical witnesses for:

- trit-depth self agreement and self distance
- cylinder construction
- a native-pollinator support guild
- an AMF candidate passing context, provenance, and biosecurity gates
- a candidate planting intervention
- policy-critical escalation from Path B to Path C
- a screening planning receipt

## LES architecture correspondence

| LES concept | DASHI carrier |
|---|---|
| GIS / graph / field state | external scenario carrier behind `WholeSystemContext` |
| functional group effect | `SSPTrit` with context gate |
| guild | list of groups plus typed interactions and tradeoffs |
| latent simulator embedding | `EnvelopeContract` |
| coarse-to-fine model selection | `ModelLane` and `EscalationEvidence` |
| residual mismatch | `ModelCost.residualCost` / `Explanation.residualCost` |
| model complexity | `structureCost` / `complexityCost` |
| expensive finite simulation | Path C plus `authorityInvocationCost` |
| pollution back-calculation | `SourceHypothesis`, `Explanation`, `RankedExplanation` |
| intervention portfolio | `Plan` and `PlanningReceipt` |

## Intended computation split

The formal layer remains backend-neutral.

A practical LES implementation may use:

- GIS and deterministic diagnostics for Path A;
- GPU graph/field propagation and learned reduced-order models for Path B;
- APSIM, DNDC, SWAT+, groundwater, hydraulic, ecological, or engineering models for Path C;
- an MDL- or Pareto-style controller to decide when deeper resolution or authoritative invocation is worth its cost.

The Agda contract requires the implementation to expose the lane, support region, uncertainty, residual, conservation checks, assumptions, exclusions, and provenance.

## Cross-pollination gained

From LES into DASHI:

- a concrete whole-system consumer for the depth/MDL formalism
- explicit model-authority escalation rather than latent-model promotion
- context-indexed ecology, guilds, fungi, machinery, labour, markets, and inverse catchment diagnosis

From DASHI into LES:

- one canonical trit carrier rather than ad hoc signed enums
- prefix/depth geometry for controlled coarse-graining
- fail-closed receipts and non-promotion boundaries
- a precise Path A -> Path B -> Path C refinement contract
- MDL-style accounting for fit, structural complexity, and expensive solver invocation

## Next proof and implementation work

1. Add finite truncation maps and prove their prefix compatibility.
2. Add a typed graph carrier with spatial and hydrological connectivity witnesses.
3. Replace natural-number placeholder costs with a unit-tagged ordered cost algebra.
4. Add conservation receipts for water, sediment, carbon, nitrogen, and phosphorus.
5. Add a surrogate-calibration receipt linked to held-out authoritative simulations.
6. Add Pareto dominance and constraint-satisfaction proofs for finite candidate sets.
7. Build one executable golden scenario, preferably a small pond/catchment nutrient and floating-planter example, with all assumptions and escalation decisions exported into an Agda-readable receipt.
