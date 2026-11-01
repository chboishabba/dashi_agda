# GR / Quantum Empirical Validation Programme

## Status

This tranche implements the evidence-facing architecture required after the proposition-level GR/quantum proof-term merge.

It does **not** claim that measured validation or independent review has already happened. The repository can construct:

```text
canonicalGRQuantumEmpiricalReadiness
```

It cannot construct:

```text
StrictPhysicalGRQuantumCorrespondence
```

without external measurement, accepted-limit, benchmark, prediction, review, and replication receipts.

## Existing repository owners reused

The programme is deliberately cross-pollinated with current repository content rather than introducing isolated evidence vocabulary.

- `DASHI.Environment.QuantitiesConservation`
  - typed units and the rule that unlike units cannot be added;
  - declared scales, residual tolerances, provenance, and model-relative conservation.
- `DASHI.Environment.SurrogateCalibration`
  - model identity, declared support, output units, held-out validation, uncertainty thresholds, and escalation.
- `DASHI.Environment.ValidationGovernance`
  - validation cases, failed criteria, independent data, visible missing data, and separate approval.
- `DASHI.Physics.DiscreteContinuumKernelTargets`
  - physical-units, consistency, stability, convergence, wave, MDL/action, and metric-selection targets.
- `DASHI.Physics.Closure.PhysicalRGCFTEmpiricalAuthority`
  - evidence provenance, uncertainty audits, competing-model comparison, independent authority, and falsification criteria.
- `scripts/validate_multiscale_flagship_receipt.py`
  - held-out evaluation, matched quality, runtime, memory, side information, leakage checks, and ablations.
- `DASHI.Unified.GRQuantumFiniteDiagnosticReceipt`
  - reproducible finite/model diagnostics with continuum and physical promotion explicitly false.
- `DASHI.Physics.Closure.PropositionEinsteinBridge`
  - exact flat Einstein/source adapters and the general tensor/source theorem boundary.
- `DASHI.Algebra.Quantum.FiniteTreeWeyl`
  - finite qutrit Weyl and Born receipts, explicitly short of continuum CCR authority.

## 1. Formal-to-measured observable maps

`DASHI.Empirical.GRQuantumObservableCalibration` defines a `CalibratedObservable` with:

- a formal state and formal observable;
- a measured experiment and measured value;
- extraction, decode, and instrument/readout maps;
- a typed physical unit;
- calibration provenance and hashes;
- a residual and declared tolerance;
- held calibration samples with a proof that residuals remain within tolerance;
- fixed normalization and propagated uncertainty.

The complete programme requires calibrated maps for:

1. proper time;
2. spatial length;
3. energy;
4. transition frequency;
5. probability;
6. curvature;
7. stress-energy.

Balanced-ternary labels, finite indices, or MDL values are not automatically seconds, metres, joules, hertz, curvature, or stress-energy.

## 2. Units and calibration

`PhysicalUnit` records:

- physical dimension;
- symbol and name;
- rational scale convention;
- normalization convention;
- traceability reference.

`GRQuantumObservableCalibration` additionally requires common coordinate and sign conventions, closed dimensional analysis, and calibration data independent of fit targets.

The current repository has exact formal observables and unit/calibration *patterns*. It does not yet contain measured calibration datasets for the GR/quantum theory.

## 3. Accepted GR/QFT limits

`DASHI.Empirical.GRQuantumKnownLimitRecovery` names six mandatory limits:

- flat special relativity;
- Newtonian weak-field gravity;
- vacuum Einstein equation;
- Born probability rule;
- free-field Heisenberg CCR;
- QFT on curved spacetime.

Each recovery case requires:

- a declared formal regime;
- DASHI and reference states;
- the same observable carrier;
- an equality-level agreement proof in the declared limit;
- assumptions and pinned reference version;
- the actual continuum/asymptotic authority.

The module supplies typed adapters to the existing flat Einstein and finite qutrit/Born receipts. Those are regression evidence only; they do not inhabit the accepted physical limit suite.

## 4. Matched-quality numerical benchmarks

`DASHI.Empirical.GRQuantumBenchmarkProtocol` requires five benchmark domains:

- weak-field GR;
- strong-field GR;
- free quantum dynamics;
- QFT correlation functions;
- joint semiclassical backreaction.

Every benchmark contains:

- pinned candidate and reference solver identities;
- immutable dataset split and leakage audit;
- matched-quality proof under a declared tolerance;
- runtime, peak memory, and energy measurements;
- side-information accounting;
- numerical error budget;
- failed-case retention;
- independent rerun;
- reproducible artifact manifest.

A runtime or memory win without matched output quality is not a successful benchmark.

## 5. Quantitatively falsifiable prediction

`DASHI.Empirical.GRQuantumPredictionProtocol` requires:

- a calibrated observable and physical unit;
- numerical DASHI and reference central values;
- declared uncertainties and minimum distinguishable separation;
- a proof that the central predictions differ;
- an explicit statistical test and rejection regions;
- outcomes capable of rejecting DASHI and the null/reference model;
- a systematics budget and sensitivity/power calculation;
- immutable theory/parameter/derivation hashes;
- preregistration before observation;
- no post-hoc parameter changes;
- publication of null and adverse outcomes.

The repository currently constructs `canonicalPredictionRequestPacket`, which explicitly records that no physical deviation value has yet been derived. Inventing a number from the finite model would be fabrication.

## 6. Independent mathematical review

`DASHI.Empirical.GRQuantumIndependentReview` requires a signed mathematical review pinned to an immutable commit and artifact manifest. Its scope includes:

- Agda dependency and postulate audit;
- finite/model versus continuum claim separation;
- Clifford/Spin, CCR, Einstein, constraint, and UV proof obligations;
- all blocking findings and their resolutions.

The reviewer must disclose authorship, collaboration, financial, and supervisory conflicts.

## 7. Independent physics review and replication

The same module requires:

- a distinct independent physics reviewer;
- review of observable semantics, units, accepted limits, numerical adequacy, and experimental falsifiability;
- a third independent replication lead;
- fresh environment, dataset, command, and expected-output manifests;
- artifact-hash comparison;
- negative and failure-case reproduction;
- no private author-only inputs.

The mathematics reviewer, physics reviewer, and replication lead must be distinct and review/replicate the same pinned commit.

## Strict terminal integration

`StrictTerminalGRQuantumProof` now requires:

```text
StrictPhysicalGRQuantumCorrespondence
```

rather than only the earlier generic `PhysicalGRQuantumCorrespondence` record.

The new strict empirical record retains the legacy surface for compatibility but additionally requires all detailed lanes and coherence among:

```text
calibration
  -> accepted limits
  -> matched-quality benchmarks
  -> preregistered prediction
  -> independent mathematics review
  -> independent physics review
  -> independent replication
```

It also requires one theory revision and one parameter manifest across all receipts, no circular use of the target claim, and retention of adverse results.

## Executable receipt validation

`scripts/validate_gr_quantum_empirical_receipt.py` validates a completed JSON receipt. It fails closed on:

- missing calibrated observables;
- placeholder units, datasets, hashes, or references;
- missing accepted limits or continuum authority;
- error above declared tolerance;
- unmatched benchmark quality;
- missing held-out/leakage/resource/independent-rerun evidence;
- equal DASHI and reference prediction values;
- missing preregistration or rejection criteria;
- shared reviewer identities;
- review commits that differ from the theory commit;
- hidden adverse outcomes;
- universal-superiority or Theory-of-Everything promotion.

The validator checks receipt structure and coherence. It cannot determine whether external data or reviewer declarations are truthful; pinned artifacts and public review remain necessary.

## Current sharp status

Implemented now:

- complete typed seven-lane validation architecture;
- strict terminal integration;
- source maps to existing repository owners;
- finite/model adapters;
- review and replication request packets;
- fail-closed JSON validator and tests;
- focused Agda and Python CI.

Still externally required:

- actual measured calibration datasets;
- continuum/asymptotic limit proofs for the selected physical theory;
- completed matched-quality solver runs;
- one derived quantitative physical prediction;
- independent mathematical review;
- independent physics review;
- independent replication.

No author-authored object is labelled independent merely because it fits the record type.
