# PR #1242 — field-control time-order drift alias: max-cut and acceptance rule

**Cut:** 25 October 2026 (Brisbane). **Scope:** a concrete S1 scientific/instrumentation defect in the existing `S1-CSV-v1` source-replay contract. **Evidence grade:** source-written implementation, standalone local synthetic tests; no instrument, force, magnetic, VSM or gravitational observation. Existing Biot/Savart, Maxwell, NIST/JCGM measurement-uncertainty research and repo exact Fourier owners retain their authorship.

## The defect

Four paired magnetic-force tests may fill all 6 binary `coil sign × magnet polarity` design arms, yielding exact rank 5 of `[1, sign(I), sign(m), sign(I) sign(m), sign(I)^2]`. But the original source fixture recorded **every sham before active**. With a drifting force balance `F(t)=F_physics(t)+d·t` (constant linear drift slope `d`), paired subtraction yields

```
(F_active - F_sham)_i
    = ΔF_physics,i + d·(t_active,i - t_sham,i)
```

Even without an effect, `d·Δt_i` may look like field-on force. Rank of a design containing no time-order covariate cannot resolve it. `sign(I)^2` is only a coil-on indicator, **not** measured `I²R` heating or thermal lag.

## Implemented, source-bound resolution

- [`psychotronics_field_loom_reducer.py`](../../scripts/psychotronics_field_loom_reducer.py) now preserves each original active-row current (only internally) and computes `Δt_i=t_active−t_sham` from **the same hashed sensor source** already used for force/current. It audits the four active-arm combinations `(+I,+m),(-I,+m),(+I,-m),(-I,-m)` separately. The conservative linear-order requirement is, for each arm, at least one active-before-sham and at least one active-after-sham **and exact zero sum of signed time gaps**. A design that only changes arms without reversing time order is reported unbalanced.
- [`psychotronics_field_loom_source_join.py`](../../scripts/psychotronics_field_loom_source_join.py) exports `temporal_counterbalance_from_source` only where source envelopes, raw pairs, exact replay and calibration all join; it cannot be replaced with operator-entered metadata.
- [`psychotronics_field_loom_metrology.py`](../../scripts/psychotronics_field_loom_metrology.py) adds an explicit `unbalanced_active_sham_time_order_by_arm` intake obligation. A full-rank factorial cannot bypass it. The report also states the physical ceiling.
- [`test_psychotronics_field_loom_reducer.py`](../../scripts/test_psychotronics_field_loom_reducer.py) adds a deliberately biased four-pair case (all active after sham), a source-replayed 8-pair/two-session reverse-order case (four arms × two orders), and a single-timestamp perturbation. The first and perturbed design must **not** pass the time-order acceptance, while the balanced synthetic example does. All six locally authored reducer-test groups passed (0.002s), including preceding schema/identity/adversarial input tests.

**Why require the check per arm rather than in aggregate?** Opposite time orders in `(+I,+m)` cannot compensate for a drift alias in `(-I,-m)` if the physical response depends on those factors. A global-zero timing sum alone is therefore insufficient to establish even this narrow linear-drift symmetry.

## What has and has not been paid

**Paid:** deterministic timestamp-order audit at source-row identity, explicit fail-closed review gate, and a reproducible 8-pair *design* with a negative regression. Timestamp labels (and their physically correct clocks) remain unauthenticated. This is not a proof of no drift: even per-arm signed gaps cancelling exactly leaves unequal GLS weights, session-varying/nonlinear drift, hysteresis, delayed heating, magnet handling, baseline remount, covariance, non-blinded operator and thermal artefacts. A real model should include observed temperature, support vibration, sampled current waveform, recorded field, force drift baselines and (if justified) a time-dependent covariance model rather than assume this gate eliminates noise.

**Independent local test versus remote state:** local reducer source corresponds to the current patch and all six standalone tests passed. GitHub source, source-join, GLS, integrator and test readbacks are inspected and committed, but this cut **did not** execute the full GitHub checkout/Agda/CI. Physically measured effects, experiment registration, instrument authentication and independent replication remain unpaid. No extraordinary mechanism, programme/event identity or finding about a missing scientist is inferred.

**Roadmap:** S1 source consistency and temporal design are software-ready; the first *new scientific receipt* must be a real same-apparatus calibrated, randomized/counterbalanced current × magnet × sham time series with continuous force/field/temperature/vibration calibration and independently audited source metadata. Keep the original 20-scientist technical work and Egely–Vértesy VSM sample-state claims in their own experimental lanes, and reuse the already-owned Biot–Savart formalisation rather than start new kernel series.
