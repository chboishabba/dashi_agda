# Prototype Runner Contract

This is the minimal runnable contract for the reduced numerical prototype that ties
the Dashi-observable interface to a surrogate response layer.

## 1. Input
- `state.json` (or equivalent trace) describing a single Dashi step: include the Δ vector,
  coarse head (projected vector), and any metadata required by the observable extraction.
- Optional `config.yaml` with symbolic parameters for `g⋆`, saturation scale `Q_s`, and GBW parameters.
- Example inputs should be emitted from the canonical shift geometry /
  admissibility path where possible, rather than authored as freehand JSON.
  For the current prototype that means:
  - one canonical shell-1 state sourced from
    `DASHI/Geometry/ShiftLorentzEmergenceInstance.agda`
    (`canonicalShiftStateWitness`)
  - one or more admissible perturbation templates that preserve the same
    coarse-head basin condition used by `ShiftInBasin`

## 2. Pipeline
1. **Observable extraction** – compute:
   * `delta_defect` (Δ channel intensity)
   * `promoted_D0` (clean observable from defect channel)
   * `density_proxy g*` (MDL-inferred quantity from the defect)
   * `sat_proxy Qs` (saturation-scale placeholder)
2. **Surrogate response** – feed the vector `(g*, Qs, promoted_D0)` into a GBW-style response
   function (see `Docs/SaturationLayer.md`) that returns a `predicted_yield` and `confidence` flag.
3. **Structured output** – emit JSON `{ "predicted_yield": ..., "trace_id": ..., "flags": {...} }`.
4. **Explanation scorecard** – compute a non-fitting internal score from:
   * normalized surrogate residual
   * MDL burden
   * confidence penalty
   This score is for comparing explanatory efficiency inside the surrogate
   stack. It is not an empirical fit score.

## 3. Contract
- The runner must be invocable as a CLI (e.g., `python prototype_runner.py --state state.json`).
- It should accept placeholder parameters but not perform data fitting.
- The code should be modular so future lanes can plug in real numeric models (GBW, IPsat, rcBK) as replacements for the surrogate response step.
- A companion batch runner should be able to consume multiple state files and
  emit a small prediction matrix for cross-channel and cross-model inspection.
- A companion state emitter should be able to materialize those example state
  files from named Dashi shift-path sources so the prototype examples have
  explicit provenance.
- The matrix and comparison entrypoints should automatically refresh those
  canonical emitted example files when they are missing or older than the
  emitter script, while leaving arbitrary user-provided state files alone.
- The comparison surfaces should expose a shared non-fitting explanation
  scorecard so “better explanation” has one repo-local meaning.

## 4. Notes
- Keep evaluation deterministic and explainable; the prototype serves to demonstrate how Dashi observables produce structured predictions.
- Logging should record the choice of observables and surrogate parameters without needing real datasets.
- Model comparisons should be explanatory only. The runner layer must not
  collapse “cleaner explanation” into “physically preferred channel.”
