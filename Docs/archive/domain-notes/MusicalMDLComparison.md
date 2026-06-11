## Musical MDL Comparison

`scripts/musical_symmetry_mdl.py` now exposes a comparison entry point that runs the `symmetry_bias` and `mdl` update rules using the same random seed and configuration. Use `--compare` to emit a combined JSON report that keeps both basin statistics for shared seeds, enabling side-by-side inspection of symmetry-biased attractors and the MDL optimizer under identical initialization.

The comparison payload nests the original `basin_scan` reports under `runs.symmetry_bias` and `.mdl` so you can reuse the existing summary/attractor layout, while the top-level `comparison` block records the shared parameters. Use this for regression tests that track how biased dynamics shift once ML-inspired compression is disabled.
