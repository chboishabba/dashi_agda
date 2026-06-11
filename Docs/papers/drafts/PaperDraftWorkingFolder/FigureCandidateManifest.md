# Paper 1 Figure Candidate Manifest

Status: curated visual-provenance surface; non-promoting.

This manifest records the local figure pack assembled for the Paper 1 origins
appendix. The figures are visual intuition surfaces for traversal, refinement,
ultrametric diagnostics, and sibling engineering experiments. They are not
Agda theorem authority, empirical closure, or promotion receipts.

Promotion rule: a sibling visual becomes proof-relevant only after a
DASHI-local receipt fixes the trace source, observation map, metric,
admissibility law, rerun command, input digest, output digest, and comparison
or promotion boundary.

## Local Figure Pack

Stable repo copies live in:

- `Docs/Images/paper1-origin-figures/`
- `Docs/papers/drafts/PaperDraftWorkingFolder/figures/paper1-origin-figures/`

The second path contains the LaTeX-facing figure copies:

- `dashifine_ultrametric_tree_frame0.png`
- `dashifine_ultrametric_grid_frame0.png`
- `dashitest_tree_diffusion_rollout_mse.png`
- `dashitest_tree_diffusion_tree_band_quotient.png`
- `fracdash_rank4_basin_branch_density.png`
- `dashirtx_refinement_frame_100.png`
- `paper1_origin_diagnostics_plate.png` remains available as an archived
  composite but is no longer the preferred manuscript figure.

## Curated Assets

| Local copy | Source artifact | Role in Paper 1 | Boundary |
|---|---|---|---|
| `dashifine_ultrametric_tree_frame0.png` | `../dashifine/viz_ultrametric_tree.gif[0]` | Still from an LCP-depth ultrametric embedding diagnostic. | Euclidean embedding of tree distances; not an ultrametric proof. |
| `dashifine_ultrametric_grid_frame0.png` | `../dashifine/viz_ultrametric_grid.gif[0]` | Still from a 2x2 ternary shell/orbit/bin/attractor diagnostic. | Script classification diagnostic only. |
| `dashitest_tree_diffusion_rollout_mse.png` | `../dashitest/outputs/tree_diffusion_metrics_20260108T055548Z_rollout_mse.png` | Rollout-error comparison for tree diffusion versus RBF baseline. | One sibling diagnostic run; no video-continuity receipt. |
| `dashitest_tree_diffusion_tree_band_quotient.png` | `../dashitest/outputs/tree_diffusion_metrics_20260108T055548Z_rollout_tree_band_quotient.png` | Tree-band quotient leakage/transport diagnostic. | Diagnostic metric surface only. |
| `dashitest_tree_diffusion_band_planes.png` | `../dashitest/outputs/tree_diffusion_band_planes/summary/bands_by_time_tiled_4wide_stacked_1x3.png` | Visual bridge between tree detail bands and codec-sheet intuition. | Engineering visualization, not codec correctness. |
| `fracdash_rank4_basin_branch_density.png` | `../FRACDASH/benchmarks/results/rank4-dataset-latest.branch-density-view.basin.branch-density.png` | Rank-4 branch-density projection illustrating traversal-density basins. | FRACDASH projection diagnostic; not general DASHI theorem evidence. |
| `dashirtx_refinement_frame_100.png` | `../dashiRTX/outputs_pda/refine_frame_100.png` | Adaptive refinement toy frame from a separate physically-based raytracing / MDL sparse light-transport prototype. | Visual provenance only; separate from DASHI Agda, Paper 1 closure, and the adelic Sobolev bridge. |
| `dashicfd_v4_t3000_compare.png` | `../dashiCFD/outputs/v4_t3000_compare.png` | Field/reconstruction/residual intuition candidate. | Analogy/provenance only; not a Paper 1 field-equation result. |
| `paper1_origin_diagnostics_plate.png` | Composite of six selected assets above. | Archived appendix plate; superseded in the manuscript by three larger figure groups. | Composite plate inherits all diagnostic-only boundaries. |

## Metric Context

The tree-diffusion figure pack is tied to:

- `../dashitest/outputs/tree_diffusion_metrics_20260108T055548Z.json`
- `tree_rollout_mse = 4.246448141002339e-06`
- `rbf_rollout_mse = 2.155684319973986e-05`
- `tree_rollout_tree_band_q_mse = 2.2923454540607163e-11`
- `rbf_rollout_tree_band_q_mse = 9.034794028524742e-11`

The same run has bridge metrics where the RBF baseline is slightly better on
some bridge surfaces, so the safe caption is not "tree methods always win."
The safe caption is that the sibling run gives a concrete visual and metric
surface for ultrametric/tree transport diagnostics.

## SHA-256 Digests

```text
2bedf187d45bd47c46249d69ededbd20a48b78c1511f500c0bad8b4a4817aad9  dashitest_tree_diffusion_rollout_mse.png
3d529a6deb1c77684ddfacae697cf687ff35dc353a3dfefcf348ba7bfbe78942  dashifine_ultrametric_tree_frame0.png
418e8f4013866dfaa6e91412cee0ef1f3f390db8bbe636f7a2bf00cf46888494  dashitest_tree_diffusion_tree_band_quotient.png
6cc19c83e83a9117f76f29e1eee7a3ad3763f76f1293afc9eece09561b8f8d8f  fracdash_rank4_basin_branch_density.png
795376811f861ae26c2110472ab77babfec3336b5018fa7225ae6520eb6bae9f  dashitest_tree_diffusion_band_planes.png
83b3669a4cb90832b7d0f2e5294101d09f1d1ffc29e0a0a081fd431a8f94402f  paper1_origin_diagnostics_plate.png
9d13d0999785519c785b76b27d95a1545d51fd7689aac6d51d57ebe1dee5a043  dashicfd_v4_t3000_compare.png
a28b4cc954a58fe524c4848654153658bc976308066fd83b26d4e70e047d0d09  dashirtx_refinement_frame_100.png
b8d21a8790e0d97f19f01bd8b1a026be830f728201c0f5284f7c5105c7932a08  dashifine_ultrametric_grid_frame0.png
```

## Excluded Or Deferred

- Dashitest MP4 files remain smoke artifacts because they are very short
  playable-container checks.
- Dashifine HEP persistence and Lyapunov plots remain high-risk empirical
  diagnostics and are not part of the current public-facing origins plate.
- UFT-C/SWAR has strong text provenance but no polished local figure yet.
  A future figure should be generated as a clean explanatory diagram rather
  than extracted from a noisy experiment screenshot.
