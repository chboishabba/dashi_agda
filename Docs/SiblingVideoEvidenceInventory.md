# Sibling Video Evidence Inventory

This inventory records the video, GIF, frame, and codec diagnostics found in
the sibling `dashifine` and `dashitest` repos. These artifacts are useful
engineering evidence for continuity, regime, codec, and rollout behavior. They
are not Agda theorem authority in this repo until a future local receipt binds
the trace, observation map, metric, admissibility law, rerun command, input
digest, and output digest.

## dashifine

`../dashifine` does not currently contain local `.mp4`, `.webm`, `.avi`, or
`.mov` artifacts in the audited paths. Its moving-image evidence is GIF and
frame-sequence based.

- `../dashifine/26_hepdata_contraction_animation.py`
  animates coefficient contraction flow over an alpha sweep and writes
  `contraction_gifs/*_coeff_contraction.gif` plus PCA CSV outputs. It
  visualizes the script's even-projection/shrinkage model. It does not prove
  HEP adequacy, provider provenance, comparison-law acceptance, or promotion.
- `../dashifine/41_viz_cone_monotone.py`
  animates `Q(delta s)` from `closure_embedding_per_step.csv` and `G_mask3.npy`.
  It is a visual diagnostic for cone quantity over steps. Certified pass/fail
  evidence belongs to `scripts/regime_test.py`, not to the GIF alone.
- `../dashifine/42_viz_closure_flow.py`
  emits `viz_closure_flow.gif` from closure embeddings and visualizes PCA
  trajectories and attractor basins. It is visual only.
- `../dashifine/43_viz_ultrametric_tree.py`
  emits `viz_ultrametric_tree.gif` from ternary lens-state LCP distances. It
  visualizes an MDS embedding and does not prove an ultrametric theorem.
- `../dashifine/44_viz_ultrametric_grid.py`
  emits `viz_ultrametric_grid.gif`, combining shell, orbit, bin, and attractor
  colorings. Its classifications are diagnostic outputs of the script choices.
- `../dashifine/26_rotate_vidk.py`
  generates exploratory GIFs for synthetic 4D field/topology views, including
  `invariant_Delta_m_bounds_-1_1.gif`,
  `invariant_sigma_Delta_m_hsv_bounds_-1_1.gif`,
  `betti012_over_theta.gif`, `persistence_surrogate_filtration.gif`, and
  `ternary_kernel_padic_residue.gif`.
- `../dashifine/newtest/grayscott_krr.py`
  can export rollout GIFs with `--rollout_gif_steps`,
  `--rollout_gif_stride`, and `--rollout_gif_fps`. This is an
  operator-learning benchmark visualization, not DASHI physics closure.

The current repo-local validation surface for the dashifine closure embedding
is still `scripts/regime_test.py cone ... --preset dashifine-closure-embedding`.
The GIFs can illustrate that surface, but they do not replace it.

## dashitest

`../dashitest` contains the stronger video-side evidence: codec scripts,
Vulkan/VAAPI preview paths, live-sheet recording scripts, existing MP4 smoke
artifacts, and tree-diffusion metrics.

- `../dashitest/compression/triadic_pipeline.md` and
  `../dashitest/compression/video_bench.py`
  document and implement a triadic video compression experiment. The runner
  uses `ffprobe`, decodes frames with `ffmpeg`, computes CPU/JAX codec stats,
  and can dump balanced-ternary planes:
  `python compression/video_bench.py path/to/video.mp4 --frames 120 --dump-planes outdir`.
  This proves the codec benchmark path exists; it does not prove visual
  correctness, GPU parity, or Agda closure.
- `../dashitest/vulkan/README.md` and
  `../dashitest/vulkan/video_bench_vk.py`
  document the Vulkan/VAAPI video benchmark path, including:
  `python vulkan/video_bench_vk.py path/to/video.mp4 --frames 240 --vaapi`.
  `../dashitest/vulkan/vk_context.txt` records a real Pixel 9 run with 475
  frames at 1920x1080 decoded through VAAPI. This is execution evidence for
  the preview path, not zero-copy or compression-kernel correctness.
- `../dashitest/vulkan/VAAPI_ZERO_COPY.md` and
  `../dashitest/vulkan/symbol_stream_stub.py`
  document dmabuf/symbol-stream scaffolding. The stated goal is a buffer and
  interop contract, not codec semantics.
- `../dashitest/vulkan_compute/compute_image_preview.py`
  exposes `--record-video`, `--record-out`, and `--record-fps`; it records raw
  RGBA frames through an `ffmpeg` pipe.
- `../dashitest/dashilearn/run_live_sheet.sh` records `sheet.mp4`.
  `../dashitest/dashilearn/run_tree_live_sheet.sh` records
  `tree_diffusion_<timestamp>.mp4`.
- Existing smoke artifacts include `../dashitest/sheet.mp4`,
  `../dashitest/sheet_20260108T021713Z.mp4`,
  `../dashitest/sheet_20260108T040701Z.mp4`, and
  `../dashitest/tree_diffusion_20260108T145922Z.mp4`. They prove the recording
  path emitted playable MP4 containers; their short durations make them smoke
  artifacts, not strong behavioral evidence.
- `../dashitest/docs/tree_diffusion_benchmark.md` and
  `../dashitest/tree_diffusion_bench.py` define the ultrametric transport
  benchmark and live-sheet/plane-dump surfaces. One audited metric artifact,
  `../dashitest/outputs/tree_diffusion_metrics_20260108T055548Z.json`, records
  `tree_rollout_mse = 4.246448141002339e-06` and
  `rbf_rollout_mse = 2.155684319973986e-05`.

## Boundary

The correct paper and repo claim is:

Sibling video evidence exists. It is executable and partly recorded, but it is
diagnostic evidence only. It becomes repo-proof here only after it is ported
into a DASHI-local receipt that fixes the trace source, observation map, metric,
admissibility law, rerun command, input digest, output digest, and comparison or
promotion boundary.
