# NS Triad K_N Compute Lane

O:
- Worker lane owner: this repo-local compute note.
- Approval boundary: candidate-only, fail-closed, no Clay or theorem promotion.

R:
- Record the current `K_N` compute-lane status without re-framing it as `N_eff`.
- Name the exact remaining proof obligations still open on the lane.
- Show how to run the tail and eigen-tail smoke commands with `VK_ICD_FILENAMES`.

C:
- `scripts/ns_triad_kn_exact_identity_scan.py`
- `scripts/ns_triad_kn_tail_progression_scan.py`
- `scripts/ns_triad_kn_lobpcg_scan.py`
- `scripts/ns_triad_kn_eigen_tail_adversary_scan.py`
- `scripts/ns_triad_kn_schur_finite_shell_audit.py`
- `scripts/ns_triad_kn_external_wall1_csv_ingest.py`
- `scripts/check_ns_triad_kn_external_wall1_csv_ingest.py`
- `scripts/ns_triad_kn_progression_artifact_audit.py`
- `scripts/run_ns_triad_kn_eigen_tail_progression_batch.py`
- `scripts/ns_triad_kn_batch_manifest_summary.py`
- `scripts/check_ns_triad_kn_exact_identity_scan.py`
- `scripts/check_ns_triad_kn_tail_progression_scan.py`
- `scripts/check_ns_triad_kn_lobpcg_scan.py`
- `scripts/check_ns_triad_kn_eigen_tail_adversary_scan.py`
- `TODO.md`

S:
- The lane is currently documented as candidate-only and fail-closed.
- The corrected positive-subspace identity is audited on the active Wall 1 carrier as
  `L_signed_norm = I - 2 K_N`.
- The lane is not promoted, and the repo text keeps the old signed route as legacy/non-canonical.
- The live adversary is now eigenmode tail escape, not profile tail mass alone.
- The external Wall1 CSV ingest records 240 rows across five uploaded CSVs with one explicit
  progression artifact and zero `danger=true` rows in the N=3 eigenmode file.
- The 2026-06-23 Vulkan batch smoke for shells 4 and 5 returned checker-ok receipts,
  `tail_escape_candidate_count = 0` for both shells, and `gpu_kn_authority = false`.
- The corrected 2026-06-23 Vulkan shell-6 compact batch with explicit triad sample
  metadata and tolerant tail-threshold classification returned checker-ok,
  `lambda_min ~= 0.19363`, worst eigen shell `1`, worst shell mass `~0.454`,
  `operator_zero_degree_mode_count = 0`, and `tail_escape_candidate_count = 1`.
  This is a mass-threshold tail candidate, not a dominant-top-shell eigenmode:
  the eigenvector has high tail mass beyond cutoff `K=4`, but its largest shell
  component remains shell `1`.
- `triad_sample_limit` is receipt sample materialization only. It does not truncate
  the matvec operator; receipts now expose `operator_triad_count`,
  `operator_selected_mode_count`, zero-degree counters, and
  `triad_sample_limit_scope = receipt_samples_only`.
- The remaining open proof items are the negative-frame coercivity, spanning, and
  Biot-Savart frame-equidistribution obligations.

L:
- audit -> candidate surface -> proof lemma -> validated lane -> promoted claim
- current position: audit/candidate surface, not validated

P:
- Keep the lane as a documentation-backed candidate surface.
- Treat the exact identity scan as an empirical receipt, not as theorem closure.
- Keep the open lemma names explicit so later proof work can target them directly.

G:
- No Clay promotion.
- No theorem promotion.
- No inference from the smoke commands unless their outputs are separately checked.

F:
- The lane still lacks proofs for:
  - `NSTriadBSNegativeFrameCoercivityBoundary`
  - `NSTriadBSSpanningLemmaReceipt`
  - `NSTriadBSFrameEquidistributionBoundary`
- The Clay-relevant gap is the asymptotic theorem:
  `low lambda_min`, low/moderate `D`, and an escaping bad eigenmode cannot coexist
  along a sequence of increasing radial shells.
  The shell-6 v3 smoke makes the gap sharper: tail mass in the eigenvector can be
  high while the dominant bad shell is still low, so proof and telemetry should
  distinguish tail-mass escape from dominant-shell escape.

Smoke commands:

```bash
VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/radeon_icd.json \
  python3 scripts/ns_triad_kn_tail_progression_scan.py

VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/radeon_icd.json \
  python3 scripts/check_ns_triad_kn_tail_progression_scan.py

VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/radeon_icd.json \
  python3 scripts/ns_triad_kn_lobpcg_scan.py

VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/radeon_icd.json \
  python3 scripts/check_ns_triad_kn_lobpcg_scan.py

VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/radeon_icd.json \
  python3 scripts/ns_triad_kn_eigen_tail_adversary_scan.py

VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/radeon_icd.json \
  python3 scripts/check_ns_triad_kn_eigen_tail_adversary_scan.py

python3 scripts/ns_triad_kn_external_wall1_csv_ingest.py \
  --output-json scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_external_wall1_csv_ingest_20260623.json

python3 scripts/check_ns_triad_kn_external_wall1_csv_ingest.py \
  --input-json scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_external_wall1_csv_ingest_20260623.json \
  --output-json scripts/data/outputs/ns_boundary_pressure_geometric_20260621/check_ns_triad_kn_external_wall1_csv_ingest_20260623.json

python3 scripts/ns_triad_kn_progression_artifact_audit.py \
  --input /home/c/Downloads/wall1_progression_N3_N6.csv \
  --input /home/c/Downloads/wall1_N3_eigenmode_escape.csv \
  --input /home/c/Downloads/wall1_eigenmode_audit_N2.csv \
  --input /home/c/Downloads/wall1_constrained_adversarial.csv \
  --input /home/c/Downloads/wall1_squarewave_fork.csv \
  --output-json scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_progression_artifact_audit_wall1_20260623.json

VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/radeon_icd.json \
  python3 scripts/run_ns_triad_kn_eigen_tail_progression_batch.py \
  --shells 4,5 \
  --backend vulkan-matvec \
  --icd /usr/share/vulkan/icd.d/radeon_icd.json \
  --tail-grid-detail compact \
  --tail-grid-serialization summary

VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/radeon_icd.json \
  python3 scripts/run_ns_triad_kn_eigen_tail_progression_batch.py \
  --shells 6 \
  --backend vulkan-matvec \
  --icd /usr/share/vulkan/icd.d/radeon_icd.json \
  --tail-grid-detail compact \
  --tail-grid-serialization summary \
  --triad-sample-limit 64

python3 scripts/ns_triad_kn_batch_manifest_summary.py \
  --input scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_eigen_tail_adversary_batch_20260623_vulkan_shell6_operator_cov64_v3/ns_triad_kn_eigen_tail_adversary_batch_manifest.json \
  --output-json scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_batch_manifest_summary_20260623_vulkan_shell6_operator_cov64_v3.json

python3 scripts/ns_triad_kn_schur_finite_shell_audit.py
```

These are smoke instructions only. They do not assert any current result.
