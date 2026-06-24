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
- `scripts/ns_triad_kn_sparse_schur_scaling.py`
- `scripts/ns_triad_kn_sparse_schur_scaling_fit.py`
- `scripts/ns_triad_kn_external_paper_bridge_audit.py`
- `scripts/check_ns_triad_kn_exact_identity_scan.py`
- `scripts/check_ns_triad_kn_tail_progression_scan.py`
- `scripts/check_ns_triad_kn_lobpcg_scan.py`
- `scripts/check_ns_triad_kn_eigen_tail_adversary_scan.py`
- `DASHI/Physics/Closure/NSTriadKNMixedTailSchurScalingReceipt.agda`
- `DASHI/Physics/Closure/NSTriadKNMixedTailProofObligationMapReceipt.agda`
- `DASHI/Physics/Closure/NSTriadKNMixedTailBKMProjectionSmallnessReceipt.agda`
- `DASHI/Physics/Closure/NSFieldsACLExternalSchurResidueBridgeReceipt.agda`
- `DASHI/Physics/Closure/NSTriadKNMixedTailACLSchurResidueProofPlanReceipt.agda`
- `DASHI/Physics/Closure/NSShahmurovAxisymmetricReductionExternalReceipt.agda`
- `docs/ns_triad_kn_shortest_path.md`
- `docs/ns_triad_kn_acl_schur_residue_bridge.md`
- `docs/ns_triad_kn_LFT_operator_norm_acl_proof_plan.md`
- `TODO.md`

S:
- The lane is currently documented as candidate-only and fail-closed.
- The external Fields ACL paper is now tracked as a candidate-only carrier for the
  Schur-residue bridge, and the Shahmurov reduction paper is tracked as a
  candidate-only endpoint-reduction carrier.
- The proof-plan note now pins the next analytic target to the ACL-compatible
  `L_FT^+` operator-norm estimate.
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
  The shell-6 v3 correction reclassifies this receipt into the three-way branch:
  finite-shell, dominant escaping top-shell, or mixed-tail broad eigenmode.
  For this batch the evidence points to the mixed-tail broad eigenmode branch:
  the eigenvector has high tail mass beyond cutoff `K=4`, but its largest shell
  component remains shell `1`, so the remaining proof work must separate tail
  mass from coherence, Schur structure, and residence.
- `triad_sample_limit` is receipt sample materialization only. It does not truncate
  the matvec operator; receipts now expose `operator_triad_count`,
  `operator_selected_mode_count`, zero-degree counters, and
  `triad_sample_limit_scope = receipt_samples_only`.
- The remaining open proof items are the negative-frame coercivity, spanning, and
  Biot-Savart frame-equidistribution obligations.
- The 2026-06-24 sparse-Schur scaling lane records top-tail forced rows
  `N=6,8,10,12`, all candidate-only.  The fitted summary is
  `scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_sparse_schur_scaling_fit_20260624/summary.json`.
  The current canonical read is:
  `R_tail > c0` in all four rows, `q_gap > 0` in all four rows,
  `q_gap ~= N^-2.198`, `D ~= N^1.985`, and `D*q_gap` is approximately stable
  with mean about `4.16e-3`.  This supports the candidate lemma name
  `MixedTailSchurGapDissipationScale`, not a theorem.
- Corrected caution: the BKM-tail projection squared fraction is tiny across
  the four rows and sharply smaller at `N=12`, but it is not monotone from
  `N=6` to `N=8`.  The cross-`L_neg` fraction is remarkably stable in the
  forced-tail family, but that stability is still finite-shell telemetry, not
  a structural theorem.
- `DASHI/Physics/Closure/NSTriadKNMixedTailProofObligationMapReceipt.agda`
  records the next proof obligations as candidate-only dependencies:
  `MixedTailSchurGapDissipationScale`, `TailSubspaceCoercivity`,
  `BKMProjectionSmallness`, and `ResidenceTimeExclusion`.  The map records
  input telemetry, target statement, and missing analytic/PDE bridge for each
  row, while keeping theorem, full-NS, BKM-exclusion, and Clay promotion false.

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
  The shell-6 v3 smoke makes the gap sharper: the lane now distinguishes
  finite-shell, dominant escaping top-shell, and mixed-tail broad eigenmode
  cases, and the latter needs coherence, Schur, and residence arguments rather
  than a simple tail-mass or dominant-shell readout.
- After the N=6,8,10,12 sparse-Schur scaling receipt, the highest-priority
  analytic target is the lower-bound shape
  `q_gap(N) >= N^(-2-epsilon)` paired with `D(N) ~ N^2`, or equivalently a
  residence-compatible lower bound on `D(N) * q_gap(N)`.  The open bridges are
  uniform tail coercivity, structural BKM projection smallness, the
  finite-dimensional-to-PDE trajectory bridge, and BKM residence assembly.

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
