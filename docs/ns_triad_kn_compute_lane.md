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

python3 scripts/ns_triad_kn_schur_finite_shell_audit.py
```

These are smoke instructions only. They do not assert any current result.
