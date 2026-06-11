# Drosophila Hemibrain Artifact Manifest

Purpose: record selected `../dashiBRAIN` evidence as non-promoting Brain lane
receipts for `dashi_agda`.

This manifest is a checksum and boundary ledger only. It does not promote the
Brain lane to local closure, biological recovery, physics evidence, or a
multiscale theorem.

## Source

- source repo: `../dashiBRAIN`
- source docs:
  - `README.md`
  - `docs/formal_axioms.md`
  - `docs/gauge_choices.md`
  - `docs/sprint-03.md`
  - `docs/sprint-04.md`
  - `CHANGELOG.md`
- checksum command: `sha256sum` run from `dashi_agda`

## Selected Artifacts

Only the following artifacts were checksummed for this receipt pass.

| Artifact | SHA-256 |
| --- | --- |
| `outputs/defect_curve_20260120-142843.csv` | `e24a19f7fb01fe423b669971e3bab45612a74637773df7b5787063601215e9f6` |
| `outputs/defect_curve_20260120-142843_state.csv` | `12fb1e74a6e717f1ef339301a66f1aea5a7afbf0c6aa9fa9fc7550af30dd4301` |
| `outputs/defect_curve_20260120-142843_defect_nodes.csv` | `ceadc69cd41a7107b5ceca5de4d810d739dc7d3e9b3db803e8bc65f490f575bc` |
| `outputs/sprint3_default_geometry_summary.json` | `15742e907ba54d63b9a902141d2ac98c808805687311556a2344d883d5b6ab83` |
| `outputs/defect_curve_coarse_random_blocks_20260120-150400.csv` | `0b5bf6f15c810f66335f9a44c34ffaca77566ed945bf41995055640de982d2a9` |
| `outputs/defect_curve_coarse_degree_binned_20260120-151536.csv` | `0b5bf6f15c810f66335f9a44c34ffaca77566ed945bf41995055640de982d2a9` |
| `outputs/defect_roi_20260120-153259.csv` | `0b5bf6f15c810f66335f9a44c34ffaca77566ed945bf41995055640de982d2a9` |
| `outputs/defect_radius_r1_20260120-153948.csv` | `0b5bf6f15c810f66335f9a44c34ffaca77566ed945bf41995055640de982d2a9` |
| `outputs/defect_radius_r2_20260120-154023.csv` | `0b5bf6f15c810f66335f9a44c34ffaca77566ed945bf41995055640de982d2a9` |

## Receipt Interpretation

Positive, bounded receipt:

- baseline hemibrain single-scale sparse degree-corrected run converges with
  defect trace `633, 42, 2, 0`
- Sprint 3 records single-scale closure and gauge robustness across tested
  deadzones and the raw baseline gauge
- geometry summary records `179907` nodes, `7084254` edges, final state
  `{+1: 137901, 0: 42006, -1: 0}`, and `8` +1 components

Negative receipt:

- selected coarse-grain curves for random blocks, degree-binned blocks, ROI,
  radius `r=1`, and radius `r=2` are all the one-step curve `0`
- these runs support a multiscale persistence obstruction: the observed
  neutral/defect structure is not established as persistent across the selected
  coarse-grainings

## Non-Claim Boundary

These receipts do not assert:

- full Drosophila neuroscience recovery
- biological interpretation of components
- a local `dashi_agda` Brain closure theorem
- multiscale latent-structure persistence
- promotion of the Brain lane into physics closure or empirical adequacy
