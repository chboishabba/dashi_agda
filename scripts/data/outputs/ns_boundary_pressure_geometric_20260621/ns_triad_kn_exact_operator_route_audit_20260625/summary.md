# NS Triad Exact-Operator Route Audit

- status: `ok`
- candidate only: `True`
- theorem promoted: `False`
- full NS promoted: `False`
- BKM exclusion proved: `False`
- Clay promoted: `False`

## Gates

| Step | Target | Closed | Reason |
|---|---|---|---|
| 1 | profile-independent exact-script row/column control and ||L_FT,script^N||_op <= C / N | False | checked families scale differently; the current exact-script audit remains sampled and profile-asymmetric |
| 2 | q_gap(N) >= c_gap / N^2 via SchurResidueScale transfer | False | sampled N^2*q_gap is stable but the exact operator-to-residue theorem transfer is not closed |
| 3 | structural BKM projection smallness | False | BKM projection is telemetry-only; no structural orthogonality theorem has been recorded |
| 4 | trajectory-level residence-time exclusion | False | residence receipt still records missing analytic objects and false closure flags |

## Readout

Route audit readout: Gate 1 remains open because the checked exact-script families are asymmetric rather than profile-independent, with forced-tail row/column slopes 0.022/-1.842 and adversarial row/column slopes -2.081/-0.958. Gate 2 remains candidate-only: the sampled residue bridge keeps N^2*q_gap in 0.017..0.019, but the route still lacks a proved exact-script-to-residue transfer. Gate 3 remains open: the BKM projection telemetry is tiny and fitted by the sampled script, but it is still structural-candidate-only with projection slope -4.871. Gate 4 remains open: the residence receipt still records missing analytic objects and false closure flags, so no trajectory-level exclusion has been proved.

## Residue Scale Context

- N^2 * q_gap stats: `{'count': 3, 'min': 0.01733001861660528, 'max': 0.019027572331753617, 'mean': 0.017917511487967178}`
- D * q_gap stats: `{'count': 3, 'min': 0.004095172011266396, 'max': 0.004557249030978871, 'mean': 0.004253938806904319}`
