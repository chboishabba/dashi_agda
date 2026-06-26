# NS Triad Exact Pair-Incidence Row/Column Audit

- status: `ok`
- candidate only: `True`
- theorem promoted: `False`
- full NS promoted: `False`
- BKM exclusion proved: `False`
- Clay promoted: `False`

## Fits

- forced row fit: `{'fit_available': True, 'point_count': 4, 'slope': 0.022231863439906754, 'decay_exponent_if_y_decays': -0.022231863439906754, 'C': 0.011015691598945762, 'points': [{'x': 6.0, 'y': 0.011469115826422354}, {'x': 8.0, 'y': 0.011498313799951723}, {'x': 10.0, 'y': 0.011658669695747196}, {'x': 12.0, 'y': 0.01161007913702235}]}`
- forced column fit: `{'fit_available': True, 'point_count': 4, 'slope': -1.8419624572467745, 'decay_exponent_if_y_decays': 1.8419624572467745, 'C': 0.009152589084452597, 'points': [{'x': 6.0, 'y': 0.00034085935063711564}, {'x': 8.0, 'y': 0.00019004849169743486}, {'x': 10.0, 'y': 0.0001398832271517856}, {'x': 12.0, 'y': 9.170933372028357e-05}]}`
- forced Schur fit: `{'fit_available': True, 'point_count': 4, 'slope': -0.9098652969034343, 'decay_exponent_if_y_decays': 0.9098652969034343, 'C': 0.010041020799012793, 'points': [{'x': 6.0, 'y': 0.0019772089856603904}, {'x': 8.0, 'y': 0.0014782547800513367}, {'x': 10.0, 'y': 0.0012770482924846045}, {'x': 12.0, 'y': 0.0010318685100806618}]}`
- adversarial row fit: `{'fit_available': True, 'point_count': 4, 'slope': -2.0811972121228446, 'decay_exponent_if_y_decays': 2.0811972121228446, 'C': 0.1728337360915966, 'points': [{'x': 6.0, 'y': 0.004119224657014591}, {'x': 8.0, 'y': 0.002302460387360837}, {'x': 10.0, 'y': 0.0014455177535300703}, {'x': 12.0, 'y': 0.0009711855405184119}]}`
- adversarial column fit: `{'fit_available': True, 'point_count': 4, 'slope': -0.9582838546919872, 'decay_exponent_if_y_decays': 0.9582838546919872, 'C': 0.009999632396412429, 'points': [{'x': 6.0, 'y': 0.001779464024250605}, {'x': 8.0, 'y': 0.001382542572444379}, {'x': 10.0, 'y': 0.0011049335405407886}, {'x': 12.0, 'y': 0.0009163894999913271}]}`
- adversarial Schur fit: `{'fit_available': True, 'point_count': 4, 'slope': -1.5197405334074154, 'decay_exponent_if_y_decays': 1.5197405334074154, 'C': 0.04157251287346631, 'points': [{'x': 6.0, 'y': 0.002707399505976815}, {'x': 8.0, 'y': 0.0017841663338638394}, {'x': 10.0, 'y': 0.001263804197382865}, {'x': 12.0, 'y': 0.00094338975607883}]}`

## Forced-Tail Decomposition

| N | row sup | worst-row active tails | mean active row entry | column sup | worst-column active finite k | mean active column entry |
|---:|---:|---:|---:|---:|---:|---:|
| 6 | 0.0114691 | 977 | 1.17391e-05 | 0.000340859 | 20 | 1.7043e-05 |
| 8 | 0.0114983 | 1810 | 6.35266e-06 | 0.000190048 | 20 | 9.50242e-06 |
| 10 | 0.0116587 | 2984 | 3.90706e-06 | 0.000139883 | 26 | 5.38012e-06 |
| 12 | 0.0116101 | 4276 | 2.71517e-06 | 9.17093e-05 | 22 | 4.16861e-06 |

## Adversarial Geometry Sweep

| N | row sup | column sup | worst-column active finite k |
|---:|---:|---:|---:|
| 6 | 0.00411922 | 0.00177946 | 476 |
| 8 | 0.00230246 | 0.00138254 | 1363 |
| 10 | 0.00144552 | 0.00110493 | 2758 |
| 12 | 0.000971186 | 0.000916389 | 5095 |

## Verdict

Row/column audit readout: under the checked exact-script normalization, the forced-tail family has row_sum_sup ~ N^0.022 and column_sum_sup ~ N^-1.842, while the uniform-geometry adversarial family has row_sum_sup ~ N^-2.081 and column_sum_sup ~ N^-0.958. So the current data does not support the alternate claim that the exact-script column supremum is O(1) for the canonical checked object. Instead, the forced-tail rows are carried by a nearly constant worst-row mass with active-count slope 2.143 and mean-active-entry slope -2.121, while the forced-tail columns are carried by an almost constant worst-column incidence count with slope 0.249 and a decaying mean-active-entry slope -2.091. This preserves the sampled N^-1 Schur scale but does not by itself prove a profile-independent C/N theorem.

- theorem gate closed: `False`
- exact-script O(1) column-claim validated: `False`
