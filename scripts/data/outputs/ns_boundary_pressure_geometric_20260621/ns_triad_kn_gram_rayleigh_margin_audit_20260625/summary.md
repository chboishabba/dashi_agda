# NS Triad K_N(A) Rayleigh Margin Audit

- status: `ok`
- candidate only: `True`
- theorem promoted: `False`
- full NS promoted: `False`
- Clay promoted: `False`

## Rows

| N | lambda_min | Rayleigh | diag | cross | diag-cross | coherence_mu | support | entropy | mechanism | verdict |
|---:|---:|---:|---:|---:|---:|---:|---|---:|---|---|
| 6 | 0.167220782344 | 0.167220782344 | 0.183461289298 | 0.0162406055106 | 0.167220683787 | 0.0885233368455 | [1, 6, 5] | 4.82882160043 | diagonal_dominance_plus_profile_spreading | coercive_margin_plausible |
| 8 | 0.167401935258 | 0.167401935258 | 0.182983724653 | 0.0155819290523 | 0.167401795601 | 0.0851547266397 | [8, 7, 1] | 4.9826364203 | diagonal_dominance_plus_profile_spreading | coercive_margin_plausible |
| 10 | 0.166811264279 | 0.166811264279 | 0.182014827305 | 0.0152037611773 | 0.166811066127 | 0.0835303442169 | [10, 9, 1] | 5.1002753602 | diagonal_dominance_plus_profile_spreading | coercive_margin_plausible |
| 12 | 0.158009233866 | 0.158009233866 | 0.172738036732 | 0.0147290490799 | 0.158008987652 | 0.0852681283091 | [12, 11, 1] | 5.1955106455 | diagonal_dominance_plus_profile_spreading | coercive_margin_plausible |

## Dominant Shell Pairs

| N | dominant negative shell pairs | cell classification |
|---:|---|---|
| 6 | 1-6:0.469119, 1-5:0.46516, 5-6:0.0249567 | open_from_receipts |
| 8 | 1-8:0.469405, 1-7:0.466643, 7-8:0.0229856 | open_from_receipts |
| 10 | 1-10:0.470116, 1-9:0.468079, 9-10:0.0227007 | open_from_receipts |
| 12 | 1-12:0.473598, 1-11:0.468616, 11-12:0.022409 | open_from_receipts |

## Readout

Rayleigh-margin audit readout: the exact scripted pair-incidence object remains canonical (sampled-script match = True). Across the sampled rows the lowest recorded Rayleigh quotient stays positive because the diagonal Gram mass continues to exceed the cross term while coherence stays small. The support proxy remains mixed rather than single-shell (N=6:[1, 6, 5], N=8:[8, 7, 1], N=10:[10, 9, 1], N=12:[12, 11, 1]), and the dominant negative shell-pair carriers are N=6:1-6, N=8:1-8, N=10:1-10, N=12:1-12. The observed protection mechanism is ['diagonal_dominance_plus_profile_spreading']. This is candidate-only evidence and the finite sign/profile dangerous-cell classification is still open from receipts.

## Stability Stats

- lambda_min: `{'count': 4, 'min': 0.1580092338656551, 'max': 0.1674019352577181, 'mean': 0.1648608039366596, 'sample_stdev': 0.004574390832296616, 'relative_range': 0.05697352656166666}`
- diag_minus_cross: `{'count': 4, 'min': 0.1580089876521116, 'max': 0.16740179560071888, 'mean': 0.16486063329184997, 'sample_stdev': 0.0045744427871586965, 'relative_range': 0.0569742318772933}`
- coherence_mu: `{'count': 4, 'min': 0.08353034421685994, 'max': 0.08852333684550705, 'mean': 0.08561913400278115, 'sample_stdev': 0.0020925515618803645, 'relative_range': 0.058316317804439854}`
- support_size: `{'count': 4, 'min': 3.0, 'max': 3.0, 'mean': 3.0, 'sample_stdev': 0.0, 'relative_range': 0.0}`
