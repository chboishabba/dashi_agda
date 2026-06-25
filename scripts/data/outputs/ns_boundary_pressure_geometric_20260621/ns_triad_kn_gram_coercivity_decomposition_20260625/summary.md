# NS Triad K_N(A) Gram Coercivity Decomposition

- status: `ok`
- candidate only: `True`
- theorem promoted: `False`
- full NS promoted: `False`
- BKM exclusion proved: `False`
- Clay promoted: `False`

## Exactness Anchor

- exact operator name: `exact_scripted_pair_incidence_operator`
- exact theorem target: `||L_FT,script^N||_op <= C / N`
- sampled-script match: `True`

## Rows

| N | profile | lambda_min | N*lambda_min | diag | offdiag | diag-offdiag | coherence_mu | support | verdict |
|---:|---|---:|---:|---:|---:|---:|---:|---|---|
| 6 | forced_tail_K5_eta_0.250 | 0.167220782344 | 1.00332469406 | 0.183461289298 | 0.0162406055106 | 0.167220683787 | 0.0885233368455 | [1, 6, 5] | coercivity_plausible |
| 8 | forced_tail_K7_eta_0.250 | 0.167401935258 | 1.33921548206 | 0.182983724653 | 0.0155819290523 | 0.167401795601 | 0.0851547266397 | [8, 7, 1] | coercivity_plausible |
| 10 | forced_tail_K9_eta_0.250 | 0.166811264279 | 1.66811264279 | 0.182014827305 | 0.0152037611773 | 0.166811066127 | 0.0835303442169 | [10, 9, 1] | coercivity_plausible |
| 12 | forced_tail_K11_eta_0.250 | 0.158009233866 | 1.89611080639 | 0.172738036732 | 0.0147290490799 | 0.158008987652 | 0.0852681283091 | [12, 11, 1] | coercivity_plausible |

## Lemma Split

| Lemma | Sampled evidence | Theorem closed |
|---|---|---|
| K_N(A) exactness | True | False |
| Diagonal mass lower bound | True | False |
| Coherence / off-diagonal control | True | False |
| Admissible profile condition | False | False |

## Readout

Gram-coercivity decomposition readout: the exact scripted pair-incidence object remains canonical (sampled-script match = True), and the sampled shell rows keep lambda_min positive with N*lambda_min spanning 1.00332..1.89611. On these rows the diagonal-minus-cross Gram margin spans 0.158009..0.167402 while the coherence proxy spans 0.0835303..0.0885233. The dominant eigen support remains mixed rather than single-shell (N=6:[1, 6, 5], N=8:[8, 7, 1], N=10:[10, 9, 1], N=12:[12, 11, 1]). This is candidate-only decomposition evidence for the live c / N target; it does not close the analytic min-max lower bound.

## Stability Stats

- N*lambda_min: `{'count': 4, 'min': 1.0033246940629643, 'max': 1.8961108063878611, 'mean': 1.4766909063267373, 'sample_stdev': 0.3896709710124518, 'relative_range': 0.6045856370482423}`
- coherence_mu: `{'count': 4, 'min': 0.08353034421685994, 'max': 0.08852333684550705, 'mean': 0.08561913400278115, 'sample_stdev': 0.0020925515618803645, 'relative_range': 0.058316317804439854}`
- diag_minus_offdiag: `{'count': 4, 'min': 0.1580089876521116, 'max': 0.16740179560071888, 'mean': 0.16486063329184997, 'sample_stdev': 0.0045744427871586965, 'relative_range': 0.0569742318772933}`
