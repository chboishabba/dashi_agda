# SM Higgs Covariant Comparison Law

- schema: `dashi-sm-higgs-covariant-comparison-law-v1`
- row count: `4`
- baseline authority status: `fixture-not-authority`
- covariance checked: `true`
- covariant chi-square law present: `true`
- accepted authority token present: `false`
- empirical validation promoted: `false`
- Standard Model promoted: `false`

This is a non-promoting adapter-level comparison receipt. It computes
`(d - m)^T Sigma^-1 (d - m)` for the supplied baseline rows, but the
fixture baseline and adapter-level observed vectors are not authority
measurement payloads.

## Rows

- `N_j_30:log`: chi2 `85.7255018661`, dof `4`, reduced `21.4313754665`
- `N_j_30:ordinal`: chi2 `88.2782604109`, dof `4`, reduced `22.0695651027`
- `pT_yy:log`: chi2 `60.6349438172`, dof `8`, reduced `7.57936797715`
- `yAbs_yy:linear`: chi2 `15.8963967714`, dof `6`, reduced `2.6493994619`

## Remaining Obligations

- replace fixture baseline with accepted SM generator or theory table authority
- bind raw HEPData measured vectors and covariance with provider/version/checksum token
- define frozen-prediction or independent holdout protocol
- record external authority acceptance before empirical or SM promotion
