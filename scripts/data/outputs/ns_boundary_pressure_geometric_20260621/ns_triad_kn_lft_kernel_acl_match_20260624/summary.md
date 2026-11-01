# NS Triad K_N L_FT Kernel ACL Match

- status: `ok`
- kernel match status: `failed`
- positive sector survives ACL: `False`
- absolute sector survives ACL: `False`
- Schur lift available: `False`
- theorem promoted: `False`

## Exact Formula

For a finite mode k and tail mode p, the exact mixed-tail cross-block entry is L_FT^+(k,p) = -sum_{triads touching {k,p}} (sqrt(pi_i*pi_j*pi_l)/3) * max(cos(phi_i+phi_j-phi_l),0), with the sum taken over retained resonant triads whose pair-incidence edge joins k to p.

## ACL Target

Candidate ACL carrier target: L_FT^+(k,p) = C_norm(N) * K_ACL(k,p), with K_ACL profile-independent and carrying the signed/angular cancellation geometry.

## Sampled Rows

| N | K | profile | active pairs | row sup | col sup | max entry | N^(3/2)*max entry |
|---:|---:|---|---:|---:|---:|---:|---:|
| 6 | 5 | forced_tail | 22270 | 0.0114691 | 0.000340859 | 2.89225e-05 | 0.000425072 |
| 6 | 5 | uniform_all_modes | 459289 | 0.00411922 | 0.00177946 | 9.71693e-06 | 0.000142809 |
| 8 | 7 | forced_tail | 41144 | 0.0114983 | 0.000190048 | 1.56294e-05 | 0.000353653 |
| 8 | 7 | uniform_all_modes | 2321604 | 0.00230246 | 0.00138254 | 2.90477e-06 | 6.57275e-05 |
| 10 | 9 | forced_tail | 66103 | 0.0116587 | 0.000139883 | 9.76219e-06 | 0.000308708 |
| 10 | 9 | uniform_all_modes | 7807110 | 0.00144552 | 0.00110493 | 1.12222e-06 | 3.54877e-05 |
| 12 | 11 | forced_tail | 96168 | 0.0116101 | 9.17093e-05 | 6.67091e-06 | 0.000277305 |
| 12 | 11 | uniform_all_modes | 20693450 | 0.000971186 | 0.000916389 | 5.12049e-07 | 2.12855e-05 |

## Profile Dependence

| N | max-entry ratio forced/uniform | row-sup ratio | col-sup ratio |
|---:|---:|---:|---:|
| 6 | 2.9765 | 2.78429 | 0.191552 |
| 8 | 5.3806 | 4.99392 | 0.137463 |
| 10 | 8.69901 | 8.06539 | 0.126599 |
| 12 | 13.0279 | 11.9545 | 0.100077 |

## Decision

Kernel-match decision: failed.  The exact DASHI cross-block entry carries profile amplitudes sqrt(pi_i*pi_j*pi_l)/3 and the positive-sector truncation max(cos(closure),0), so the signed ACL factor does not survive entrywise and the kernel is not profile-independent.  On the sampled shells, forced-tail max cross entries span 6.67091e-06..2.89225e-05, the uniform all-mode comparison spans 5.12049e-07..9.71693e-06, and their ratio spans 2.9765..13.0279.  The forced-tail N^(3/2) * max-entry normalization stays in 0.000277305..0.000425072, which is compatible with a shell-count story but does not repair the lost sign cancellation or the profile dependence.

## Scaling

- forced-tail max entry stats: `{'count': 4, 'min': 6.670913119765903e-06, 'max': 2.89224666250484e-05, 'mean': 1.5246243942163915e-05, 'sample_stdev': 9.845421873307777e-06, 'relative_range': 1.4594777303638178}`
- forced-tail N^(3/2) max entry stats: `{'count': 4, 'min': 0.00027730465095149645, 'max': 0.0004250717120042692, 'mean': 0.00034118425690608226, 'sample_stdev': 6.410384882925235e-05, 'relative_range': 0.43310046715739453}`
- profile-dependence max-entry ratio stats: `{'count': 4, 'min': 2.9765036158598757, 'max': 13.027886952467458, 'mean': 7.520999525268657, 'sample_stdev': 4.356882920836482, 'relative_range': 1.336442490501093}`
