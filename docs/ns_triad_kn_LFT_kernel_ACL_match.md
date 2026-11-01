# NS triad K_N L_FT kernel ACL match

This note answers one question only:

`L_FT^+(k,p) =? C_norm(N) * K_ACL(k,p)`

for the current mixed-tail positive-sector cross block.

Decision:

`kernelMatchStatus = failed`

The current DASHI `L_FT^+` kernel is not the Fields ACL kernel up to an
`N`-only normalization.

## Exact DASHI entry

From `scripts/ns_triad_kn_shell6_mixed_tail_decomposition.py`, the streaming
builder retains resonant triads and assigns each retained pair-incidence edge
the weight

`(sqrt(pi_i pi_j pi_l) / 3) * max(cos(phi_i + phi_j - phi_l), 0)`.

Therefore, for a finite mode `k` and a tail mode `p`,

`L_FT^+(k,p) = -sum_{triads touching {k,p}} (sqrt(pi_i pi_j pi_l) / 3) * max(cos(phi_i + phi_j - phi_l), 0)`.

Two consequences are immediate.

1. The entry is profile-dependent through `sqrt(pi_i pi_j pi_l)`.
2. The signed oscillatory factor is truncated to `max(cos(...), 0)`, so the
   ACL sign cancellation does not survive entrywise.

That already kills the claimed identity with a profile-independent ACL kernel.

## ACL carrier target

The candidate carrier shape was:

`L_FT^+(k,p) = C_norm(N) * K_ACL(k,p)`

with `K_ACL` carrying signed/angular cancellation and depending only on the
shell geometry up to harmless bounded factors.

The current DASHI cross block does not have that form.

## Sampled analytic artifact

Artifact:

- `scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_lft_kernel_acl_match_20260624/summary.json`
- `scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_lft_kernel_acl_match_20260624/summary.md`

The run completed on 2026-06-24 and recorded its own timer/logger. Total
elapsed time was about `556515 ms`.

Sampled rows `N=6,8,10,12`:

| N | forced-tail max entry | uniform-all-modes max entry | ratio forced/uniform |
| ---: | ---: | ---: | ---: |
| 6 | `2.89225e-05` | `9.71693e-06` | `2.9765` |
| 8 | `1.56294e-05` | `2.90477e-06` | `5.3806` |
| 10 | `9.76219e-06` | `1.12222e-06` | `8.6990` |
| 12 | `6.67091e-06` | `5.12049e-07` | `13.0279` |

So even at the sampled scaling level, the exact entry size changes materially
when the profile changes. That is incompatible with an `N`-only normalization
times a profile-independent kernel.

The same run also found that the forced-tail normalization

`N^(3/2) * max_{k,p} |L_FT^+(k,p)|`

stays in

`[2.77305e-04, 4.25072e-04]`.

That is consistent with a shell-count story, but it does not repair either of
the two structural failures:

1. profile dependence;
2. loss of signed ACL cancellation.

## Decision tree outcome

This is Case C plus a normalization/profile obstruction.

- Case C: the match fails by sign/absolute-sector destruction.
- Also: the exact DASHI entry carries profile amplitudes, so the kernel is not
  profile-independent.

Therefore:

- `positiveSectorSurvivesACL = false`
- `absoluteSectorSurvivesACL = false`
- `schurLiftAvailable = false`
- `profileIndependentBoundClosed = false`
- `theoremPromoted = false`
- `clayPromoted = false`

## Bottom line

The Fields ACL paper is not the current proof carrier for DASHI’s
`L_FT^+` Schur gate.

What survives is narrower:

1. the sampled finite-shell Schur witness remains valid;
2. the profile-independent Schur theorem remains open;
3. the exact ACL kernel-match route is killed for the present positive-sector,
   profile-weighted `L_FT^+`.
