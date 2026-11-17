# NS triad K_N after ACL fork resolution

Decision:

- Fork A dead.

Reason:

- The corrected ACL harmonic is the azimuthal first harmonic in the plane
  perpendicular to `k`, not the closure-angle cosine between `p` and `k-p`.
- On the sampled same-shell transverse sets, the corrected harmonic satisfies
  `S_signed = S_+ - S_- = 0` and `S_+ = S_- = S_abs / 2`.
- Therefore the ACL cancellation is real but only cancels the positive and
  negative halves against each other. It does not make the positive block
  `S_+` small.

Artifacts:

- `scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_acl_signed_half_sum_proof_20260624/summary.json`
- `scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_acl_signed_half_sum_proof_20260624/summary.md`

What survives:

- The sampled finite-shell positive-sector Schur witness.
- The pointwise upper-bound route
  `|L_FT^+(k,p)| <= |L_FT^raw(k,p)|`.
- Bounded profile weights for upper bounds, since
  `sqrt(pi_i pi_j pi_l) / 3 <= 1/3`.

What is dead:

- Any proof route that tries to control the positive-sector Schur block by ACL
  signed cancellation alone.

Live route:

- Fork B only: direct positive-sector magnitude/counting control.

Next gate:

- Prove profile-independent row and column bounds for the positive-sector block,
  with target scale
  `sup_p sum_k |L_FT^+(k,p)| + sup_k sum_p |L_FT^+(k,p)| <= C * N^(-1/2)` at the
  counting layer, yielding `|L_FT^+|_op <= C / N` after Schur.
