# NS triad K_N ACL to L_FT^+ operator-norm proof plan

This note is candidate-only. It now records the post-fork proof state after the
Fields ACL route was tested against the exact mixed-tail block.

Current status:

- The sampled finite-shell Schur-test witness is still valid.
- The direct kernel match to the Fields ACL carrier now fails for the current
  positive-sector `L_FT^+`; see `docs/ns_triad_kn_LFT_kernel_ACL_match.md`.
- The corrected signed half-sum test also fails to rescue the route: see
  `docs/ns_triad_kn_after_acl_fork_resolution.md`.
- The DASHI telemetry says the mixed-tail tail block is stable on the sampled
  shells, the Schur subtraction stays small, and the normalized gap is positive
  with an observed decay near N^-2.2.
- None of that is yet a proof of `q_gap(N) >= c / N^2`.

The target chain is:

1. abandon the signed ACL lane for the current positive-sector block;
2. prove a direct magnitude/counting bound on the positive-sector off-diagonal block;
3. promote that counting theorem to a profile-uniform weighted Schur product bound
   `R_N(w) * C_N(w) <= C^2 / N^2`;
4. lift it to an `L^2 -> L^2` operator-norm estimate;
5. transfer that estimate to the normalized Schur residue `q_gap`;
6. combine with `D(N) ~ N^2` to get a dissipation-scaled lower bound.

Compatibility map:

| Fields ACL object | DASHI object |
| --- | --- |
| Theorem 4.27 / Angular Cancellation Lemma | structurally relevant geometry only; no live direct proof carrier for the current `L_FT^+` block |
| unit-width shells `S_j` | the shell convention in the mixed-tail lane |
| resonant set count `O(k_j)` | the cancellation count that could suppress the cross block |
| geometric factor `G(k,p)` | the kernel geometry behind `L_FT^+` |
| assembled shell-local cancellation | potential route to `SchurResidueScale` |

Proof obligations that remain open:

| Gate | What must be proved |
| --- | --- |
| shell normalization | the DASHI block split really uses the same thin-shell geometry as the ACL proof |
| kernel normalization | fails: the entrywise `L_FT^+` kernel is profile-weighted and uses `max(cos,0)` |
| signed rescue | fails: the corrected ACL harmonic gives `S_+ = S_- = S_abs/2`, so the positive block does not inherit the signed cancellation |
| weighted Schur lifting | prove `R_N(w) * C_N(w) <= C^2 / N^2`, then deduce `|L_FT^+|_op <= C / N` |
| residue transfer | the operator bound implies `q_gap(N) >= c / N^2` in the DASHI normalization |
| trajectory scope | the estimate is not restricted to the forced-tail sampled profiles |

Analytic conclusion:

The shortest honest path is now:

1. prove the direct positive-sector magnitude/counting theorem;
2. prove a profile-uniform weighted Schur product bound
   `R_N(w) * C_N(w) <= C^2 / N^2`;
3. deduce `|L_FT^+|_op \lesssim N^-1`;
4. deduce `q_gap(N) >= c / N^2`;
5. combine with `D(N) ~ N^2` to get `D q_gap` bounded below.

This note records the route only. It does not claim theorem authority, full-NS
promotion, BKM exclusion, or Clay promotion.
