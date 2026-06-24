# NS triad K_N ACL to L_FT^+ operator-norm proof plan

This note is candidate-only. It records the analytic route that would be needed
to turn the Fields Angular Cancellation Lemma into a Schur-residue bound for
the mixed-tail lane.

Current status:

- The Fields paper is a plausible carrier for the angular-cancellation side of
  the estimate.
- The DASHI telemetry says the mixed-tail tail block is stable on the sampled
  shells, the Schur subtraction stays small, and the normalized gap is positive
  with an observed decay near N^-2.2.
- None of that is yet a proof of `q_gap(N) >= c / N^2`.

The target chain is:

1. map the Fields ACL kernel to the DASHI finite-to-tail block `L_FT^+`;
2. verify that the shell convention is the same unit-width convention;
3. prove a per-output cancellation bound on the off-diagonal block;
4. lift the cancellation to an `L^2 -> L^2` operator-norm estimate;
5. transfer that estimate to the normalized Schur residue `q_gap`;
6. combine with `D(N) ~ N^2` to get a dissipation-scaled lower bound.

Compatibility map:

| Fields ACL object | DASHI object |
| --- | --- |
| Theorem 4.27 / Angular Cancellation Lemma | candidate carrier for a finite-to-tail Schur estimate |
| unit-width shells `S_j` | the shell convention in the mixed-tail lane |
| resonant set count `O(k_j)` | the cancellation count that could suppress the cross block |
| geometric factor `G(k,p)` | the kernel geometry behind `L_FT^+` |
| assembled shell-local cancellation | potential route to `SchurResidueScale` |

Proof obligations that remain open:

| Gate | What must be proved |
| --- | --- |
| shell normalization | the DASHI block split really uses the same thin-shell geometry as the ACL proof |
| kernel normalization | the entrywise `L_FT^+` kernel matches the ACL geometric factor up to harmless constants |
| Schur-test lifting | the per-output cancellation estimate becomes an `L^2` operator norm bound |
| residue transfer | the operator bound implies `q_gap(N) >= c / N^2` in the DASHI normalization |
| trajectory scope | the estimate is not restricted to the forced-tail sampled profiles |

Analytic conclusion:

The shortest path is still:

1. prove `|L_FT^+|_op \lesssim N^-1`;
2. deduce `q_gap(N) >= c / N^2`;
3. combine with `D(N) ~ N^2` to get `D q_gap` bounded below;
4. then attack BKM projection smallness and residence-time exclusion.

This note records the route only. It does not claim theorem authority, full-NS
promotion, BKM exclusion, or Clay promotion.
