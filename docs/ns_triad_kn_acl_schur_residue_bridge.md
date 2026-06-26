# NS triad K_N ACL / Schur residue bridge

This is a candidate-only bridge note, not a theorem.

Current reading:

- The Fields paper is structurally relevant as shell-count geometry, but
  `docs/ns_triad_kn_LFT_kernel_ACL_match.md` kills the direct kernel match to
  the current positive-sector `L_FT^+`.
- `docs/ns_triad_kn_after_acl_fork_resolution.md` kills the signed rescue as
  well: the corrected ACL first harmonic cancels exactly in signed form, but
  leaves `S_+ = S_abs / 2`, so the positive block is not controlled by ACL.
- The Shahmurov paper is structurally relevant downstream because it records a reduction theorem to the axisymmetric-with-swirl endpoint, but keeps the reduced endpoint theorem conditional.
- Neither paper closes a DASHI proof obligation on its own.

Compatibility audit for the Fields paper:

| Fields object | DASHI object |
| --- | --- |
| Angular Cancellation Lemma / Theorem 4.27 | shell-count carrier candidate only; not the exact current `L_FT^+` kernel |
| unit-width shells | the shell convention used in the current mixed-tail lane |
| resonant band count `O(k_j)` | the cancellation-count carrier that could suppress the off-diagonal block |
| geometric factor `G(k,p)` | the block-kernel geometry behind `L_FT^+` |
| shell-local cancellation | possible route to `SchurResidueScale` |

Compatibility audit for the Shahmurov paper:

| Shahmurov object | DASHI object |
| --- | --- |
| Theorem 2.2 reduction to axisymmetric-with-swirl | endpoint-reduction carrier only |
| Corollary 2.3 conditional on AS | the missing endpoint theorem remains open |
| compatibility checklist / Theorem 12.4 | endpoint-to-trajectory bridge target |
| no independent full regularity proof | no Clay promotion, no theorem promotion |

Analytic conclusion:

The shortest path is still

1. prove a uniform tail coercivity lower bound;
2. prove `q_gap(N) >= c / N^2` via a Schur/off-diagonal block estimate;
3. prove the BKM projection estimate structurally;
4. prove the residence-time exclusion.

The Shahmurov paper is still downstream carrier input. The Fields ACL paper is
no longer the active direct carrier for step 2: the exact kernel match already
failed, and the corrected signed half-sum test shows that ACL cancellation dies
when the positive-sector block keeps only `S_+`. The live route is therefore a
direct positive-sector magnitude/counting proof.
