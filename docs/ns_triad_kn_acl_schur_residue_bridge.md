# NS triad K_N ACL / Schur residue bridge

This is a candidate-only bridge note, not a theorem.

Current reading:

- The Fields paper is structurally relevant because it gives an Angular Cancellation Lemma with unit-width shell counting and a geometric-factor cancellation mechanism.
- The Shahmurov paper is structurally relevant downstream because it records a reduction theorem to the axisymmetric-with-swirl endpoint, but keeps the reduced endpoint theorem conditional.
- Neither paper closes a DASHI proof obligation on its own.

Compatibility audit for the Fields paper:

| Fields object | DASHI object |
| --- | --- |
| Angular Cancellation Lemma / Theorem 4.27 | candidate carrier for a finite-to-tail Schur estimate |
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

The current external papers are aligned with steps 2 and 4, but they are only carrier inputs until the exact normalizations are matched and the missing bounds are proved.
