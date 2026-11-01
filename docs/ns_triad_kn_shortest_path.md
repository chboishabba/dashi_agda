# NS triad K_N shortest path

This is a proof-plan note, not a theorem.

Current status:

- candidate-only finite-shell telemetry exists for the mixed-tail lane;
- tail-only collapse is not the observed obstruction;
- catastrophic Schur cancellation is not the observed obstruction;
- BKM-tail projection is tiny on the sampled rows, but that is still telemetry, not a structural proof.
- external carrier notes now exist for the Fields ACL paper and the Shahmurov reduction paper;
  they remain candidate-only bridge inputs, not authority upgrades.
- the ACL-to-`L_FT^+` proof-plan note now exists and pins the next analytic target to the
  finite-to-tail operator norm estimate, not to more telemetry.

Shortest analytic path:

1. TailDiagonalStable

   Prove a uniform lower bound for the tail block Rayleigh quotient:

   `q_diag(N) >= c_diag > 0`.

   Numerical input: `q_diag` stays on the sampled `10^-2` scale across `N=6,8,10,12`.

2. SchurResidueScale

   Prove the normalized Schur residue is not just observed but controlled:

   `q_gap(N) >= c_gap / N^2`.

   Equivalent target shape:

   `D(N) * q_gap(N) >= c_mix > 0`.

3. BKMProjectionSmallness

   Prove the bad mixed-tail eigenpiece is structurally small against the BKM stretching proxy.

   The telemetry says the BKM-tail projection squared fraction is tiny and drops sharply by `N=12`, but the proof needs an orthogonality estimate, not a fit.

4. ResidenceTimeExclusion

   Use the energy inequality

   `nu ∫ D(t) dt <= E0`

   to rule out enough residence time in bad mixed-tail configurations.

External carrier alignment:

- Fields ACL is the candidate carrier for the `SchurResidueScale` off-diagonal block question.
- `docs/ns_triad_kn_LFT_operator_norm_acl_proof_plan.md` is the current analytic bridge note.
- Shahmurov is the candidate carrier for the endpoint-reduction / residence bridge, conditional on the missing AS theorem.
- `scripts/ns_triad_kn_external_paper_bridge_audit.py` is the audit runner for the two local PDFs.

What is still missing:

- a structural Schur-test / off-diagonal block bound;
- a uniform tail coercivity argument from the triad geometry;
- a PDE bridge from finite-dimensional candidate telemetry to actual Navier-Stokes trajectories;
- a residence-time argument that closes the BKM contradiction.

Bottom line:

The shortest path is still analytic, not computational. The next code artifacts are candidate-only bridge receipts and the only route that changes the proof state is a uniform operator-norm / Schur estimate, not another telemetry scan.
