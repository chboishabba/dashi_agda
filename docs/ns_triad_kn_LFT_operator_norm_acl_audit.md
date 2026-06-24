# NS triad K_N ACL-to-L_FT^+ operator-norm audit

This is a candidate-only audit note.

Purpose:

Audit the exact bridge from the Fields Angular Cancellation Lemma carrier to
the mixed-tail finite-to-tail block `L_FT^+`.

The analytic claim we want is:

`|L_FT^+|_op <= C / N`

which would then transfer to:

`q_gap(N) >= c / N^2`

under the DASHI normalization.

Audit checklist:

1. Kernel match

   - Write the exact `L_FT^+` kernel from the DASHI triad operator.
   - Compare it with the ACL geometric factor `G(k,p)`.
   - Record whether the positive/absolute sector split preserves the same
     oscillatory factor or only a bounded proxy.

2. Shell convention match

   - Confirm the DASHI carrier uses the same unit-width shell geometry as the
     ACL proof.
   - Confirm the finite-tail index convention does not change the counting
     regime.

3. Cancellation lift

   - Determine whether the ACL shell-local cancellation is per-output or
     genuinely operator-valued.
   - Check whether the `O(k_j)` resonant-band count becomes a `1/N`
     suppression after the cross-block sum.

4. Schur-test route

   - Identify summable row/column bounds for `L_FT^+`.
   - Check whether a standard Schur test is enough, or whether a Hilbert–
     Schmidt bound is the only honest route.
   - Record the exact Schur-test kernel-sum bound as a fail-closed socket in
     `NSTriadKNMixedTailACLOperatorNormAuditReceipt.agda` while keeping
     `theoremPromoted` false.

5. Normalization transfer

   - Verify how the operator-norm estimate becomes the normalized Schur gap
     lower bound in the current receipts.
   - Confirm that the residue is normalized in the same way as the sampled
     `q_gap` rows.

6. Scope

   - State explicitly whether the estimate is profile-independent or only a
     forced-tail carrier statement.
   - If profile-dependent, record the exact assumptions.

7. Derived bound

   - Square the `N^-1` block bound into the `N^-2` Schur residue scale.
   - State exactly which profile assumptions are needed for the transfer.

Addendum, 2026-06-24:

- `scripts/ns_triad_kn_acl_schur_test_proof.py` now proves the exact finite-shell
  Schur-test inequality for the sampled `N=6,8,10,12` mixed-tail rows by
  reconstructing the positive-sector cross block `L_FT^+` and computing the
  exact row/column absolute sums.
- On those sampled rows the row/output sum stays on an `O(1)` scale, the
  column/input sum stays on an `O(N^-2)` scale, and the resulting Schur bound
  `sqrt(row_sup * col_sup)` stays on an `O(N^-1)` scale.
- This is still finite-shell and candidate-only.  It does not by itself
  promote a uniform/profile-independent theorem.

Open gaps that remain after the audit:

- the exact `L_FT^+` normalization;
- the positive/absolute-sector relation to the ACL factor;
- the uniform/profile-independent operator-norm lifting step;
- the residue-to-gap normalization step;
- the profile-scope question.

Conclusion:

The route is still candidate-only and fail-closed. The next theorem-shaped
object, if the audit succeeds, is the `N^-1` operator norm bound; the current
Agda receipt now records the explicit Schur-test kernel-sum witness and the
finite-shell proof artifact without promoting the theorem.
