# YM/BT Hodge Gauge Commutator Chain

- Decision: `fail_closed_compatibility_chain_no_promotion`
- Compatibility defect: `[d_A,*]F_A = d_A(*F_A) - *(d_A F_A)`
- Validation passed: `True`
- Closure guards fail closed: `True`

## Chain

| row | stage | status | defect role | remaining path |
| --- | --- | --- | --- | --- |
| R01 | finite_hodge_variation | NORMALIZED_SURFACE | not yet evaluated | Prove the selected star is compatible with gauge transport on admissible fields. |
| R02 | finite_hodge_ibp | NORMALIZED_SURFACE | boundary and Hodge-choice leakage is visible before gauge covariance is imposed | Separate ordinary finite adjointness from gauge-covariant adjointness. |
| R03 | gauge_commutator_defect | COMPATIBILITY_DEFECT_ISOLATED | leakage term in the attempted finite YM Euler-Lagrange reduction | Prove the commutator estimate or exact vanishing in the finite BT model. |
| R04 | bt_metric_admissibility | CONDITIONAL_VANISHING_CRITERION | zero only inside the selected admissible compatibility lane | Formalize admissibility and prove the BT metric compatibility lemma without hidden continuum assumptions. |
| R05 | finite_ym_equation_path | OPEN_FAIL_CLOSED | unclosed leakage blocks promotion from variational surface to finite YM equation | Close finite YM equation, Hamiltonian construction, spectral gap, uniform lower bound, and continuum transfer. |
| R06 | downstream_gap_transfer_path | OPEN_FAIL_CLOSED | resolved defect is necessary but not sufficient for downstream gap transfer | Build the finite Hamiltonian, prove positivity and nonzero uniform lower bound, establish spectral convergence, then transfer to the continuum YM measure/theory. |

## BT Metric Vanishing Criterion

The finite BT metric/star is covariantly constant on admissible curvature cochains, preserves boundary/admissibility conditions, and the finite Bianchi identity d_A F_A = 0 is available.

## Maxwell Special Case

After finite Hodge/IBP, abelian Maxwell has the clean adjoint identity `d dagger = +/- * d *` up to the selected degree/sign convention. The nonabelian YM route must separately account for `[d_A,*]F_A`.

## Remaining Path

Close the finite YM equation, construct the finite Hamiltonian, prove a spectral gap, prove a uniform lower bound across the finite BT family, and transfer the lower bound to the continuum.

## O/R/C/S/L/P/G/F

- O: Worker 4 owns the Sprint166 YM/BT finite Hodge gauge-commutator chain emitter.
- R: Normalize the finite Hodge variation chain and isolate [d_A,*]F_A as the compatibility defect/leakage term before any YM promotion.
- C: One stdlib Python script writes normalized JSON, CSV, Markdown, and manifest outputs.
- S: Finite Hodge/IBP gives a clean variational surface; Yang-Mills needs gauge-Hodge compatibility, not just Maxwell-style d dagger equals star-d-star.
- L: BT metric selected so star is covariantly constant on admissible fields implies [d_A,*]F_A vanishes; outside that lane the commutator is leakage.
- P: Use the artifact as a fail-closed compatibility chain and obligation ledger.
- G: Promotion stays blocked until finite YM equation, Hamiltonian, spectral gap, uniform lower bound, and continuum transfer are closed.
- F: No theorem, Clay promotion, spectral gap, or continuum transfer is asserted here.
