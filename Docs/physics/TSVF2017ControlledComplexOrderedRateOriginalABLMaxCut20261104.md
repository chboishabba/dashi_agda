# TSVF 2017 controlled complex → ordered ABL rate: same-source max-cut (4 Nov 2026)

**Owner:** [#1460](https://github.com/chboishabba/dashi_agda/pull/1460), `DASHI/Quantum/TSVF2017ControlledComplexOrderedRateBridgeExact.agda`. Downstream of #1444; do not import child back into physical YM parent. **Status:** SOURCE-WRITTEN `{-# OPTIONS --safe #-}` header, GitHub readback; **NOT kernel checked** or a physical many-body result.

## Source owners and mathematical statement

Reuse (do not replace):
- `TSVF2017ControlledPointerRecordUnitaryExact`: actual complex-linear controlled isometric two-register rotation; `emittedEnvironmentSite` from the original selected vacuum.
- `TSVF2017HeterogeneousEnvironmentABLExact`: sitewise complex Hermitian overlaps, tensor Born factorization and original `Q.ablProbability` with positive selected total.
- `TSVF2017OriginalComplexABLSelectedExact`: the original ABL numerator/denominator pair and original two projectors.
- `TSVFComplexGammaProductBornExact`: arbitrary complex gamma product and its exact squared Born norm.
- `NSTriadKNLuoFiniteRationalOrderCore`: existing nonnegative ordered rational multiplication.
- `TSVF2017CorrelatedEnvironmentMarginalNoGoExact`: full one-register marginal equality does NOT license product factorization for entangled global records.

The new `CalibratedControlledPulse` is an **actual** `CertifiedRotation` with the explicit chosen site certificate `2*siteBorn(emittedEnvironmentSite pulse) <= 1`. For a heterogeneous list `ss`, `powerTwo ss` is proved equal to `Env.rationalPower 2 (count ss)`. Let `GammaBorn` be the **actual squared complex norm** of the given arbitrary gamma list. Under the separate hypothesis `GammaBorn <= 1`, the chosen original ABL weights satisfy:

```text
powerTwo(ss) * ABL.numerator(Hetero.wrongABL gamma (emittedSites ss)) <= 1
(powerTwo(ss)+1) * ABL.numerator(Hetero.wrongABL gamma (emittedSites ss))
 <= ABL.denominator(Hetero.rightABL gamma (emittedSites ss))
```

The proof composes actual emitted-record Born factors, rational monotone products and original ABL numerator/denominator equalities; no new arbitrary Born-factor proxy, Nat-scale `rightRaw/wrongRaw`, or substitute probability law. The original right mass is 1, so the selected original positive ABL context supplies the nonzero denominator. The published 3/5 overlap from the existing norm-preserving `threeFourPulse` has exact `2*(9/25)<=1` certificate, furnishing the all-k homogeneous specialization.

## Executed independent reference

`scripts/check_tsvf_controlled_complex_ordered_rate.py`, exact `fractions.Fraction` complex multiplication and norm-square, 3000 deterministic heterogeneous fixtures, 21000 checked identities/inequalities; passed. A noncalibrated pulse (`c=1`, one site) and an oversized `gamma=2+0i` (zero sites) each violate the desired universal bound, so both hypotheses are essential. The reference is **not** Agda typechecking.

## Correlated-global Born error: exact conditional correction

The follow-on `ControlledCorrelationBornError` does NOT infer independence from local density matrices. It requires an **actual global complex wrong amplitude** `A_actual`, a nonnegative explicit error `delta`, and the source-side comparison `|A_actual|² <= W_independent + delta`, where `W_independent` is the original controlled-pulse ABL wrong numerator. Then `correlatedWrongRateWithError` and `correlatedTwoChannelCrossWithError` prove over the exact rationals:

```text
2^k |A_actual|² <= 1 + 2^k delta
(2^k+1)|A_actual|² <= 1 + |A_actual|² + 2^k delta
```

This is the correct **error-dependent** inequality to use in physical correlated-environment work rather than declaring a tensor product from local marginals. A physical selected global source must independently construct `A_actual`, derive a useful `delta`, and instantiate its chosen **original ABL** two-outcome context; the present theorem intentionally does NOT equate the global correlated amplitude with that unconstructed postselection. Without an upper bound on global deviation, the Bell counterexample prevents a uniform tensor-rate promotion.

Independent `scripts/check_tsvf_correlated_born_error_rate.py` exact-Fraction run passed 3200 variable-global-amplitude fixtures with nonzero and zero additive errors. Source-written lemma; Agda kernel acceptance pending.

## Physical no-promotion boundary

The local `CalibratedControlledPulse` certificate is NOT yet derived for the *selected physical many-body interaction*. The current tensor product is a finite independent record preparation, not a theorem for correlated or entangled environmental histories. A selected real final effect/bra and actually admissible disturbance class, relation to the published 2017 experiment, quantum dynamics, real-Hilbert completion, strongly continuous observer semigroup, domain/core identification, and same OS Hamiltonian spectral transport remain open. No 4D Yang–Mills nontriviality, cutoff-uniform CMP116 decay, continuum OS gap or Clay result is claimed.

## P00 cross-PR reconciliation (4 Nov API heads)

- Physical YM [#1444](https://github.com/chboishabba/dashi_agda/pull/1444): `ef8dd28009e70673213bce8ba6d773395dc2d42f`, contains original SU(N) R445 F08–F12 physical/finite-source developments.
- Downstream [#1460](https://github.com/chboishabba/dashi_agda/pull/1460): child branch descended from earlier `e80d63c5f19f1b7c84f2513ee66e9dad99879a3e`, now diverged. The user-cited `78549bf4970c12aac34c5b440b20a4e3a87c081f` is an ancestor of `92c25b24a877...`, not the newest PR head.
- Changed-file overlap between the two PRs before this note: 26 shared paths; 20 had **identical Git blob SHAs**, including all shared YM Agda owner modules and the 219-field JSON inventory. The other six are docs, TODO, changelog and `BalabanRGTOERegression.agda` with independent additions. This is source-level reuse, **not** a completed integration/merge.
- Merge/rebase/reconciliation of the parent branch's later physical SU(N) F08–F12 modules into the child remains an explicit **P00 open item**. Do not overwrite a child's TSVF/KK additions with parent docs or vice versa, and do not declare the child's selected physical measure equivalent to a standalone parent theorem via a filename import alone.

**Attribution:** Aharonov/Bergmann/Lebowitz (1964), Aharonov/Vaidman, Aharonov/Cohen/Landsberger (2017) and existing DASHI theorem owners. Wilson/Bałaban and original finite-Haar/RG theorem owners remain separately credited in #1444.
