# Navier–Stokes Round 33 — canonical same-object lookup and sharp HH-bad gain

Round 33 advances two concrete leaves of the highest-alpha periodic Navier–Stokes path and connects the resource ledger to the literal nine-owner type. It does not add a terminal Clay wrapper and it does not claim any missing physical owner estimate.

## 1. The same-object lookup obstruction is now explicit

The Round-31 interface required one finite Galerkin system whose stored velocity agrees with every positive coefficient, every reconstructed negative coefficient, and the exact retained-mode list. The earlier state type, however, did not itself rule out two positive representatives with the same mode but different values, or a positive representative that conflicts with another representative's reconstructed negative sheet.

Round 33 proves that any `SameCarrierSameObjectGalerkinBuilder` forces both compatibility laws:

```text
same positive mode  -> same stored value
positive mode = reconstructed negative mode
                    -> positive value = reconstructed negative value.
```

Consequently either conflict is a formal refutation of the claimed builder. This is a genuine necessary-condition theorem, not a status receipt.

## 2. Canonical executable Fourier lookup

For a state carrying those compatibility laws, Round 33 constructs an executable total coefficient function using the repository's decidable equality on `Z^3`.

Positive lookup scans the positive-orbit list. Negative lookup scans the conjugately reconstructed sheet. The combined lookup gives priority to a positive representative; compatibility proves that this is harmless whenever a mode occurs on both sheets.

The main exact theorems are:

```text
literalVelocityAtPositiveExact
literalVelocityAtNegativeExact
builderAndCanonicalPositiveAgree
builderAndCanonicalNegativeAgree.
```

Thus the coefficient function and retained-mode list required by the finite Galerkin system are no longer free fields once the compatibility certificate is present.

The remaining finite-system producer must still supply, on this same object:

```text
literal cutoff and mode membership;
viscosity;
mode inverse-square data;
triad enumeration authority;
zero-mode exclusion and reality closure;
transversality evidence.
```

Only after those fields are assembled does the existing Round-31 `SameCarrierSameObjectGalerkinBuilder` become inhabited.

## 3. The HH-bad dyadic gain is sharp and unique

The raw half-kernel/Bernstein ratio is represented exactly as

\[
R_q=2\,2^q.
\]

Round 33 proves

\[
R_{q+1}=2R_q.
\]

For an owner allocation \(\eta\), define

\[
g_q(\eta)=\frac{\eta}{2}\,2^{-q}.
\]

The machine-checked results are

\[
g_{q+1}(\eta)=\frac12g_q(\eta),
\qquad
g_q(\eta)R_q=\eta,
\]

and the uniqueness theorem

\[
gR_q=\eta\quad\Longrightarrow\quad g=g_q(\eta).
\]

This strengthens the Round-31 dimensional diagnosis. Exact cutoff-independent calibration does not merely benefit from one inverse shell power: on this dyadic model the compensating multiplicative factor is forced and halves at every shell.

The physical theorem remains to derive that gain from the actual trajectory through occupation time, dissipation-range localization, intermittency, alignment, or another signed cancellation. The algebra cannot manufacture that mechanism.

## 4. Resource valuation on the actual nine-owner family

Every existing `AdmissibleOwnerEstimate` now maps to

\[
(\eta_i,A_i,B_i,0),
\]

where the fourth coordinate is the forbidden continuation-resource coordinate. Finite aggregation is proved coordinatewise equal to the repository's existing sums:

```text
dissipation coordinate = sumEta
data coordinate        = sumDataRemainder
critical coordinate    = sumCriticalCoefficient
forbidden coordinate   = 0.
```

For an actual `NineOwnerEstimateFamily`, define

\[
\delta_{\mathrm{NS}}=1-\sum_{i=1}^{9}\eta_i.
\]

A `StrictAdmissibleOwnerBudget` now yields both

\[
\delta_{\mathrm{NS}}>0
\]

and the exact robustness identity

\[
\sum_{i=1}^{9}\eta_i+\delta_{\mathrm{NS}}=1.
\]

This closes the valuation/slack algebra on the literal nine-owner type. It does not construct the nine estimates.

## Sources

The Agda headers record:

- Jean Leray, *Sur le mouvement d'un liquide visqueux emplissant l'espace*, DOI `10.1007/BF02547354`;
- Roger Temam, *Navier-Stokes Equations: Theory and Numerical Analysis*, DOI `10.1090/chel/343`;
- Hajer Bahouri, Jean-Yves Chemin and Raphael Danchin, *Fourier Analysis and Nonlinear Partial Differential Equations*, DOI `10.1007/978-3-642-16830-7`;
- Xiaoyutao Luo, *A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal Localization*, DOI `10.1007/s00021-019-0411-z`.

The finite-dimensional Cauchy–Lipschitz/Picard–Lindelöf step remains standard once the literal coordinate bridge is constructed; Round 33 deliberately works before that analytic library boundary.

## Exact frontier after Round 33

The next finite-flow leaves are:

```text
canonical finite Galerkin system from the compatible lookup;
physical/real coordinate equivalence;
real Picard–Lindelöf authority;
literal triad-energy family;
real integrated energy identity;
literal global finite-flow authority.
```

The decisive analytic leaves remain:

```text
physical HH-bad gain;
physical two-sided Com cross-shell decay;
periodic strain kernel and HH-good estimate;
LH, HL, CC, kernel, tail and boundary estimates;
one actual nine-owner family with delta_NS > 0;
shell/Galerkin limits and periodic Serrin continuation.
```

The implementation follows the fail-closed rule:

```text
never transport a bound without transporting its index,
carrier, trajectory and resource valuation.
```
