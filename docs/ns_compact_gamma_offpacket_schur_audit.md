# Compact-Gamma off-packet Schur-tail audit

## Purpose

The exact compact-Gamma differential audit localized the held-out failure of a common local logarithmic escape modulus to the off-packet nonlinear response `D m_off(u)[h]`.

This lane tests the finite-Galerkin candidate

```text
|D m_off,K(u)[h]|
  <= C_Schur E_K(u) ||h||_Xtilde + Tail_K(u,h).
```

It is a proof-search and falsification instrument, not a continuum theorem.

## Exact derivative

On the strict positive-transfer branch,

```text
B_K = Q_K / (Q_K + 2 nu D_K)
```

and

```text
m_off(u) = DB_K(u)[F_off(u)] / (nu 2^(2K)).
```

The audit computes

```text
D m_off(u)[h]
  = (D2 B_K(u)[h,F_off(u)] + DB_K(u)[D F_off(u)[h]])
    / (nu 2^(2K)).
```

The calculation uses the exact finite Fourier convolution, Leray projection, cubic-transfer second variation, quadratic-dissipation second variation, and rational compact-potential derivative.

## Weighted tangent norm

Tangents are projected onto the fixed target-packet-energy surface. The candidate family is

```text
||h||^2_Xtilde(K,sigma,eta)
  = sum_k (1 + 2^(-2K)|k|^2)
          2^(2 sigma |j(k)-K|)
          (1 + eta a_K(k))^2
          |h_k|^2,
```

where `j(k)=floor(log2 |k|)` and

```text
a_K(k) = 1 - khat^T M_K khat.
```

`M_K` is the target-packet Fourier-energy second moment. The angular term is projective and invariant under `k -> -k`.

## Exact shell split

The projected tangent is partitioned into reality-closed dyadic shell pieces

```text
h = sum_r h_r,
```

with `r=j(k)-K`. Linearity gives

```text
D m_off(u)[h] = sum_r D m_off(u)[h_r].
```

For tail radius `R`, the audit defines

```text
Near_R = sum_|r|<=R |D m_off(u)[h_r]|,
Tail_R = sum_|r|>R  |D m_off(u)[h_r]|.
```

Hence

```text
|D m_off(u)[h]| <= Near_R + Tail_R.
```

Calibration fits only `Near_R / (E_K ||h||_Xtilde)`; the far-shell response remains explicit.

## Validation protocol

The workflow uses independent center, calibration, and held-out seeds, two target shells, evolved multi-triad packets, path and Navier-Stokes RHS tangents, a declared weight grid, and exact-seed matched N32/N48/N64 reconstructions.

A candidate survives only when every branch resolves, the calibration constant is finite, all held-out near and full split inequalities hold, and the same checks hold at every matched cutoff. A clean falsification is accepted as a valid outcome.

## Formal layer

`NSCompactGammaOffPacketSchurSplit.agda` proves that a near-shell Schur bound plus an explicit tail bounds the full off-packet response, that a separately controlled tail yields a full off-packet budget, and that this bound composes with the remaining logarithmic-numerator terms.

`NSCompactGammaOffPacketWeightedKernelBridge.agda` requires the concrete near response to be bounded by the output energy of the exact certified weighted kernel before the Schur certificate may enter that composition.

`WeightedKernelSchurTest.agda` now has a companion `ExactKernelAction` surface. It prevents an abstract `applyKernel` from being treated as though it were definitionally assembled from the declared matrix entries. A concrete vector model must provide an evaluator and prove exact action equality.

`NSCompactGammaOffPacketPairIncidenceKernelBridge.agda` adds a finite list-indexed pair-incidence kernel whose entries vanish away from their declared row/column incidence. It proves that exact entry identity, exact action semantics, and exact equality of the concrete near response with the pair action are sufficient to discharge the representation inequality required by the weighted-kernel bridge. The adapter then feeds the existing Schur-tail composition without inserting a fitted comparison bound.

## Updated exact frontier

The logical chain is now explicit:

```text
finite pair enumeration
  -> exact incidence entries
  -> exact kernel-entry identity
  -> exact kernel action
  -> concrete near response equality
  -> weighted Schur certificate
  -> near + explicit tail
  -> logarithmic numerator bound.
```

The next mathematical instance must populate this surface with the actual Fourier pair incidences of the compact-Gamma off-packet derivative and prove row/column bounds uniformly in shell and cutoff. After that, the remaining independent leaf is the far-shell decay/absorption estimate.

## Authority boundary

The implementation does not yet construct the concrete Fourier pair-incidence instance, prove a shell/cutoff-uniform weighted Schur certificate, absorb the far-shell tail, establish compact path coverage, continuum compactness, BKM continuation, global regularity, or promotion.
