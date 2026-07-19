# Generic Schur coercivity join for Navier–Stokes and Yang–Mills

## Purpose

The repository had two independent Schur lanes:

- a constructive finite block Schur complement in the Bałaban SU(2) one-step Yang–Mills programme;
- a fail-closed Navier–Stokes shell frame-gap target
  \(S_N=(I-K_{11})-K_{10}(I-K_{00})^{-1}K_{01}\).

This join extracts the shared mathematics and makes the NS analytic frontier exact.

## Shared theorem

`DASHI.Analysis.BlockSchurCoercivity` proves, over an abstract ordered scalar carrier, that

\[
D \succeq \delta,
\qquad
C A^{-1}B \preceq \eta,
\qquad
\eta \preceq \delta
\]

imply

\[
D-C A^{-1}B \succeq \delta-\eta.
\]

The theorem is coordinate-free. It requires only:

1. a quadratic-form identity for the Schur complement;
2. a diagonal high-block lower bound;
3. a cross-correction upper bound;
4. an ordered-subtraction law.

A separate `StrictSchurGap` witness records positivity of the residual \(\delta-\eta\).

## Yang–Mills instance

`BalabanSchurGenericInstance.agda` maps the existing
`BalabanFiniteOneStepCore.BlockSchurData` into the shared structural socket. It preserves:

- the exact Schur definition;
- the exact cross correction \(C A^{-1}B\);
- the existing determinant factorization.

No new Yang–Mills analytic claim is introduced.

## Navier–Stokes instance

`NSShellSchurInstance.agda` uses

\[
A=I-K_{00},\quad B=K_{01},\quad C=K_{10},\quad D=I-K_{11}.
\]

The shell structure is intentionally separate from analytic bounds.
`NSCrossShellSchurBound.agda` exposes two independent inputs:

- `NSDiagonalShellGap`;
- `NSCrossShellCorrectionBound`.

Once those are joined, `frontierDischargeImpliesFrameGap` proves the quantitative NS Schur frame gap.

## Exact remaining frontier

The live NS obligation is now precisely

\[
\langle x,
K_{10}(I-K_{00})^{-1}K_{01}x
\rangle
\leq
\eta
\]

with

\[
\eta < \delta_{11},
\]

where \(\delta_{11}\) is the high-shell diagonal gap. A numerical fit or a naive product-of-norms estimate is not promoted as this theorem input.

## Promotion boundary

Constructive in this change:

- the shared structural adapter;
- the abstract Schur lower-bound theorem;
- preservation of the finite YM determinant identity;
- the conditional NS frame-gap reduction.

Still open:

- a scale-uniform, non-adversarial Biot–Savart cross-shell estimate;
- positivity of a concrete residual gap for the full NS shell family;
- any full Navier–Stokes or Clay promotion.
