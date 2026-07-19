# NS pair-incidence kernel Schur bridge

## Purpose

This tranche replaces an unnamed “concrete rectangular kernel” obligation with an exact finite construction and then instantiates that construction with the linearized Fourier-vorticity Biot–Savart interaction.

For enumerated source modes, target modes, and resonant triads, the transfer entry is the finite fold

\[
K(k,q)=\sum_{p+q=k}\operatorname{majorant}\bigl(DN_{\bar\omega}(p,q)\eta_q\bigr).
\]

The weighted row and column sums are computed directly from this kernel.

## Fourier convention

For nonzero Fourier mode `p`, velocity is reconstructed from vorticity as

\[
u_p=|p|^{-2}(p\times\omega_p).
\]

The vorticity interaction convention is

\[
T(p,q;\omega_p,\omega_q)
=(\omega_p\cdot q)u_q-(u_p\cdot q)\omega_q.
\]

Linearization around background vorticity `bar-omega` uses

\[
T(p,q;\bar\omega_p,\eta_q)+T(q,p;\eta_q,\bar\omega_p).
\]

The Schur kernel records a declared nonnegative vector majorant of this expression. It does not use sign or phase cancellation.

## Constructive content

`FiniteWeightedKernelSums.agda` defines finite carriers, exact weighted row and column sums, proof-relevant pointwise inequalities, and exact identity matching.

`NSPairIncidenceKernel.agda` defines the generic finite pair-incidence fold.

`NSFourierBiotSavartTriadKernel.agda` adds:

- resonant triads with `p + q = k`;
- nonzero-mode witnesses for both Biot–Savart denominators;
- divergence-free background and perturbation fields;
- the exact Fourier velocity-from-vorticity formula;
- the two-term linearized vorticity interaction;
- pointwise insertion into the matching `(target, source)` entry;
- a definitional proof that the constructed Fourier kernel is the pair-incidence fold.

`NSPairIncidenceSchurBridge.agda` transports exact finite-sum certificates into the existing weighted Schur operator theorem through an explicit analytic realization map.

## Productive chain

```text
resonant Fourier triads p + q = k
  -> Biot-Savart velocity from vorticity
  -> linearized triad interaction majorant
  -> exact rectangular K01/K10 entries
  -> exact weighted row/column sums
  -> weighted Schur certificate
  -> C10 * (R0 * C01)
  -> conditional NS frame gap
```

## Remaining frontier

The structural Fourier kernel is now explicit. The remaining analytic and concrete-data obligations are:

1. instantiate `Mode`, vector/scalar arithmetic, mode equality delta, and finite shell lists with the repository's exact Fourier lattice carrier;
2. instantiate the background amplitudes and divergence-free polarization basis used by the active Wall-1 shell model;
3. prove scale-uniform weighted row and column inequalities over the admissible shell family;
4. prove the low-shell resolvent bound;
5. close the strict product budget below the high-shell diagonal gap.

The pointwise pair-incidence identity is definitional for the kernel constructed here. Identifying an external numerical or coarse shell-angle matrix with this kernel still requires an explicit representation theorem. Coarse receipts remain non-promoting without that theorem.
