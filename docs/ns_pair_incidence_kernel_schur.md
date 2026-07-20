# NS pair-incidence kernel Schur bridge

## Purpose

This tranche replaces an unnamed “concrete rectangular kernel” obligation with an exact finite construction and instantiates it with the linearized Fourier-vorticity Biot–Savart interaction on the integer lattice \(\mathbb Z^3\).

For enumerated source modes, target modes, and resonant triads, the transfer entry is

\[
K(k,q)=\sum_{p+q=k}\operatorname{majorant}\bigl(DN_{\bar\omega}(p,q)\eta_q\bigr).
\]

## Exact lattice and Wall-1 data

`NSIntegerFourierLattice.agda` fixes the mode carrier to triples of Agda integers, with exact mode addition, negation, nonzero witnesses, resonance, shell predicates, and shell separation.

`NSWall1FourierShellInstance.agda` packages the active finite Wall-1 family:

- low- and high-shell predicates;
- finite active low/high mode lists;
- proof that active modes inhabit their declared shells;
- amplitude-scaled background vorticity;
- target/source mode lists and weights;
- exact resonant triads;
- divergence-free background and perturbation fields.

`NSDivergenceFreePolarizationBasis.agda` and `NSWall1PolarizationInstantiation.agda` make the polarization basis and mode-by-mode background/perturbation label selections proof-relevant.

## Fourier convention

For nonzero Fourier mode `p`, velocity is reconstructed from vorticity as

\[
u_p=|p|^{-2}(p\times\omega_p).
\]

The vorticity interaction is

\[
T(p,q;\omega_p,\omega_q)
=(\omega_p\cdot q)u_q-(u_p\cdot q)\omega_q.
\]

Linearization around background vorticity uses

\[
T(p,q;\bar\omega_p,\eta_q)+T(q,p;\eta_q,\bar\omega_p).
\]

The Schur kernel records a declared nonnegative vector majorant. It does not use sign or phase cancellation.

## Uniform weighted theorem surface

`NSWall1UniformWeightedSchur.agda` quantifies over a scale-indexed Wall-1 family and requires one pair of constants valid for every scale:

\[
\sum_q K_j(k,q)w_Q(q)\le C_R w_K(k),
\qquad
\sum_k K_j(k,q)w_K(k)\le C_C w_Q(q).
\]

Those uniform inequalities construct a finite weighted Schur certificate at every scale. Separate families provide the `K01` and `K10` directions.

## Productive chain

```text
integer Fourier modes Z^3
  -> active Wall-1 low/high shell lists
  -> amplitude and divergence-free polarization data
  -> resonant Fourier triads p + q = k
  -> Biot-Savart velocity from vorticity
  -> linearized triad interaction majorant
  -> exact rectangular K01/K10 entries
  -> scale-uniform weighted row/column inequalities
  -> weighted Schur certificates
  -> C10 * (R0 * C01)
  -> conditional NS frame gap
```

## Remaining frontier

The structural lattice, shell, amplitude, polarization, and uniform-quantifier layers are now explicit. Still open:

1. populate the active Wall-1 lists and amplitude values with the canonical dataset/model instance;
2. instantiate the exact scalar/vector arithmetic and mode delta used for evaluation;
3. prove the scale-uniform row and column inequalities for that instance;
4. prove the low-shell resolvent bound;
5. close `C10 * R0 * C01 < delta11`.

No numerical audit or coarse shell-angle matrix receives theorem authority without an explicit representation theorem matching its modes, triads, weights, amplitudes, and kernel entries to these objects.
