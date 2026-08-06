# NS/Luo NEMGRO physical audit — Round 20

This round continues the exact Navier–Stokes absorption stack from Round 19. It performs the concrete audit requested against Ryusho Nemoto's manuscript *Global Regularity of the Three-Dimensional Navier–Stokes Equations via a Coupled Energy and Stability Framework* (PhilArchive record `NEMGRO`, no DOI located), while advancing the positive periodic directional route through exact Fourier-symbol and finite kernel-cell mathematics.

No theorem from the manuscript is imported. Every claimed shortcut is tested against its actual algebra, scaling and sign.

## 1. Gradient identity sign

For a gradient matrix `G`, each column `g_k` satisfies

```text
g_k^T G g_k = g_k^T Sym(G) g_k.
```

The implementation proves this division-free as

```text
2 rawQuadratic = symmetricNumeratorQuadratic
antisymmetricNumeratorQuadratic = 0.
```

Summing the three columns gives the exact pointwise cubic in the differentiated convection term.

If

```text
S = S+ - S-,
```

then the gradient-energy right-hand side is

```text
-<S grad u,grad u>
  = -<S+ grad u,grad u> + <S- grad u,grad u>.
```

Thus positive strain is favourable in the gradient identity; negative strain is the potentially amplifying part. This is kept distinct from vorticity stretching, whose sign orientation is the reverse.

## 2. Literal projected-Korn counterexample

On the unit cube,

```text
u(x,y,z) = (2x,-y,-z)
```

has

```text
div u = 0,
grad u = S(u) = diag(2,-1,-1),
grad S(u) = 0.
```

The positive projector keeps the first row, so

```text
|Pi+ grad u|_F^2 = 4,
S+[grad u,grad u] = 8.
```

Consequently, for every coefficient `C`,

```text
C |grad S|^2 = 0 < 4,
C |grad S|^2 = 0 < 8.
```

This directly refutes the manuscript's localized projected Korn lemma as stated.

## 3. Divergence-free compact-support core

The exact vector potential

```text
A(x,y,z) = (0,-xz,xy)
```

satisfies

```text
curl A = (2x,-y,-z).
```

For a scalar cutoff `chi`, the branch expands the complete gradient jet of

```text
u = curl(chi A)
```

through the second derivatives of `chi`. The divergence cancels identically for every jet. On a plateau where

```text
chi = 1,
grad chi = 0,
grad^2 chi = 0,
```

the gradient is exactly `diag(2,-1,-1)` and the positive-strain density is exactly `8`.

A standard smooth compactly supported plateau cutoff supplies the analytic field on `R^3`. The repository currently lacks a constructive-real bump-function library, so the bump constructor itself remains an explicit boundary; the vector-potential, curl, divergence, plateau and positivity calculations are checked.

## 4. Amplitude scaling no-go

Let the checked base positive response be `8` and the finite base Laplacian energy be `d >= 0`. For any proposed coefficient `C >= 0`, choose

```text
r = C d + 1.
```

The exact gap is

```text
8 r^3 - C r^2 d = r^2 (7 C d + 8) > 0.
```

Therefore no universal scale-free coefficient can control the cubic strain response by a quadratic dissipation on every amplitude rescaling.

## 5. Correct three-dimensional interpolation

The manuscript's displayed `L4` interpolation uses the wrong exponents. The correct three-dimensional pattern is

```text
||grad u||_4
  <= C ||grad u||_2^(1/4) ||grad^2 u||_2^(3/4),
```

hence

```text
||grad u||_4^2
  <= C ||grad u||_2^(1/2) ||grad^2 u||_2^(3/2).
```

The branch proves the radical-free Young identity

```text
3 x^4 + y^4 - 4 x^3 y
  = (x-y)^2 ((x+y)^2 + 2x^2) >= 0.
```

When `x^4` represents Laplacian dissipation and `y^4` represents the sixth power of the gradient norm, the resulting closure necessarily contains a `||grad u||_2^6` remainder. It is not unconditional linear absorption.

## 6. Coupling parameter sign

Starting from

```text
S' <= C2 (E + D),
T = E + alpha S,
```

the Laplacian coefficient is

```text
2 nu - alpha C2,
```

and the new positive energy source is

```text
alpha C2 E.
```

The branch proves:

```text
2 nu <= alpha C2
  => 2 nu - alpha C2 <= 0,

alpha C2 = 2 nu
  => 2 nu - alpha C2 = 0.
```

Increasing `alpha` therefore destroys rather than creates a strict dissipative coefficient. A valid coupled functional must produce a negative stability response cancelling nonlinear transfer.

## 7. Spectral-projector gap dependence

For

```text
S+(r) = diag(r,-r),
S-(r) = diag(-r,r),
```

the positive projectors are

```text
P+ = diag(1,0),
P- = diag(0,1).
```

The branch checks

```text
|P+ - P-|_F^2 = 2,
|S+(r) - S-(r)|_F^2 = 8r^2,
gap(r) = 2r,
|P+ - P-|_F^2 gap(r)^2
  = |S+(r) - S-(r)|_F^2.
```

The inverse-gap dependence is therefore literal. At the crossing `r=0`, the matrices coincide while the one-sided projectors remain distinct. Measurability does not supply a uniform derivative estimate.

## 8. Periodic Biot–Savart Fourier symbol

For a nonzero periodic wavevector `k`, transverse vorticity `omega`, and inverse-radius witness

```text
|k|^2 inv = 1,
k dot omega = 0,
```

the branch proves the vector triple-product identity and reconstructs the transverse vorticity from the curl numerator. It defines the twice-strain symbol

```text
2 S_ij = -inv (k_j c_i + k_i c_j),
c = k cross omega,
```

and proves the symbol symmetric and trace-free. The zero mode is represented separately and mapped to zero.

This is the finite Fourier-symbol part of the periodic Biot–Savart operator. The periodized principal-value kernel, smooth remainder and Calderón–Zygmund estimate remain analytic producers.

## 9. Directional kernel factor

For a unit radial direction `r`, the exact scalar triple product satisfies

```text
(r dot (omega_x cross omega_y))^2
  <= |omega_x cross omega_y|^2.
```

Combined with the checked physical Gram identity,

```text
|omega_x cross omega_y|^2
  = a^2 b^2 Theta(xi,eta),
```

this gives the exact radical-free directional estimate

```text
triple^2 <= a^2 b^2 Theta.
```

Thus the unsquared estimate carries `sqrt(Theta)` and the squared estimate carries `Theta`.

## 10. Finite directional high-high shell bridge

A finite shell is represented by literal nonnegative kernel-weighted cells. Each cell satisfies

```text
weight * triple^2
  <= weight * a^2 b^2 Theta.
```

Recursive finite summation yields

```text
finiteHHTransferSquared
  <= finiteDirectionalEnvelope.
```

Any proved envelope absorption estimate then transports to the finite high-high transfer. This is a genuine finite P4 bridge; it does not manufacture the continuum annular kernel or a strict viscosity coefficient.

## Source authority

Headers attach author/title/identifier metadata for:

- Evan Miller, *A Regularity Criterion for the Navier–Stokes Equation Involving Only the Middle Eigenvalue of the Strain Tensor*, DOI `10.1007/s00205-019-01419-z`;
- Peter Constantin and Charles Fefferman, *Direction of Vorticity and the Problem of Global Regularity for the Navier–Stokes Equations*, DOI `10.1512/iumj.1993.42.42034`;
- Jean-Michel Bony, *Calcul symbolique et propagation des singularités pour les équations aux dérivées partielles non linéaires*, DOI `10.24033/asens.1404`;
- Zoran Grujić, *A Geometric Measure-Type Regularity Criterion for Solutions to the 3D Navier–Stokes Equations*, DOI `10.1088/0951-7715/26/1/289`;
- Tosio Kato, *Perturbation Theory for Linear Operators*, DOI `10.1007/978-3-642-66282-9`;
- Roger Temam, *Navier–Stokes Equations: Theory and Numerical Analysis*, DOI `10.1090/chel/343`;
- Charles R. Doering and J. D. Gibbon, *Applied Analysis of the Navier–Stokes Equations*, DOI `10.1017/CBO9780511608803`;
- Shin-ichi Inage, DOI `10.20944/preprints202603.1591.v1`, explicitly marked non-peer-reviewed;
- Ryusho Nemoto, PhilArchive record `NEMGRO`, no DOI located, explicitly marked an audit target rather than an authority.

## Remaining highest-alpha physical frontier

The false static shortcut is now closed at the exact finite/algebraic level. The live path remains:

```text
periodized principal-value Biot–Savart kernel
-> physical directional kernel estimate
-> annular/shell-localized HH operator bound
-> good-time strict absorption
-> PDE-produced bad-time residence compression
-> seven-source critical weighted summability
-> eta_good + eta_bad + eta_lower < 1
-> uniform H^(1/2) estimate
-> critical continuation.
```

The nearest concrete analytic producers are:

1. construct the periodic principal-value kernel from the checked nonzero-mode multiplier;
2. prove the singular-kernel cancellation and smooth periodic remainder;
3. transport the squared directional triple estimate through the annular kernel;
4. identify every collar, pressure, tail and localization source;
5. prove a PDE residence/evolution theorem for bad coherent intervals.

No unconditional regularity theorem is asserted in this round.
