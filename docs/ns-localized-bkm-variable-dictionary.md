# NS localized-BKM variable dictionary

This document fixes the meanings of cutoff, scale, solution-class and multiplier
constants used by the localized Navier–Stokes continuation lane. It is normative
documentation for new Closure modules: a variable called `N`, `p`, `cutoff`,
`depth`, or a constant called `BernsteinConstant` must be identified with one of
the roles below before decay rates or operator norms are compared.

## Canonical roles

| Role | Preferred name | Mathematical meaning | Typical growth |
|---|---|---|---|
| Littlewood–Paley shell index | `p`, `shellIndex` | Integer dyadic shell label | linear in shell number |
| Dyadic wavenumber | `lambdaP`, `dyadicWavenumber` | `2^p` under Luo's convention | exponential in `p` |
| Parabolic window denominator | `lambdaPSquared`, `parabolicDenominator` | `lambdaP^2 = 2^(2p)` | exponential in `p` |
| Finite Fourier-mode count | `modeCount` | Number of lattice modes in a finite truncation | approximately cubic in wavenumber in 3D |
| Profile depth | `profileDepth` | Combinatorial depth in the Schur/profile graph | repository-defined; not automatically a shell index |
| Galerkin cutoff | `galerkinCutoff` | Finite approximation parameter | implementation-defined |

## Official finite Fourier convention

The selected official finite periodic convention is coefficient-unitary. The
physical and coefficient `L2` quantities use the same duplicate-free finite
Fourier fold, and the official finite Hermitian pairing is the corresponding
finite coefficient pairing. Parseval is definitional for this selected
convention.

This does not make every unrelated continuum-measure representation
definitionally identical. Any additional continuum realization must still
identify its physical norm or pairing with the selected official finite fold.

## Luo radial multiplier convention

Luo uses a fixed smooth radial cutoff `chi` satisfying

```text
chi(r) = 1  for r <= 3/4
chi(r) = 0  for r >= 1.
```

The selected realization is the normalized exponential transition

```text
eta(t) = 0         for t <= 0
eta(t) = exp(-1/t) for t > 0

chi(r) = eta(1-r) / (eta(1-r) + eta(r-3/4)).
```

At shell `p`, the smooth low-pass symbol is `chi(2^-p |k|)`. The repository hard
low-pass at `p + 1` contains that support, so the exact coefficient identity is

```text
S_p = M_p H_(p+1).
```

The periodized dyadic kernel is normalized by

```text
K_p^T(x) = sum_(n in Z^3) 2^(3p) check-chi(2^p (x + 2pi n)),
```

and the standard imported estimate is

```text
||K_p^T||_L1(T^3) <= ||check-chi||_L1(R^3) = C_chi,
```

uniformly in `p`. This is a pointwise multiplier factorization and kernel
estimate. A smooth radial symbol is not silently replaced by a finite scalar
linear combination of hard-shell indicators.

## Three distinct constants

| Constant | Meaning | Permitted source of scale loss |
|---|---|---|
| `derivativeBernsteinConstant` | `L-infinity -> L-infinity` derivative estimate | one wavenumber factor `2^p` |
| `finiteModeL2ToLInfinityConstant` | finite-mode `L2 -> L-infinity` estimate in three dimensions | mode-count factor, typically `2^(3p/2)` |
| `hardSmoothMultiplierLInfinityConstant` | `L-infinity -> L-infinity` norm of the already-differentiated smooth multiplier | scale-uniform periodic kernel `L1` norm only |

The first two constants cannot inhabit the third role. In the hard/smooth
comparison differentiation has already been applied on both sides; neither a
new derivative factor nor an `L2 -> L-infinity` mode-count factor is allowed.

## Leray–Hopf and pre-terminal regularity

The official weak-solution carrier records

```text
u in L-infinity(0,T;H) intersection L2(0,T;V),
```

distributional periodic Navier–Stokes, strong `L2` continuity at `0+`, and the
unit-viscosity energy inequality

```text
||u(t)||_2^2 + 2 integral_0^t ||grad u(s)||_2^2 ds
  <= ||u_0||_2^2.
```

Luo's continuation theorem additionally assumes regularity on `(0,T)`. The
exact hard-high cutoff energy identity is licensed by that prior regularity and
classical projected testing. It is not derived from the general Leray–Hopf
energy inequality. In the cutoff data, `physicalDissipation` means exactly

```text
2 integral ||grad u_{>=p}||_2^2.
```

Pointwise absolute cutoff flux and its time integral are distinct quantities and
must be connected by an explicit integration witness.

## Rules

1. Never rewrite `(N + 1)^-1` or `(N + 1)^-2` as a dyadic decay without an
   explicit theorem identifying `N` with `2^p` or a comparable wavenumber.
2. Never identify profile depth with shell index merely because both were
   historically named `N`.
3. Luo's parabolic window is indexed by the shell label `p` but has duration
   proportional to `lambda_p^-2 = 2^(-2p)` under viscosity normalization
   `nu = 1`.
4. Mode-count Bernstein losses must be expressed through the actual spatial
   dimension and cutoff geometry, not through the profile-depth variable.
5. The low-pass quantity in Luo's theorem is the full gradient
   `||∇ u_{≤p}||_∞`, not merely curl or a single-shell vorticity norm.
6. Weighted Schur is used on the flux/energy factor. It does not by itself
   derive the low-pass gradient smallness hypothesis.
7. Hard-projector orthogonality requires both idempotence and Hermitian
   self-adjointness. The coefficient theorem and the official finite Parseval
   selection must be named separately.
8. A `standardImported` multiplier or continuation theorem does not promote a
   route until the repository carrier and every source hypothesis are matched.
9. Never replace the Leray–Hopf energy inequality by equality. Exact cutoff
   energy identities must cite the separate pre-terminal regularity witness.
10. Never identify pointwise flux with integrated flux. The time-integration
    witness is a separate proof object.

## Current module mapping

| Module family | Current variable | Intended role |
|---|---|---|
| `NSTriadKNLuo*` | `cutoff`, `shellIndex` | Littlewood–Paley shell index |
| `NSTriadKNProfileDepthGeometryCutoffIndexedExact` | `N` | profile-depth cutoff |
| `NSTriadKNProfileCross*` | `N` | profile/Schur cutoff; physical identification still required |
| `NSTriadKNOutputRelocation*` | `lowShell`, `gap` | dyadic shell and shell separation |
| finite lattice/Galerkin modules | `R`, `cutoff` | finite spatial or Galerkin truncation |

## Sources

Xiaoyutao Luo, *A Beale–Kato–Majda Criterion with Optimal Frequency and
Temporal Localization*, Journal of Mathematical Fluid Mechanics 21 (2019),
article 1. DOI: `10.1007/s00021-019-0411-z`; arXiv DOI:
`10.48550/arXiv.1803.05569`.

Jean Leray, *Sur le mouvement d'un liquide visqueux emplissant l'espace*, Acta
Mathematica 63 (1934), 193–248. DOI: `10.1007/BF02547354`.

Hajer Bahouri, Jean-Yves Chemin, and Raphael Danchin, *Fourier Analysis and
Nonlinear Partial Differential Equations*, Springer, 2011. DOI:
`10.1007/978-3-642-16830-7`.
