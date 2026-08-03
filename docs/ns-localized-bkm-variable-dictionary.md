# NS localized-BKM variable dictionary

This document fixes the meanings of cutoff, scale and multiplier constants used
by the localized Navier–Stokes continuation lane. It is normative documentation
for new Closure modules: a variable called `N`, `p`, `cutoff`, `depth`, or a
constant called `BernsteinConstant` must be identified with one of the roles
below before decay rates or operator norms are compared.

## Canonical roles

| Role | Preferred name | Mathematical meaning | Typical growth |
|---|---|---|---|
| Littlewood–Paley shell index | `p`, `shellIndex` | Integer dyadic shell label | linear in shell number |
| Dyadic wavenumber | `lambdaP`, `dyadicWavenumber` | `2^p` under Luo's convention | exponential in `p` |
| Parabolic window denominator | `lambdaPSquared`, `parabolicDenominator` | `lambdaP^2 = 2^(2p)` | exponential in `p` |
| Finite Fourier-mode count | `modeCount` | Number of lattice modes in a finite truncation | approximately cubic in wavenumber in 3D |
| Profile depth | `profileDepth` | Combinatorial depth in the Schur/profile graph | repository-defined; not automatically a shell index |
| Galerkin cutoff | `galerkinCutoff` | Finite approximation parameter | implementation-defined |

## Luo radial multiplier convention

Luo uses a fixed smooth radial cutoff `chi` satisfying

```text
chi(r) = 1  for r <= 3/4
chi(r) = 0  for r >= 1.
```

At shell `p`, the smooth low-pass symbol is `chi(2^-p |k|)`. The repository hard
low-pass at `p + 1` contains that support, so the exact coefficient identity is

```text
S_p = M_p H_(p+1).
```

This is a pointwise multiplier factorization. A smooth radial symbol is not
silently replaced by a finite scalar linear combination of hard-shell
indicators.

## Three distinct constants

| Constant | Meaning | Permitted source of scale loss |
|---|---|---|
| `derivativeBernsteinConstant` | `L-infinity -> L-infinity` derivative estimate | one wavenumber factor `2^p` |
| `finiteModeL2ToLInfinityConstant` | finite-mode `L2 -> L-infinity` estimate in three dimensions | mode-count factor, typically `2^(3p/2)` |
| `hardSmoothMultiplierLInfinityConstant` | `L-infinity -> L-infinity` norm of the already-differentiated smooth multiplier | scale-uniform periodic kernel `L1` norm only |

The first two constants cannot inhabit the third role. In the hard/smooth
comparison differentiation has already been applied on both sides; neither a
new derivative factor nor an `L2 -> L-infinity` mode-count factor is allowed.

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
   self-adjointness. The coefficient theorem and the Parseval transport must be
   named separately.
8. A `standardImported` multiplier or continuation theorem does not promote a
   route until the repository carrier and every source hypothesis are matched.

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

Hajer Bahouri, Jean-Yves Chemin, and Raphael Danchin, *Fourier Analysis and
Nonlinear Partial Differential Equations*, Springer, 2011. DOI:
`10.1007/978-3-642-16830-7`.
