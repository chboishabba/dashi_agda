# NS localized-BKM variable dictionary

This document fixes the meanings of cutoff and scale variables used by the
localized Navier–Stokes continuation lane. It is normative documentation for
new Closure modules: a variable called `N`, `p`, `cutoff`, or `depth` must be
identified with one of the roles below before decay rates are compared.

## Canonical roles

| Role | Preferred name | Mathematical meaning | Typical growth |
|---|---|---|---|
| Littlewood–Paley shell index | `p`, `shellIndex` | Integer dyadic shell label | linear in shell number |
| Dyadic wavenumber | `lambdaP`, `dyadicWavenumber` | `2^p` under Luo's convention | exponential in `p` |
| Parabolic window denominator | `lambdaPSquared`, `parabolicDenominator` | `lambdaP^2 = 2^(2p)` | exponential in `p` |
| Finite Fourier-mode count | `modeCount` | Number of lattice modes in a finite truncation | approximately cubic in wavenumber in 3D |
| Profile depth | `profileDepth` | Combinatorial depth in the Schur/profile graph | repository-defined; not automatically a shell index |
| Galerkin cutoff | `galerkinCutoff` | Finite approximation parameter | implementation-defined |

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

## Current module mapping

| Module family | Current variable | Intended role |
|---|---|---|
| `NSTriadKNLuo*` | `cutoff`, `shellIndex` | Littlewood–Paley shell index |
| `NSTriadKNProfileDepthGeometryCutoffIndexedExact` | `N` | profile-depth cutoff |
| `NSTriadKNProfileCross*` | `N` | profile/Schur cutoff; physical identification still required |
| `NSTriadKNOutputRelocation*` | `lowShell`, `gap` | dyadic shell and shell separation |
| finite lattice/Galerkin modules | `R`, `cutoff` | finite spatial or Galerkin truncation |

## Source

Xiaoyutao Luo, *A Beale–Kato–Majda Criterion with Optimal Frequency and
Temporal Localization*, Journal of Mathematical Fluid Mechanics 21 (2019),
article 1. DOI: `10.1007/s00021-019-0411-z`; arXiv DOI:
`10.48550/arXiv.1803.05569`.
