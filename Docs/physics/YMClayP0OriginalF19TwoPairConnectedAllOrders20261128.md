# Original Wilson F19 adjacent-pair mixed derivatives — 28 November 2026

**Owner/provenance:** continuation of original 4D SU(N) Wilson 1536-face
L=4 positive-link enumeration in
`Docs/physics/YMClayP0OriginalSUNF19TwelveStapleCenterHaarBaryonAndNonfactorization20261123.md`.
This is not a new gauge-field model, Haar substitute or original CMP119 T.
All N >= 2. Original Wilson and Bałaban are original physical/source owners;
DASHI's contribution is the source-specific higher-order algebra below.

## Exact source

On the **same original two adjacent y/z F19 pairs** at x=(0,0,0,0),
W_y=W_z=I, with all 1020 other original positive links held at identity,
the already checked full native 1536-face action is

  S_N(theta,phi) = 2/N [11(1-cos theta)+11(1-cos phi)
                          +(1-cos(phi-theta))].

The original enumeration has 1513 untouched faces, 11 y-only faces,
11 z-only faces and **one** shared yz plaquette. The latter is the only
source of any mixed derivative. This is NOT a product of 64 independent
one-pair conditional sources.

## All-order exact connected analytic identity

For integers m,n>=1:

- m+n odd: (partial_theta^m partial_phi^n S_N)(0,0)=0.
- m+n=2k: (partial_theta^m partial_phi^n S_N)(0,0)
           = -(2/N) (-1)^(m+k).

Proof directly from the original source: single-variable 11-term pieces
differentiate to zero when both m,n are positive. Differentiating
cos(phi-theta) yields an additional (-1)^m from theta derivatives, and
cos(2k*pi/2)=(-1)^k from the cosine's 2k-th derivative at zero.
The minus sign comes from 1-cos. No finite N-dependent approximation,
factorization, commutation of source integration, or termwise absolute
cluster estimate is used.

Concrete original derivatives:

  S_{theta phi}   = -2/N,
  S_{theta theta phi phi} = -2/N,
  S_{theta theta theta phi} = +2/N,
  S_{theta phi phi phi} = +2/N.

For the genuine original fixed-background Gibbs density
W(theta,phi)=exp(-beta S_N(theta,phi)), the mixed derivatives of
log W are -beta times these (normalization constant is phase-independent
on this fixed original slice). In particular

  partial_theta^2 partial_phi^2 log W|0 = +2 beta/N.

This is a nonzero fourth connected derivative on the ACTUAL
source slice for every beta>0. A Gaussian truncation that matches the
mixed Hessian has zero fourth connected log derivative and is NOT an
identity for this native Wilson source. An independent-product surrogate
already fails at mixed second order. Neither observation proves a
positive or negative physical CMP116 absolute spatial cluster activity.

## Executable acceptance

`scripts/check_ym_original_two_pair_all_mixed_derivatives_20261128.py`
checks all 64 symbolic (m,n) with 1<=m,n<=8, all four displayed
derivative identities, and five selected SU(N) ranks using SymPy.
These are exact symbolic checks of the already-enumerated source
formula. They do not independently rerun the original face enumeration
or establish the CMP119/122 constrained Omega/Lambda/S or SI bound.

## Forward endpoint cut

Use the existing original 12-staple continuous Haar source, signed
baryon/meson sectors and two-pair inherited coupling at the SAME
constrained Bałaban T history (S inside T; do not multiply independent
one-pair Z_N). Source-preserve the mixed derivative family through
each conditional integration with its true W-dependent connected
remainder, then obtain an actual termwise absolute CMP116
rooted-shell majorant **uniform in cutoff and volume at beta(a)**.
The all-order parity identity is an obstruction/required control,
not the majorant. Physical noncollapsed continuum measure,
OS positivity and same-H strictly positive nonvacuum mass remain open.
No Agda native kernel/CI or Clay endpoint claim.
