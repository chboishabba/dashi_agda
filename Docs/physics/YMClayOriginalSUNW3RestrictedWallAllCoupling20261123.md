# YM P0/W3 — original SU(N) two-mark wall: exact restricted finite-coupling character channel

Date: 23 November 2026. **Source ownership:** original full 4D SU(N) Wilson/Haar/F19 finite Gibbs, `YMClayOriginalSUNW3TwoTimeEightPlaquetteHaarSurface20261123.md`, `scripts/check_ym_original_sun_w3_two_time_tube_20261123.py`; historical compact-group character convolution and two-dimensional lattice gauge Haar reduction. Existing CMP116/119/122 rooted-shell compilers and original physical E1/OS remain independent. This note does not replace those sources.

## Original geometry and the restriction

Keep all 256 sites, 1024 original positive SU(N) links, 1536 six-plane original positive plaquettes on the side-four lattice. Let F and G be the actual normalized real fundamental Wilson plaquette marks on the same (1,2) spatial face at time 0 and time d=1 or 2 (for d=2 they are precisely the existing original two-time marks). Let T_d be the 4d actual original temporal side plaquettes of their rectangular time-prism. **Only the interaction couplings on T_d are active**; the two cap plaquettes are MARKS and are not coupled. The remaining 1536-4d physical plaquettes and all original links still exist, with other bare couplings set to zero in this selected *restricted original Wilson family*. The full homogeneous Wilson action with all couplings equal beta is NOT covered.

Let `t(U)=ReTr(U)/N` and `z_N(beta)=integral_SU(N) exp(beta*t(U)) dH(U)`. Define the genuinely original Haar one-face normalized character response

`m_N(beta)=z_N'(beta)/z_N(beta)=E_beta[t(U)]`.

At nonnegative finite beta, compact Haar positivity, t bounded in [-1,1], strict nonconstancy, and positive covariance give `0<=m_N(beta)<1` with `m_N(0)=0` and `m_N(beta)>0` when beta>0. All `beta_q` on the 4d walls may differ.

## Exact all-coupling restricted original source identity

For the normalized connected source of the two original marks, the finite 2D spherical Wilson cell complex formed by the two caps and 4d temporal walls has Euler characteristic 2 and a single shared fundamental character channel. Haar leaf elimination on the original link graph removes all other uncoupled physical edges, and the compact-group character convolution/orthogonality on the closed surface gives:

```
Cov_Td(F,G) = v_N * product_(q in T_d) m_N(beta_q),
  v_2=1/4,
  v_N=1/(2N^2) for N>=3.
```

The one-face `m_N` is a coefficient of the SAME positive original Wilson action. The product is a character-convolution result after integration, NOT an assumption that the two global F/G insertions or their original path-ordered holonomies factor configurationwise. In particular F and G have zero mean because the interaction-free cap attachment leaves one Haar-independent cap channel. Every proper subset `S proper subset T_d` leaves at least one original link on the marked surface as a Haar leaf, so its two-mark covariance is zero for arbitrary finite couplings on S. For all T_d active the covariance is nonzero for positive couplings.

**Character-normalization check:** for N=2, `t=chi_f/2`, and `E_Haar[t²]=1/4`; for N>=3, `t=(chi_f+chi_f*)/(2N)` and `E_Haar[t²]=1/(2N²)`. In each surviving global fundamental-or-conjugate surface channel the sphere amplitude is `N^(V-E-F)` with `(V,E,F)=(4(d+1),8d+4,4d+2)`. There are two coherent real trace orientations for N>=3; the SU2 trace is real. Consequently its selected `4d`-fold mixed derivative at all wall beta=0 equals `v_N^(4d+1)`, exactly the PREEXISTING original source coefficient:
```
d=2: SU2: 2^-18; N>=3: 2^-9 N^-18.
```
For SU2 explicitly `z_2(beta)=2 I_1(beta)/beta`, `m_2(beta)=I_2(beta)/I_1(beta)`, with Bessel functions I_n. The exact rational Taylor jet is `m_2=beta/4-beta^3/96+beta^5/1536-beta^7/23040+...`. The source-specific finite connection is therefore not dependent on a leading-term perturbation expansion.

For a uniform active wall beta and d nonwrapping native time steps,

```
Cov_Td(F,G) = v_N * m_N(beta)^(4d),
absolute restricted-wall shell ratio Q_wall(beta) = m_N(beta)^4 in (0,1).
```

At lattice spacing a>0, this restricted cylinder has formal distance rate

`mu_wall(a,beta) = -(4/a) log m_N(beta)`

for positive finite beta. This is exactly geometric separation on the selected original wall graph at fixed beta; it is **not** a cutoff-uniform rate for a selected beta(a), and not a 4D homogeneous Wilson spectral mass. On a periodic side-four lattice d=2 is the largest shortest time separation; increasing d requires larger original lattices to keep the nonwrapping physical route shortest. A source-rate function written for d->infinity on an L4 torus would be a false physical-distance statement.

## Exact executable acceptance and deliberately negative physical scope

New [original 4D exact source checker](../../scripts/check_ym_w3_restricted_wall_finite_coupling_20261123.py) was run locally with SymPy:
- reconstructs all 1536 physical original L4 plaquettes and each actual d=1,2 capped T_d surface;
- all `2^(4d)-1` proper subsets fail original closed mod-two incidence, both d=1,2;
- original sphere counts E=8d+4, V=4(d+1), F=4d+2 and chi=2;
- exact source leading-coefficient agreement for SU2,3,4,5 for both d;
- exact SU2 Haar Catalan moment expansion and positive 4d-wall response first nonzero orders, including original d=2 8-wall coefficient;
- directly prints the finite-coupling character identity but does NOT numerically evaluate `m_N(beta)` on a nonzero beta input, nor independently prove the character-convolution theorem: that step uses the standard compact-group identity.

**Local script PASS**, committed original checker source re-fetched separately; exact-byte execution of the GitHub checkout and Agda/Lean/CI were not performed.

The genuinely open physical W3 gate is an all-coupling, same-source **termwise ABSOLUTE** bound on the SUM of all differentiated connected 4D original Wilson activities at homogeneous beta(a), including walls, repeated faces, spectators, frustrated/large-field regions, entropy, CMP119/122 constrained E/R/B/V, source-dependent FP/Jacobians, F19 globally unique 1/F/G/FG and original physical separation. The isolated tube is a positive connected coefficient but provides neither an upper bound on other connected surfaces nor a renormalized CMP116 polymer activity estimate. Original 3+1 signature and OS same-H nonvacuum continuum remain separately open.

Preserve separate physical t, Singer chart index k, RG scale, zero-branch and signed-zero provenance; no 369, RH or NS semantic identification is claimed. Attribution: Wilson/Haar, standard compact-group Peter–Weyl/Schur character orthogonality, original Bałaban CMP116/119/122, and original DASHI Wilson/F19 source owners.
