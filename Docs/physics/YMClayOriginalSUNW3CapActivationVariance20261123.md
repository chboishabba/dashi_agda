# YM P0 — FIRST omitted original Wilson cap interaction: exact variance correction and W3 gate

23 November 2026. Work on ORIGINAL 4D periodic SU(N) Wilson links (256 L4 sites, 1024 original positive links, 1536 native positive plaquettes), actual two unique original real plaquette marks, original SU(N) product Haar, native Euclidean physical time d=1,2 and 4d original time-side plaquettes. Retain full F19 ordered 64-pair / 896 spectator provenance. Previous source owner: [original isolated-wall all-coupling exact character formula](YMClayOriginalSUNW3RestrictedWallAllCoupling20261123.md); [prior eighth mixed original coefficient](YMClayOriginalSUNW3TwoTimeEightPlaquetteHaarSurface20261123.md). Do not reimplement Yang–Mills, a new operator, or CMP116/119/122.

## Source-identified first excluded interaction (the marked cap, not a replacement theory)

Keep the original wall couplings beta_q on 4d source side plaquettes; all remaining interaction couplings are zero EXCEPT the original cap F's existing interaction at bare coupling gamma. The cap G remains a unique global mark with zero bare coupling. Original t(U)=ReTr(U)/N, z_N(lambda)=int_SU(N) exp(lambda*t(U)) dH(U), m_N(lambda)=z'_N/z_N. By the standard central-character convolution for this ORIGINAL spherical two-cap plaquette subcomplex, the cap F marginal at gamma=0 is Haar and the conditional expectation of the distant cap G given F equals (prod_q m_N(beta_q)) F. With the source interaction exp(gamma F) inserted, the cap's original marginal law is tilted by that factor, so

```
E_gamma(G | F) = [product_q m_N(beta_q)] F,
Cov_gamma(F,G) = m_N'(gamma) product_q m_N(beta_q),
m_N'(gamma) = Var_gamma(t(U)) > 0 for finite real gamma.
```

This is the exact **same-source, one-extra-interaction** bridge and first violation of an unwarranted gamma-independent `v_N` prefactor. The cap is still an original physical Wilson plaquette; all other 1536-4d-1 couplings remain zero. The factorization is a post-Haar **character projection**, NOT independent F and G insertions, independent paths, or a scalarized CMP119 T.

At gamma=0, `m'_N(0)=v_N`, recovering the previously sourced isolated-wall identity, where v2=1/4 and v_N=1/(2N²), N>=3. Nonzero gamma does NOT generally preserve the prefactor even on unchanged topology. At finite gamma, `m'_N(gamma)` is a positive variance; for positive gamma -> infinity it tends to zero by cap Haar concentration at the identity, so the isolated bare coefficient cannot remain a universal full-action response.

## Original SU(2) exact rational physical-source jet

Original SU(2) Haar normalized fundamental trace t=cos(theta) has even moments E[t^(2n)]=Catalan(n)/4^n and odd moments zero; hence `z_2(gamma)=2I_1(gamma)/gamma`, `m_2(gamma)=z_2'/z_2=I_2(gamma)/I_1(gamma)`. An exact (not finite-difference) SymPy rational series yields

```
m_2(gamma) = gamma/4 - gamma^3/96 + gamma^5/1536
             - gamma^7/23040 + O(gamma^9)
m_2'(gamma) = 1/4 - gamma^2/32 + 5gamma^4/1536
              - 7gamma^6/23040 + O(gamma^8).
```

With 4d equal wall couplings beta, the joint source jet starts
```
Cov_gamma(F,G)
 = (beta^(4d)/4^(4d)) [1/4 - gamma^2/32 + 5gamma^4/1536
                        - 7gamma^6/23040 + O(gamma^8)]
   + O(beta^(4d+2)).
```
Thus in the ORIGINAL d=2 eight-wall channel, `[beta^8 gamma^0]=1/262144` and `[beta^8 gamma^2]=-1/2097152`. The first 1/262144 is the prior eighth mixed-derivative coefficient; the gamma² correction is a new negative higher mixed-source contribution. The sign of this correction should not be promoted to a sign of unrestricted full covariance.

## Acceptance and physical-rate boundary

New exact [local original L4 SymPy checker](../../scripts/check_ym_w3_original_cap_activation_20261123.py) checks:
- original full 1536 positive plaquette incidence and all missing-wall proper subsets for d=1,2;
- the actual E=8d+4 capped sphere geometry, without erasing original source links;
- literal SU2 continuous-Haar Catalan moment coefficients, cap variance jet and d1/d2 first wall coefficients;
- the negative control to the fictitious constant `v_N` at gamma nonzero.

The local independently executed source-equivalent script PASS. Committed Git code was read back separately; not exact-byte rerun or Agda/Lean kernel. Standard compact-group character convolution is the imported mathematical theorem, not separately proved by this finite source checker.

**W3 P0 remains OPEN:** activating one cap interaction is far from activating all 1536 original plaquette interactions and CMP119/122 all histories. The remaining physical minimum cut is (i) actual same-original global-mark 1/F/G/FG renormalized physical `T` with S internal T, FP/Jacobian, 896 spectators, beta(a); (ii) termwise ABSOLUTE mark-differentiated `BalabanLiteralTwoWilsonSourceFirstJetLocalizationExact` charge plus source-matched CMP116 positive rooted-shell bound including repeated plaquettes, sparse animals and frustrated/large-field sectors; (iii) cutoff/volume-uniform physical distance prefactor and exponent and finally the original E1/OS same-H D2 nonvacuum gap.

Physical Euclidean time coordinate, Singer chart k, RG scale, zero-branch residual and signed zero are all separate. This calculation uses only the native physical 4D source and changes none of those indices. Attribution: original Wilson and compact SU(N) Haar/Peter–Weyl, standard 2D spherical gauge character convolution, existing DASHI/Wilson F19 and CMP116/119/122 source owners.
