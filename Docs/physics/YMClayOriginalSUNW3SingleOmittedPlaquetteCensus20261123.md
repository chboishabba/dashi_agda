# YM P0/W3 — full original L4 single-omitted-plaquette census and the interior-time variance

23 November 2026. **Same source**: original periodic side-four four-dimensional SU(N) Wilson product Haar on 256 sites, 1024 positive links and 1536 positive plaquettes. F and G are the *same two original spatial plaquette real normalized trace marks* on time slices 0,d, d=1,2. T_d is the original four-native-temporal-side-plaquettes-per-step cylinder. Reuse original eight-wall coefficient [source](YMClayOriginalSUNW3TwoTimeEightPlaquetteHaarSurface20261123.md), full finite-coupling restricted T identity [source](YMClayOriginalSUNW3RestrictedWallAllCoupling20261123.md) and original F-cap variance [source](YMClayOriginalSUNW3CapActivationVariance20261123.md). This is a **single-omitted-interaction classification**, not a replacement CMP119/122 RG or a W3 full homogeneous bound.

## 1. Exact exhaustive native plaquette incidence, one new coupling at a time

At d=1, T contains four original source walls. Of the other 1532 original plaquettes, ONLY the two marked caps F and G have every link already present in the closed six-face sphere. Each of the other 1530 plaquettes introduces at least three original links that are absent from T and the two original marks: precisely 48 have three new links and 1482 have four new links.

At d=2, T contains eight original walls. Of the other 1528 plaquettes, precisely THREE have all their links inside the original ten-face sphere: F, G, and the *intermediate original time-one spatial plaquette* H=((1,0,0,0),1,2). The remaining 1525 original plaquettes each introduce at least three new original links: 76 have three, 1449 have four. The classifier enumerates **all 1536 original positive 4D plaquettes** and tests actual link sets—not P3^9, ternary labels or approximate spatial distances.

For any **genuinely exterior** plaquette p outside both T_d and the d+1 complete transverse time sections H_0,...,H_d (including the marked caps F and G), activating its arbitrary finite real bare coupling eta while leaving only T_d active otherwise is **exactly invisible to the normalized F/G marked law**. There are precisely 1530 such exterior p when d=1 and 1525 when d=2 on the original L4 torus. Proof: each such p contains at least three original fine links absent from F, G and ALL T_d action terms; choose one as ell. **The statement is false for the d+1 section plaquettes:** their cap/interior activations change the two-mark covariance, as shown in Sections 2 and the cap-variance source note. Conditional on all other links, the unique p holonomy has normalized SU(N) Haar law in ell. Integrating ell sends exp(eta t_p) to the constant z_N(eta) independent of all old source variables. Therefore Z_F, Z_G, Z_FG and Z_0 all gain the same factor, so Cov(F,G) stays exactly equal to its previous restricted-wall value. This argument uses original continuous compact SU(N) product Haar and does not require a finite subgroup surrogate. It remains true at arbitrary *individual* eta, not just first derivative. It does **not** imply joint invisibility after multiple outside couplings are turned on.

## 2. Interior original Euclidean-time H — a new coupling-sensitive W3 response

For d=2, couple **only** the intermediate original plaquette H with gamma, in addition to arbitrary finite couplings beta_q on the eight time-side walls; keep both original end caps F/G as marks, not action couplings. The adjacent four-wall transfer kernels are literal central SU(N) character convolutions on the two original time-one cylinders. Their respective fundamental conditional expectations are

```
E(F | H) = a H,     E(G | H) = b H,
a=product_(q in first 4 walls) m_N(beta_q),
b=product_(q in second 4 walls) m_N(beta_q),
m_N(beta) = int_Haar t(U)e^(beta*t(U)) / int_Haar e^(beta*t(U)).
```

Because the two native slabs share ONLY the original intermediate plaquette links, the first and second slab fields are conditionally independent given those middle links, and their gauge-invariant conditional mark expectations depend only on H. Both slabs' marginal partition functions are independent of H by their original compact Haar invariance; thus the H marginal becomes the original single-plaquette tilted Haar law proportional to exp(gamma H). Taking the conditional covariance correctly, without identifying the original global marks, yields

```
Cov_T,gamma(F,G) = a*b Var_Haar,gamma(H)
                 = m_N'(gamma) * product_(q in T_2) m_N(beta_q).
```

For gamma=0 it recovers the old `v_N product m_N(beta_q)`, where v2=1/4 and v_N=1/(2N²), N>=3. The intermediate H *is not the same field as either end cap*: only the scalar character-variance function has the same form because of the original spherical transfer symmetry. The original physical lattice Euclidean time coordinate is **not** Singer chart k or RG scale.

For SU2 exact continuous Haar Catalan moments (not Z2 sampling), with all eight walls beta and small gamma,

```
Cov(F,G) = m_2(beta)^8 m_2'(gamma),
m_2'(gamma)=1/4-gamma²/32+5gamma⁴/1536-7gamma⁶/23040+O(gamma⁸),
[beta^8 gamma^0] Cov = 1/262144,
[beta^8 gamma^2] Cov = -1/2097152,
[beta^8 gamma^4] Cov = 5/100663296,
[beta^10 gamma^0] Cov = -1/786432.
```

Here bracket coefficients are ordinary Taylor *polynomial coefficients*, not additional derivatives missing factorial factors. The full expression is finite-coupling for this restricted original Wilson source, using imported standard compact-group character convolution. The executable only checks literal geometry and exact SU2 moments, not the continuous convolution theorem itself in a kernel.

## 3. Collective outside channels exist — exact original 3D cube flip

Enumerate all original three-dimensional unit-cube boundaries in the original four-dimensional L4 source. Exactly **24** distinct six-face cube boundaries share exactly ONE of the eight selected temporal wall plaquettes, and share neither marked cap F nor G. Each has five additional original plaquettes *outside* the original ten-face sphere. Replace its shared wall face by those five original cube faces, retaining F,G and the seven remaining walls.

Every replacement has:
- **14 original plaquette faces**, **28 original link edges**, **16 original vertices**, Euler characteristic 16−28+14=2;
- every original positive link used exactly twice;
- zero mod-two boundary and a literal original physically connecting cap-to-cap closed surface.

Therefore the exact single-outside-plaquette Haar-leaf cancellation CANNOT be promoted to a multi-plaquette invisibility law; the original source has alternative closed connecting surfaces built from collective spectator activations. This is a native source **geometry witness** and permissible character-channel candidate, not a calculation of the complete finite-coupling correction or proof of absolute W3 summability. Replacing one wall by five outside faces increases the square-free *surface area* from ten to fourteen (and interacting faces from eight to twelve), but other repeated/branched interaction words and non-spherical sectors remain.

## 4. Acceptance and strict proof boundary

New [standalone exact source checker](../../scripts/check_ym_w3_single_omitted_plaquette_20261123.py) enumerates all native original plaquettes, missing-link histograms, all 24 cube flip surfaces and exact SU2 Haar Catalan/variance jets. Independently executed local equivalent completed all checks PASS. Committed source is source-written and GitHub readback verified; no exact-byte remote checkout rerun, Agda/Lean kernel or GitHub CI claimed. Mathematical factors involving continuous SU(N) Haar leaf and character orthogonality use standard imported compact-group results.

**Precise next absolute W3 payment:** the original named `BalabanLiteralTwoWilsonCMP116ConnectingTailExact.TwoWilsonCMP116PhysicalShellPayment.chargeSumBelowPhysicalRootedShell` is a conditional proof obligation on the **whole** original `connectingClusters` sum. The excluded microscopic exterior factors vanish **singly**, but collective cube-flip patches already show why the full 1536-coupling homogeneous measure needs literal CMP119/122 source-dependent E/R/B/V + FP/Jacobian + both marks + 896 fine spectators, good/large-field controls, pointwise absolute cluster charges and cutoff/volume-uniform physical rooted-shell rate. The current single-extra-plaquette theorem does **not** inhabit that field, identify the true renormalized KP activities or prove the interacting OS/H spectral gap.

Attribution: original Wilson compact SU(N) action, Haar/Schur/Peter–Weyl and standard lattice-gauge character convolution, original Bałaban CMP116/119/122 and DASHI F19/marked charge owners. No fresh Clay claim.
