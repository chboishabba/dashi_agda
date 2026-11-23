# YM P0/W3 — 24 original 4D Wilson cube-flipped connected twelve-coupling coefficients

23 November 2026. Canonical current-master source. **Reuse, do not replace:** original 256-site/1024-positive-link/1536-positive-plaquette periodic side-four SU(N) Wilson/Haar action; the original time-0 and time-2 normalized real Wilson plaquette marks F,G; original eight temporal wall interactions T, the 23-Nov single-extra-plaquette census, true F19 1/F/G/FG global marks and 896 spectators; existing literal CMP116 connecting shell and CMP119/122 RG. This is an EXACT selected multivariate bare-source coefficient via native 4D incidence and imported standard SU(N) Haar orthogonality. No new physical model or arbitrary reconstructed Hamiltonian.

## Source-specific 24 physically distinct connecting surfaces

The original d=2 (1,2)-spatial-plaquette two-mark connection has eight side interaction plaquettes T. An original three-dimensional elementary cube boundary c consists of SIX original 4D plaquettes. Among all original oriented native 3D cube boundaries, EXACTLY 24 have |c intersect T|=1 while neither marked cap is in c.

For each one, remove its ONE shared side wall q and add the other FIVE source-physical cube faces c minus {q}. The **actual** twelve distinct interaction labels are

```
Q_c = (T \ {q}) union (c \ {q}),  |Q_c| = 7+5=12.
S_c = {F,G} union Q_c,                |S_c| = 14.
```

All 24 Q_c are pairwise distinct. The resulting original Wilson closed, orientable 2-complex satisfies `V=16,E=28,F=14, Euler=2` and uses each of its 28 original link variables exactly twice with opposite orientation (after coherent face orientation). The exact 4D source incidence and signed orientation are independently checked for all 24, not inferred from an indexed 9-trit graph.

## Full proper-subset Haar-leaf / connectedness gate

For each original source Q_c the independent exact GF(2) plaquette-to-link boundary checker enumerates **all 2^12=4096 subsets**. For any PROPER A subset Q_c, the 2-chain `F+G+sum(A)` has nonzero native 1024-link mod-two boundary, hence a singly appearing original Haar link and a zero Haar moment `int F G prod_(p in A) t_p = 0`. Moreover, for EVERY subset A (including the full Q_c), neither `F+sum(A)` nor `G+sum(A)` has zero boundary. Their corresponding single-mark Haar moments vanish.

The full Q_c has `boundary(F+G+sum(Q_c))=0`. Exact subset gates: 24 x 4096 = **98,304** parity checks, all PASS in the independent local native original L4 checker. The last masks are the ONLY selected proper-subset-free F+G completions in their own Q_c families.

This is enough to isolate the selected twelve-distinct-interaction mixed derivative of the **connected covariance** (i.e. mixed globally marked log jet) at ALL original plaquette bare couplings zero:
```
D_c = (prod_(p in Q_c) partial_(lambda_p))
      Cov_lambda(F,G)|_(all lambda=0)
    = int_(SU(N)^1024) F G prod_(p in Q_c) t_p dH^1024.
```
Even though nonmarked partition `Z` has nonzero other derivatives, it cannot contribute to this twelve-fold selected derivative because ALL proper FG numerators vanish. This does not require full common-beta cluster cancellations.

## Exact original continuous SU(N) character tensor contraction

The standard imported continuous Haar fundamental formula `int U_ab (U^-1)_cd dH(U)=delta_ad delta_bc/N` applies to each doubly used original link after coherent face orientation. The source checker constructs and contracts the 56 oriented face-index slots, obtaining 16 independent index loops and 28 factors `1/N` for 14 normalized fundamental traces. Hence each coherent globally oriented assignment contributes

```
N^(16-28-14) = N^-26.
```

For SU(N>=3), centre invariance on the original twice-used links leaves two coherent trace/conjugate orientations among 2^14 sign choices, yielding `2^(1-14)N^-26=2^-13 N^-26`. For SU(2), the fundamental trace is real and equals its conjugate, yielding `2^-26` directly. Therefore each of the 24 original selected derivatives has **strictly positive exact** coefficient

```
D_c = 2^-26                       for SU2;
D_c = 2^-13 N^-26                 for SU(N>=3).
```

This is four more interaction faces than the previous eight-wall surface and eight more original Haar-index powers in the exponent (previous SU2 2^-18 vs now SU2 2^-26). For homogeneous *formal* beta, each labelled selection Q_c contributes its own positive `beta^12 D_c` term to a distinct-coupling multivariate jet. The sum over these 24 selected labels would be `24 D_c`, **not** the full homogeneous beta^12 Taylor coefficient: the latter also contains other distinct-face configurations, repeated faces, lower-order normalisation and disconnected cumulant combinations. No monotonicity of the full homogeneous covariance under beta follows.

A standard Haar lemma, not separately kernel formalized, underwrites the continuous SU(N) character reduction. The exact local algorithm verifies native incidence, mod-two subset obstruction, actual orientability and delta-index loop algebra. It does NOT numerically integrate the continuous 1024-fold Haar product, nor construct a cutoff-independent cluster expansion.

## W3 maximum-cut consequence and physical separation

**New proved bare-source fact:** exactly 24 *witnessed* independent sets of five simultaneously active spectator factors can replace one source wall and contribute a strictly positive, time-separated connected twelve-coupling derivative. Each spectator alone remains exactly invisible in the restricted-wall source (previous census). Thus nonlocal connecting correction families arise first as genuinely interacting *collections*, and must appear in any source-faithful full-shell activity model.

**Not proved:** that *five* is the absolute first possible collective spectator order over every original Wilson interaction word at arbitrary wall couplings (repeated plaquette terms, other surfaces and centre/representation interactions are not exhausted); that 24 are all order-12 connected contributions; an absolute correction bound; the homogeneous weak-coupling physical beta(a); CMP119/122 E/R/B/V/FP/Jacobian source-identical renormalized activity; uniform physical W3 rooted shell, original E1 interacting OS and same-H D2 nonvacuum gap.

The existing Agda `BalabanLiteralTwoWilsonCMP116ConnectingTailExact.TwoWilsonCMP116PhysicalShellPayment.chargeSumBelowPhysicalRootedShell` and `BalabanLiteralTwoWilsonSourceFirstJetLocalizationExact.SourceFirstLiteralWilsonJetLocalization.localizedLiteralShellChargeSum` remain explicitly **uninhabited physical inputs**, not repaired by a positive sphere coefficient. Preserve actual Euclidean t, chart k and RG scale separately; the surface is native 4D, not an H05 face count or RH/NS analytic zero.

## Execution / attribution

Locally executed original L4 exact checker independently: **PASS 98,304/98,304 GF2 subset checks, 24/24 actual 4D oriented surface contractions, exact SU2/SU3/SU4/SU5/SU6 coefficients**. New committed [reproducible checker](../../scripts/check_ym_w3_cube_flip_connected_coeff_20261123.py) source-written and GitHub-readback; no claimed exact-byte replay of this blob, Agda 2.9 typecheck, Lean kernel or GitHub CI. Attribution: original Wilson lattice and compact Haar, standard SU(N) fundamental Peter-Weyl/Schur orthogonality, Bałaban CMP116/119/122 and existing DASHI original marked Wilson/F19 owners.
