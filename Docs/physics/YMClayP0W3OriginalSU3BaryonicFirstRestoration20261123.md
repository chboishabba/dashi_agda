# YM P0 MASS GAP / W3 — first omitted-interaction restoration on original 4D SU(N) Wilson tube

23 November 2026 · master-based YM PR #1536. The Clay **mass gap is P0**. This is one genuine *original Wilson source* coefficient for that route, not a solution of the physical W3 absolute/cutoff-uniform estimate or the continuum OS gap. All SU(N) group and Haar statements below refer to **continuous, independent original SU(N) link Haar**, not a Q8 or Z2 replacement.

## Exact source and derivative being evaluated

Retain the full original four-dimensional periodic L=4 lattice: 256 vertices, 1024 positive links, 1536 positive plaquettes. Let the genuine normalized real trace insertion `t_p=(ReTr P_p)/N` live on the original SU(N) positive-link word. Select the original two time-separated source plaquette marks `F=t_(0,0,0,0;1,2)`, `G=t_(2,0,0,0;1,2)` and the eight four-sided original time-0/time-1 wall plaquettes `T` as in [original two-time sphere](YMClayOriginalSUNW3TwoTimeEightPlaquetteHaarSurface20261123.md). For independent original interaction couplings `lambda_q` on the 8 walls and `eta` applied to **one additional original Wilson plaquette H outside T**, define

`C_N(lambda,eta)= (d_s d_t log integral exp(s F+t G+ sum_(q in T) lambda_q t_q + eta t_H) dH^1024)|_(s=t=0)`.

The single-extra original source derivative is

`D_(N,H) = [ (product_(q in T) d_(lambda_q)) d_eta C_N(lambda,eta) ]_(lambda=eta=0)`.

Its **sum over H in the full omitted complement** of T is the first restoration jet of the other 1528 original Wilson interaction couplings in the already-connected bare tube channel. These are *independent-coupling derivatives at the all-zero coupling point*, not a full homogeneous-beta ninth Taylor coefficient and not an upper bound on the true physical Gibbs covariance.

## New full-native incidence theorem: exactly THREE exceptional omitted faces

The two original end-cap marks plus the eight side faces have exactly 20 distinct original links, with **multiplicity two at each link** and no other occupied links. Of the 1528 original plaquettes outside T:

- **1449** share zero edges with this closed source surface;
- **76** share one edge;
- **3** share all four edges: the two marked caps at times 0 and 2 and the **unmarked intermediate spatial cross-section at time 1**.

Every other omitted H has at least three links appearing only once in the 11-trace integrand. Integrating any such singly occupied original Haar link kills its moment. Hence **1525/1528 first-restoration derivatives vanish for every SU(N>=2)**. The checker generates all 1536 original positive plaquette words and all 1024 original positive link addresses, rather than counting from an auxiliary cube or assuming a boundary geometry.

## Non-Abelian SU(3) correction: the three exceptional insertions survive

For any of the three exceptional H, precisely four original surface links are occupied three times and the other 16 are occupied twice. For SU(2), the fundamental centre element -I negates each triple-link integrand, so the Haar integral is zero. For SU(N>=4), centre selection also kills a triple-link fundamental orientation: each edge charge is one of `-3,-1,1,3`, none divisible by N>=4.

**SU(3) is different.** All three fundamentals or all three antifundamentals have total zero centre charge. There are exactly **two globally permitted** trace-orientation assignments among the 2^11 ReTr choices (checked separately for each H). At every triple-occupied original link use the true SU(3) Haar identity

`int U_(a1,b1) U_(a2,b2) U_(a3,b3) dH(U) = epsilon_(a1,a2,a3) epsilon_(b1,b2,b3) / 6`,

with the conjugated analogue for three antifundamentals; the 16 ordinary paired links use `int U_ab conj(U_cd) dH = delta_ac delta_bd / 3`. After the 16 doubled-link delta identifications, the index graph has **20 color equivalence classes**, of which 12 appear in eight Levi-Civita tensors and eight remain free. An **independent exhaustive 3^12 exact signed-color enumeration** gives an active Levi-Civita contraction of **1296 = 6^4** with no cancellation, leaving the full contraction `3^8 * 6^4` for each of the two allowed orientations.

Including four baryonic Haar denominators, sixteen ordinary Haar denominators, eleven normalized traces and the 2^-11 ReTr orientation factor gives, for **each** H in the three exceptional original plaquettes,

`D_(3,H) = 2 * (3^8 * 6^4) / [2^11 * 3^(11+16) * 6^4] = 1/(2^10 * 3^19) = 1/1190155742208.`

The existing original eight-wall coefficient is `C_3^[8]=1/(2^9*3^18)=1/198359290368`. Therefore

`D_(3,F) = D_(3,M) = D_(3,G) = C_3^[8]/6`,

and the full first restoration derivative over **all 1528 omitted original plaquettes** is

`sum_(H outside T) D_(3,H) = 3*(C_3^[8]/6) = C_3^[8]/2 = 1/396718580736`.

For SU(2) and every SU(N>=4), the corresponding full first restoration derivative vanishes. This is an exact, group-specific *bare marked cumulant* result, not a 4D continuum statement.

## Connectedness, rather than a bare moment

The checker additionally exhausts every nontrivial set partition of the 11 labeled traces `F,G, eight distinct walls, H` into two nonempty subfamilies. No partition has **both** families free of singleton original Haar links. Thus every nontrivial cumulant product includes a factor that vanishes by an exact one-link Haar/centre argument. Consequently the selected eleven-insertion mixed derivative of the normalized log partition is the **same** as the calculated eleven-trace moment. We do not equate a generic unnormalized moment to a connected response without this check.

## Executed and committed local acceptance

[Exact original 4D source checker](../../scripts/check_ym_p0_w3_first_restoration_su3_20261123.py), executed locally with ordinary Python/Fraction and separately checked using NumPy/opt-einsum tensor contraction. **PASS:** all 1536 full source plaquettes, overlap histogram 1449/76/3, 1528 restored-face classification, 2 coherent SU3 orientations for each of the 3 exceptional faces, zero SU2 and N=4/5/6 centre orientation assignments, full proper-partition connectedness negative control, three independent 531441-assignment Levi-Civita sums of 1296 each, exact rational coefficient and half-ratio. Local Git blob `337d54c3180eb9e48e73fcf8ce1d16929b133ec9` is **byte-identical** to GitHub readback of committed checker; the exact core result and proof above are not based only on finite numerical sampling.

No pinned Agda 2.9, CI or original YM kernel claim. The colour contraction is an exact combinatorial reference for standard continuous SU(N) Schur/Haar orthogonality and SU3 determinant, not a self-contained Agda formalization of Haar integration.

## Physical mass-gap P0: what this narrows and what remains OPEN

This payment supplies a genuine source-connected **nonzero original SU(3) baryonic first restored interaction** at zero coupling. It is useful for exact cluster-charge support auditing and warns that SU2 centre/parity screening is **not** group-generic. In particular the SU(3) triple-invariant insertion cannot be dropped in a claimed all-compact-simple-G cluster bound.

It does **not** show the CMP116 source cluster log equals this bare cumulant, that the same original CMP119/122 full `Omega/Lambda/S` constrained T and FP/Jacobian/R/background recognizes the coupling derivative, or that the entire original differentiated **absolute** rooted-shell sum obeys an upper estimate. The unknown homogeneous positive Wilson beta(a), all remaining multivariate higher orders, large-field excitations, scale entropy and volume/UV prefactor cannot be bounded by the first nonzero primitive.

**The controlling mass-gap proof is still:**

1. **P0.T**: same original Wilson/Haar/F19 four unique global marks -> actual non-linear CMP98 Q_B, all original source CMP119/122 ordered/constraint/gauge/FP/Jacobian T and E/R/B/V on physical beta(a), *including both* direct mixed-Hessian and first-score covariance contributions.
2. **P0.W3**: the actual source-localized differentiated CMP116 two-support absolute cluster charge, uniform physical support/distance, volume/cutoff summable scale and positive physical SI rate; include SU3 baryon channels and true large fields.
3. **P0.OS**: noncollapsed interacting continuum reflection-positive Schwinger family; dense gauge-invariant local OS sector and **one same** reconstructed H_OS with strict positive nonvacuum gap. N1 and G1 remain open. A finite selected Wilson coefficient is neither a physical W3 bound nor a mass gap.

Attribution preserved: Wilson and original compact SU(N) Haar/Schur, standard SU(3) epsilon invariant and high-temperature linked-surface expansion, Bałaban CMP98/109/116/119/122, original DASHI F19, existing two-time Wilson tube and source-first CMP116/W3/OS proof owners. No new Wilson measure, source T, Hamiltonian or postulate.
