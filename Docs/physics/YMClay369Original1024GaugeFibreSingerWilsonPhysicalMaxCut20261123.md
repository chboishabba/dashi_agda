# YM P0 × RH #1533 × indexed 369: original 1024-link Wilson gauge-fibre, Singer-chart geometry, and honest remaining physical welds

Date 23 November 2026. Source integration owner PR #1536 against master; RH geometric finite temporal/intertwiner source PR #1533; H05 369 indexed chart source PR #1291. This is a focused **YM** cross-pollination and original source geometry test; no imported RH operator is asserted to be a physical YM transfer/Hamiltonian.

## 1. What the RH worker actually supplied

RH #1533's \`Docs/proofs/RHNSYMHyperfabricOriginalTemporalSufficientConsumerSubdivision20261123.md\` and \`scripts/check_ym_r445_hyperfabric_signed_midpoint_gauge_fibre_20261123.py\` prove and numerically check an important obstruction. The original side-four 4D YM source gives 16 even-origin coarse sites, 64 positive coarse bonds, and two distinct oriented original fine limbs per coarse bond. Their signed nine-trit projected edges are valid P3^9 source paths at k=0; however the **64 original odd fine midpoint sites** project to **32** signed vertices. Equating these projected vertices equates two independent original SU(N) fine-site gauge factors and is invalid.

The useful RH time result \`U_P3^9(pi)=U_C3^9(pi)=(2J3/3-I3)^{tensor9}\`, and its Singer transport, is a **finite source operator coincidence at selected times**, not an equality of original four-dimensional Wilson transfer dynamics or graph adjacency. The fixed Singer graph/wave operator does NOT commute generally, and k-indexed conjugacy is chart transport. YM must keep the original source graph while transporting the chart.

## 2. Minimum reversible signed-zero fibre; NO opaque extra source ID needed

The original \`YMClayR445Base2ThreeAxis369FibreBIDIExact.agda\` already bijects **all** 1024 original fine positive Wilson bond labels with

\`\`\`
(original coarse oriented bond, axial phase, 3 transverse bits)
64 × 2 × 8 = 1024;
transverse 000 -> 128 exact original selected R445 pair bonds;
7 other sheets -> 896 ORIGINAL interacting spectators.
\`\`\`

Extend **that same existing owner** with the exact source coordinate codec

\`\`\`
C4 site coordinate:   0 ↦ negative trit; 1 ↦ zero with branch 0;
                      2 ↦ positive trit; 3 ↦ zero with branch 1.
decoding:              (neg) -> 0, (zero,0) -> 1,
                       (pos) -> 2, (zero,1) -> 3.
\`\`\`

New Agda source term names include
\`originalQuadToSignedZeroBranchThenBack\`,
\`originalSignedZeroBranchThenQuadThenBack\`,
\`originalFourSignedZeroBranchesRoundTrip\`,
\`originalSourceSiteFourSignedBranchesRoundTrip\`,
\`originalFourSignedBranchesProjectionIsSource\`,
\`originalMinimalSignedSourceRecoversAt\`,
\`originalMinimalSignedTargetRecoversAt\`.

For four original spatial-temporal torus site coordinates, signed positions with **r projected zero coordinates have 2^r original gauge-site lifts**. The exact original 256→81 projected-site stratification is:

| Number r of signed zero coordinates among first 4 | Number of projected vertices | Independent source sites per vertex | Original sites |
|---|---:|---:|---:|
| 0 | 16 | 1 | 16 |
| 1 | 32 | 2 | 64 |
| 2 | 24 | 4 | 96 |
| 3 | 8 | 8 | 64 |
| 4 | 1 | 16 | 16 |
| **Total** | **81** | depends on r | **256** |

The last five of nine signed coordinates are **chart padding**, not five extra physical Wilson directions. Retaining one original branch bit per source-zero is sufficient and minimal for reconstructing all 256 source gauge vertices, unlike retaining an opaque full original-site ID on every signed point.

**Actual no-go proofs:** \`originalSignedNineMidpointGaugeCannotDescend\` uses source C4 odd sites 1 and 3 and two independent Boolean gauge labels: their signed projection is both zero, so no single-valued midpoint gauge observer can reproduce both. \`originalSignedNineMidpointMetricCannotDescend\` uses the ACTUAL original periodic C4 shortest-path distance from site 1: \`d(1,1)=0, d(1,3)=2\`, whereas both project to signed zero. Thus W3 root/physical separation cannot be replaced by plain projected signed Hamming distance. These source-written Agda proofs have no compiler receipt.

## 3. Same-source full field and original noncommutative gauge law

New Agda terms in the SAME existing owner:

- \`originalSignedNineSourceCommutingAt\`, \`originalSignedNineTargetCommutingAt\`: pointwise original source and positive-step target for EVERY original bond.
- \`originalFullSignedNineGaugeFibreLift\`, \`originalFullSignedNineGaugeFibreRecover\`, \`originalFullSignedNineGaugeFibreRecoversEveryLink\`, \`originalFullSignedNineGaugeFibreRecoversEveryAddress\`: two-sided 1024-link indexing, no erased 896 spectator links.
- \`sourceLiftedSignedNineGaugeAction\` **calls original** \`YMClaySUNVariablePeriodicGibbsGaugeExact.periodicSUNGaugeTransform theory 3\` on the fully recovered original physical field. \`originalFullSignedNineRecoveredGaugeIsOriginalAt\` proves the exact original SU(N) gauge operation at EVERY recovered original positive bond. This is a geometric import of an existing original gauge theorem, not a new postulated SU(N) action.

Already source-written stronger physical owners remain authoritative: \`YMClaySUNConstructedPeriodicGaugeCodecExact\` for the original native 1024-bond gauge and normalized Haar expected invariance (under its Haar inputs); \`YMClayOriginalF19R445DecoderCommutingSquareExact\` for the entire original 1024 source field; \`YMClayOriginalR445NativeF19WeightedPhysicalSourceBIDIExact\` for the original **weighted** native/F19 coarse observable pushforward; \`YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact\` for original 1,F,G,FG *fine* source marks. Do not duplicate any of these, and do not collapse two noncommuting U0,V factors.

Exact group law retained on each of the original 64 coarse directed bonds:

\`\`\`
W = U0 V,       U0 = W V^-1,       V = U1.
(h_x U0 h_m^-1)(h_m V h_y^-1) = h_x W h_y^-1.
\`\`\`

Original fine gauge at m is independent for both source odd-site branches, not a fixed signed-midpoint gauge. After full source-faithful lift, **every one of the 1536 original Wilson plaquette words** is evaluated on precisely the same original labelled edges in the same order and thus no new group trace or action is introduced.

## 4. Full-field independent exact local acceptance (not continuous Haar)

New [full original Q8 check](../../scripts/check_ym_369_original_full1024_wilson_gauge_fibre_20261123.py), source-equivalent local file executed under Python 3, exact finite quaternion subgroup Q8 of SU(2):

- 256 sites, 1024 source positive links, 1536 original oriented plaquettes, 64 native coarse bonds, 128 duplicate-free selected fine bonds and 896 spectators: all PASS.
- 81 signed projected original sites, 256 zero-branch lifted, multiplicities 16/32/24/8/1 by r=0..4: PASS.
- 32 genuinely double-source midpoint projections, each with two distinguishable source gauge labels: PASS.
- All 1024 original bond value/gauge transformations, all 1536 oriented plaquette group words and gauge conjugations and normalized \`ReTr_SU2\`: PASS.
- All 64 original coarse path ordered \`W=U0V\`, \`WV^-1=U0\` and gauge midpoint cancellation, with **noncommuting** first and second SU2 subgroup links: PASS.
- Each \`Q8×Q8 → Q8×Q8\`, \`(U0,V)↦(U0V,V)\`, is a bijection; 64 disjoint pair factors +896 spectator factor labels thus preserve the **finite subgroup** product-uniform measure. NOT a proof of continuous compact SU(N) Haar/Fubini or CMP119 localized constrained T.

For the selected exact Q8 fine field the full source Wilson real-trace plaquette sum is -16 and unchanged by gauge/lift; this is a regression value, not a Wilson parameter estimate or continuum gap.

## 5. Actual source Singer G and the crucial indexed graph negative control

The RH worker's Griess/Sah native order-26 Singer matrix over F3 is

\`\`\`
G = [-1 -1  0]
    [ 0 -1 -1]
    [-1 -1 -1]  mod 3.
\`\`\`

Act on the original nine balanced trits in **three** independent 3-vectors, as RH #1533 does. For original YM source site x let signed address \`s(x)\` have first four signed C4 projections and last five zero. Let \`rho(x)\` be the **source** zero-branch bits. Then

\`\`\`
iota_k(x) = (k, G9^k s(x), rho(x))
recover x = decode_zero_branches(G9^-k position_k, rho(x)).
\`\`\`

The source gauge/adjacency at every k uses **transported original labelled edges**

\`\`\`
E_k = { (iota_k(x), iota_k(x+e_mu), mu, original_bond_label)
        : original side-four positive fine bonds (x,mu) }.
\`\`\`

This is a graph isomorphism **to the transported original graph E_k**, but NOT generally an embedding into the fixed P3^9 nearest-neighbour graph. The source-native gauge and Wilson products commute with this chart reindexing. Importantly, zeros occurring in a k-chart need not be original zero coordinates; source rho is transported, not recomputed from the current zero mask. This is identical in spirit to RH source position \`G^k\` and contragredient frequency \`G^{-kT}\`, without asserting a physical Yang–Mills wave frequency.

New [26-stage Singer-gauge-Wilson check](../../scripts/check_ym_369_singer_k_1024_gauge_wilson_20261123.py), using RH's exact G and the original full source Q8 fixture, source-equivalent locally executed:

- 26/26 k charts/inverse with **all 256** source zero-branch vertices reconstructed.
- **26×1024=26,624** original SU2 subgroup link and local gauge transformation equalities.
- **26×1536=39,936** original Wilson plaquette group words and gauged trace equalities.
- Fixed P3^9 nearest-neighbour edge survival among the **original 128 selected half-edges**, stages 0..25:
  \`(128,0,0,0,48,48,0,0,24,80,0,0,0,128,0,0,0,48,48,0,0,24,80,0,0,0)\`.
  In particular at k=1, **0/128** of these transported source edges is an edge of the FIXED P3^9 graph. At k=13, 128/128 happens to survive; this does not restore global invariance.
- Thus one must transport both \`E\` and the Wilson field, or accept a genuine geometric discrepancy. DO NOT silently read off YM physical path distance from the fixed k graph.

This is the **source-specific finite commuting-square repair** of a real broken square, not an assumption about evolving YM physical space. The RH same-time P3/C3 wave coincidence does not imply equality of SU(N) gauge path-ordered products, Wilson plaquette actions, or reconstructed Hamiltonians.

## 6. Correct revised exact YM minimum cut (no new generic infrastructure)

| ID | Exact downstream lemma / consumer | Strongest existing producer | Payment still required |
|---|---|---|---|
| **Y369.0** | \`originalFourSignedZeroBranchesRoundTrip\`, \`originalFullSignedNineRecoveredGaugeIsOriginalAt\`, \`originalSignedNineMidpointGaugeCannotDescend\`, \`originalSignedNineMidpointMetricCannotDescend\` | Newly attached to existing #1536 \`YMClayR445Base2ThreeAxis369FibreBIDIExact\`; full master gauge action imported | Source-written, Agda kernel/trust acceptance pending. Q8 1024/1536 and RH 128-local regressions pass |
| **Y369.1** | \`originalSingerKIndexedLiftedGaugeIncidenceSquare\` | RH #1533 G/k chart, #1291 H05 indexed cube, full #1536 original 1024 field, existing \`YMClayR445TimeKResidualHyperfabricExact\` | **Agda source-native k map on all 256 fibre-labelled sites + original E_k/Wilson plaquette transport**; now exact **finite Q8 test PASS**, not Agda-produced, and prove the nonidentity fixed-graph obstruction; avoid importing unmerged #1533 file into #1536 blindly |
| **Y369.2** | \`originalWilsonHaarAndMarkedF19SignedGaugeLiftNaturality\` | Original \`YMClaySUNConstructedPeriodicGaugeCodecExact\` and full original F19 marked weighted BIDI, plus current indexed source chart | Prove **measurable** full original continuous SU(N) product-Haar and \`1,F,G,FG\` Wilson functional pushforward through the **lifted** graph chart, preserving all 1536 plaquettes, 896 spectators and common partition; no independent 9D YM measure |
| **W0.G1–G2** | \`originalCMP109PrintedNonlinearAverageOnOriginalLift\`, \`originalCMP98SourceAverageF19MarkedPushforward\` | Existing CMP109 printed nonlinear Q, rooted gauge, CMP98 Path13/principal-log and original F19 arbitrary fine-function theorem | Source-specific original 1024-link nonlinear Q formula, **L=13 vs L=2 scale compatibility**, charts/gauge/endpoint and correct D=Q_B W^-1, not Q_B=W |
| **W0.G3–G5** | \`originalCMP119OrderedHistoryMarkedTEqualsWilsonLiftedPushforward\` | Existing CMP119 Omega/Lambda/S factorization, CMP122 Eq171/Gate4, E/R/B/V Round214, same-flow CMP116 | Actual original beta(a) source, nontrivial domains and original source-specific gauge/FP/Jacobian/R T constraints with **S inside T**, one normalized 1/F/G/FG history equality; don't identify one local T with global F19 |
| **W0.G6** | \`originalWilsonW3RootedPhysicalMetricAndAbsoluteCharge\` | Existing R576/R574/R494 CMP116 marked WEXT receiver, native geometric W3 roots, first R445 small-beta marked bounds | Retain ORIGINAL graph distance and physical SI time, **not signed-nine observed Hamming**; prove real selected Wilson cluster-log and absolute rooted shell uniform in volume and cutoff along beta(a), with genuine large-field rates |
| **W0.G7** | \`originalWilsonContinuumNoncollapsedSameHOSGap\` | Existing finite original OS and same-H spectral compilers | Nontrivial continuum E1/RP/OS same-source measure and strictly positive physical nonvacuum H gap; RH stroboscopic B operator is not a YM spectral gap producer |

**Min-cut sequence:** accept Y369.0 kernel/trust; reuse the RH Singer exact chart to prove Y369.1 on original sources; attach Y369.2 by explicit original coordinate reindex/measurable Haar; consume existing CMP109/119/122 on the same lifted ORIGINAL source without duplicates; then physical absolute W3/source distance and same-H continuum. Geometry/reindexing cannot pay the latter analytic estimates by itself.

Verification: GitHub Agda/file write + readback requested; original Q8 source-equivalent local Python tests PASS; committed scripts separately read back, not independently exact-byte replayed; Agda compiler/CI not run. Source attribution Wilson/Haar, Bałaban CMP98/109/116/119/122, RH #1533 Singer, H05 #1291, original DASHI R445/F19/gauge owners; external physical mass-gap status OPEN.
