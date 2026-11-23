# YM P0 / W3 — exact ORIGINAL 4D SU(N) two-time Wilson connected-surface coefficient

23 November 2026. **Source-first new finite Wilson calculation, not a Clay continuum mass gap.** Full original periodic side-four 256 sites, 1024 positive SU(N) links, 1536 six-positive-plane plaquettes. Original F19/W1 normalized globally marked two-plaquette source, true independent one-link continuous Haar. No replacement of the physical SU(N) field by a Z2 subgroup, auxiliary nine-state wave, spin toy or CMP116 printed J. Source geometrical checker: [scripts/check_ym_original_sun_w3_two_time_tube_20261123.py](../../scripts/check_ym_original_sun_w3_two_time_tube_20261123.py). Local source-EQUIVALENT extended 4D Python/SymPy 1.14 checks PASS. GitHub Agda kernel/CI not run. SU(N) fundamental matrix-entry Haar orthogonality is a standard imported mathematical theorem, not a new Agda one-link authority.

## 0. Precedence — important prior art recovered rather than duplicated

Earlier original source SU2 all-degree Haar/moment algorithm exists in \`scripts/check_ym_original_wilson_polynomial_cylinder_20261117.py\`; \`YMClayOriginalWilsonDyadicCauchyMaxCut20261117.md\` and \`YMClayOriginalWilsonGaugeCubicMaxCut20261117.md\` previously computed original 6L^4 plaquette polynomial Taylor moments through third order and gauge identities, not this original TWO MARK / time-2 connected eighth multilinear coefficient. Original continuous SU(N) Wilson 4D action, F19 64 native W plus 896 spectators, globally affine 1,F,G,FG coefficients and R445 time/cylinder are already present. The actual CMP119(2.18)/(2.19)/(2.20), CMP122 Eq1.71 constrained T source, CMP116 original differentiated Wilson absolute-tail **COMPILERS** and R556→R551→R552 same-H OS gap are also present. This finite source formula does not replace those, and avoids inventing a new polymer source, Haar authority or Hamiltonian.

## 1. The exact same original 4D source and physical Euclidean separation

Use original periodic \((\mathbb Z/4\mathbb Z)^4\), coordinates \((x_0,x_1,x_2,x_3)\), original time \(x_0\), and original positive \((\mu,\nu)\) six-plane plaquette \(p=(x,\mu,\nu)\). Its word in ORIGINAL positive-link SU(N) variables is
\[
P_p=U_\mu(x)\,U_\nu(x+e_\mu)\,U_\mu(x+e_\nu)^{-1}\,U_\nu(x)^{-1},
\quad t_p=\frac1N\mathrm{ReTr}(P_p).
\]
Choose original Wilson closed marks
\[
F=t_{p_F},\quad p_F=((0,0,0,0),1,2);
\quad G=t_{p_G},\quad p_G=((2,0,0,0),1,2).
\]
They are the ORIGINAL Wilson gauge-invariant \(F,G\) observable insertions on two time slices separated by TWO native Euclidean steps; not new fields or original Hilbert-time evolution.

Choose a physically connected eight-plaquette side wall \(T\) of a \(1\times1\times2\) Euclidean-time prism. For each \(x_0=t\in\{0,1\}\), the **actual 4D source coordinates** \((x_0,x_1,x_2,x_3;\mu,\nu)\) of the four side plaquettes are \((t,0,0,0;0,1)\), \((t,0,1,0;0,1)\), \((t,0,0,0;0,2)\), \((t,1,0,0;0,2)\). These are exact native \`PeriodicPlaquette\` identifiers under the chosen six-positive-plane orientation, not a fixed 9-sheet graph. Source count: two marked end caps F,G plus eight original distinct side plaquettes, exactly TEN original faces and TWENTY links, twelve vertices, \(\chi=12-20+10=2\).

All other 1528 original Wilson interaction plaquette couplings may be set to zero when computing the **selected mixed derivative AT the original all-zero-coupling point**. This is a tagged/multivariate derivative of the same canonical original \(\exp[-\sum_p\beta_p(1-t_p)]\), not an alternative physical 4D action. In the actual homogeneous Wilson theory all couplings share one bare \(\beta\); the selected multilinear coefficient is one SOURCE component of its formal expansion, and is not by itself the full homogeneous coefficient.

## 2. Eight is SHARP for the stated square-free mark-excluding original surface problem

In the *actual full 1536-plaquette L4 source*, every distinct original positive plaquette other than F or G shares AT MOST ONE positive link with F and at most one with G. No nonmarked original plaquette shares a link with BOTH marks (their native time slices are t0 and t2). To compensate \(\partial (F+G)\) modulo 2 using a set of distinct nonmarked interaction plaquettes, each of the FOUR original boundary links of F and each of the FOUR original boundary links of G requires its OWN distinct interaction plaquette. This proves a mathematical lower bound **8** without an optimization oracle. The eight explicitly given original +time side plaquettes attain it:
\[
\partial_2\left(p_F+p_G+\sum_{q\in T}q\right)=0\quad\text{in }\mathbb F_2^{1024}.
\]
Local exact full-4D code checks 1536 source plaquette supports and all 256 subsets of T. Every proper subset of T leaves some original link singly occupied in the source F/G joint product; neither F nor G alone can be made Haar-neutral using ANY subset of T. The same source was independently checked by a full 4D 1536-variable/1024-parity-constraint integer optimization (HiGHS optimal eight), but the 8-point hand/counting argument, not the MILP floating solver, is the actual proof. IMPORTANT: this is a sharp **square-free, end-mark-excluding 2-chain** result. It does NOT exclude repeated-plaquette or marked-cap insertions in an unrestricted common-beta expansion from lower total orders; do not label eight the first nonzero general Wilson covariance order.

## 3. Exact Haar character contraction: one nonzero ORIGINAL connected response component

On the full ORIGINAL independent SU(N) product Haar source, use the SAME original Wilson normalized two-mark source
\[
Z_N(s,t;\boldsymbol\lambda)=
\int_{SU(N)^{1024}}\exp\left(sF+tG+\sum_{q\in T}\lambda_qt_q\right)\,dH^{1024};
\quad
C_N(\boldsymbol\lambda)=
\left.\partial_s\partial_t\log Z_N(s,t;\boldsymbol\lambda)\right|_{s=t=0}.
\]
The physical source Wilson action is \(\exp[-\sum\lambda_q(1-t_q)]\); its extra \(\exp(-\sum\lambda_q)\) factor cancels in normalized connected responses. All 1024 physical links exist and are integrated, including 896 original F19 spectators under the same full Haar measure; irrelevant spectator integrals here equal 1 at the zero-coupling expansion point, not an independent spectator ansatz at finite beta. No nontrivial finite-Haar covariance is silently assumed.

For every proper \(S\subsetneq T\), independently integrating just a singly occupied ORIGINAL Haar link gives
\(\int F G\prod_{q\in S}t_q\,dH=0\).
The same original support argument gives all \(\int F\prod_{q\in S}t_q=0\) and \(\int G\prod_{q\in S}t_q=0\) when S is any of the 256 subsets. Hence neither the normalized denominator nor the disconnected \(\mathbb E F\,\mathbb E G\) can contribute to this selected eight-fold mixed coefficient:
\[
\boxed{
\left.\left(\prod_{q\in T}\partial_{\lambda_q}\right)
  C_N(\boldsymbol\lambda)\right|_{\boldsymbol\lambda=0}
=\int F G\prod_{q\in T}t_q\,dH^{1024}.}
\]
This is a source exact CONNECTED, genuinely time-separated normalized Wilson observable coefficient, not a source-free polymer envelope or a complete W3 absolute tail.

Each of the twenty original positive links appears EXACTLY TWICE in the closed oriented prism boundary. Choose the coherent orientation of all ten faces. At each link the true SU(N) Haar identity
\[
\int_{SU(N)}U_{ab}(U^{-1})_{cd}\,dH(U)
=\delta_{ad}\delta_{bc}/N
\]
contracts the native matrix index strands. There are 12 remaining index loops (actual prism vertices), 20 Haar factors \(1/N\), and 10 original \(1/N\) normalized traces. Hence the coherently oriented product is \(N^{12-20-10}=N^{-18}\).

For \(N\ge3\), each \(\mathrm{ReTr}\) contributes a HALF SUM of the two orientations, and the SU(N) centre kills every inconsistent orientation assignment at a twice-occupied link. There are exactly TWO globally coherent orientation choices among \(2^{10}\) terms. For \(N=2\), the fundamental trace is real (pseudoreal fundamental representation), so no independent factor-of-2 orientation average is imposed. Thus
\[
\boxed{
C_N^{[8]}=
\begin{cases}
2^{-18}=1/262144,&N=2,\\
2^{-9}N^{-18},&N\ge3.
\end{cases}}
\]
Direct selected exact values: SU3 \(1/198359290368\), SU4 \(1/35184372088832\), SU5 \(1/1953125000000000\); the checker separately verifies N=2,3,4,5,6. These fractions come from the genuine full compact SU(N) Haar contraction, not a finite subgroup sum, 24-cell cubature or a putative physical OS mass.

**Why this is relevant to W3:** The original F,G product source has a witnessed, genuinely connecting, nonzero and gauge-invariant marked contribution whose signed value and absolute magnitude agree because it is positive. The remaining W3 requires the uniform ABSOLUTE SUM of ALL original differentiated connected activities after the true CMP119/122 RG including source-dependent large fields, FP, coupling beta(a), entropy and physical support metric. One selected positive coefficient DOES NOT upper-bound that sum and its existence does not prove gap.

## 4. Same original-time selected prism family and honest scaling

For the \(+x_0\) oriented non-wrapping \(1\times1\times d\) prism with \(4d\) side interactions and two marked caps, exact combinatorics give
\[
(V,E,F)=(4(d+1),\,8d+4,\,4d+2),\quad\chi=2,
\]
and a selected \((4d)\)-fold **multivariate** interaction coefficient
\[
C_{2,d}=2^{-(8d+2)},\qquad
C_{N,d}=2^{-(4d+1)}N^{-(8d+2)}\ (N\ge3).
\]
Actual original L4 source checks d=1,2,3 (wall length 4,8,12), for SU2/SU3/SU4 and exact source parity. For d=3, the *periodic reverse-time* path has d=1, so the +time cylinder is a VALID contribution but NOT the shortest physical separation path. At any physical spacing a, d and Euclidean time \(d a\) are separate. A selected monomial amplitude \(\beta^{4d}C_{N,d}\) is a bare-coupling formal Taylor component, NOT a pointwise physical Wilson covariance bound; it cannot justify a cutoff-uniform physical mass \(m\) under \(\beta(a)\to\infty\). In particular, forcing a fictitious transfer ratio from this one term would violate the existing native R551/R552 same-H source semantics.

## 5. Exact source boundary / next maximum cut

**COMPLETED**: original full 4D source cylinder combinatorics, sharp end-mark-excluding 8-face minimum (without MILP reliance), all 256 subsets and zero lower proper moments, true Haar-index contraction and explicit strictly positive eighth mixed two-mark Wilson coefficient in every SU(N≥2), selected d=1..3 family.

**NOT COMPLETED**: the original literal absolute two-Wilson CMP116 differentiated pointwise bound \`BalabanLiteralTwoWilsonCMP116ConnectingTailExact.twoWilsonPointwiseCMP116ChargeLevel=conditional\`, its connecting shell charge sum \`twoWilsonChargeSumBelowRootedTailLevel=conditional\`, original physical normalized source across actual CMP119/122 complete localized T and FP with beta(a), original interacting continuum OS Schwinger family and same reconstructed H. These remain explicit source inputs, not a new missing formalism. Neither RH zero winding, finite unmarked SU(N) transfer candidates nor an eight-wall tube is the accepted physical uniform gap.

**BIDI next:** use the existing \`BalabanLiteralWilsonMarkedLocalizationSourceExact\` to identify whether *actual* CMP119/122 differentiated E/R/B/V cluster charges reduce to this source-selected primitive at the bare step, **with original factorized T domain histories and all spectator/link constraints retained**. Then prove a physical beta(a) pointwise absolute upper bound and SUM over all other irreducible original connected charge families, including frustrated/large-field sectors. The appropriate original already-produced SU2 coherent/frustrated packing source is \`YMClayOriginalWilsonCoherentConnectedPolymerPacking20261109.md\`, whose own negative control correctly says extensive frustration suppression does NOT pay sparse connected paths. The older \`check_ym_original_wilson_polynomial_cylinder_20261117.py\` can serve as an independent low-degree polynomial-Haar basis; do not duplicate it.

Attribution: Wilson 4D lattice action, standard SU(N) Haar/Schur/Peter–Weyl, Bałaban CMP109/116/119/122, OS, original DASHI native Wilson/Haar/F19 and exact source incidence, and ordinary high-temperature linked-surface character expansion. No Agda/Lean kernel, GitHub CI or Clay completion is asserted.


## 6. Six genuine original Wilson space/time route witnesses — not H05 six-face identity

A further exact L4 source regression, appended to the committed checker, enumerates ALL THREE native spatial transverse two-planes \((1,2),(1,3),(2,3)\) and BOTH shortest independent periodic-time routes between the time slices \(x_0=0\) and \(x_0=2\): forward time edges \(0\to1\to2\) and reverse periodic time edges \(2\to3\to0\). This yields **3×2=6 different true original L4 Wilson ten-face spheres**, each with 8 side plaquettes, 20 positive-link supports counted twice and a mod-2 closed boundary. For each fixed transverse plane, the two 8-side plaquette sets are disjoint. The original spatial C3 plane permutation acts on the THREE plane *types*, while periodic Euclidean time reflection exchanges the TWO time *path types*; the physical 4D plaquette support/id transport is verified directly by native incidence rather than assumed from chart count. Full original geometry local PASS.

The six actual Wilson route labels are **NOT** the six faces of H05's indexed \(3^3\) cube, not six physical polarizations, and do not identify a new C2/C3 or Singer \(k\) physical action on the original OS Hilbert space. They simply give an exact concrete positive source-connected witness in each of the six selected spatial-plane/time-path channels; the per-route Haar coefficient is the same \(C_N^{[8]}\) by the original Wilson lattice symmetry. For a fixed source mark pair there are TWO true shortest time tubes, not six, and this neither proves interference/cancellation absent among the remaining clusters nor the desired strict physical spectral estimate.

Preserve separate \(t\)=original Euclidean lattice coordinate, \(k\)=Singer/TOE reversible address, RG scale/cutoff and RH horizontal coordinate. No Agda/Lean/CI or all-cluster W3 promotion.
