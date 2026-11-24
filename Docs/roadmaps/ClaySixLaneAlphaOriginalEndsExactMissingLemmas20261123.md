# Active Clay rollup — 24 November 2026

**This is the controlling portfolio roadmap on the new master-based rollup.** P0: RH, BSD, NS, Hodge. P vs NP is donor-only; YM remains independent; Poincare is established. Retain zero mode, signed residual and indexed hyperfabric, including source/time/scale/ramification indices; geometry-forward, endpoint-first, bidirectional and reverse-solved. Historical priority labels and original-source PR links below remain provenance, not competing portfolio instructions.

## Source reconciliation and ownership

- Base master `350e2c6a20fbf445f489a2c7354836cb6f153ad6`; its one commit since the #1543 merge base changes nine disjoint YM paths. Recover all 34 #1543 paths from `fd0cc32cfccd016259c8b7181a43e5073cd5dba2` and all 27 actual master-comparison #1533 paths from `07e71d1e168e408fe2797cc0158ae21684095a62`, not the 122 historical PR paths. RH additions absent on master (23); four modified RH blobs match their merge-base versions. Preserve source blobs/modes except this explicit coordinator preface. No old branch merge or force push. #1543/#1533 stay open as provenance; direct subsequent portfolio work to this rollup, not parallel conflicting edits.
- #1444 `3f9c3c9eb3507c2a6ad34afa6f6bf2a4bd231add`: 24 ahead / 97,958 behind master. Its finite Euclidean Hodge-star basis module is already byte-identical on master (a94ed928aa5fdd297db76d2cae63e7f102437ca7); this is a donor, not Hodge conjecture closure. CMP102 factorial-pair and finite-row-aggregate modules absent on master; preserve under independent YM #1444/#1536/#1544. Do not import divergent YM history.
- Latest donor metadata at this audit: Langlands #1549 `0208b560be2af193f7d6c68f20e79cf70adc2c30`; PNP #1548 `f10fa7a0852e193e318ed49e906733a8d2e6a89d`; pi #1546 `59276f8e27457374da0755a33d5f3f4fddeee2cf`. Older detailed donor deductions below are pinned to their inspected source heads; this rollup does not claim new theorem-body audit of these latest heads. Keep independent donors separate and consume verified same-object results, not unrelated source replacements.

## Next large mathematical cuts

| P0 | Existing source / consumer | Exact next proof obligation |
| --- | --- | --- |
| RH | Original Weil/xi and Mellin, recovered #1533 prime aperture/zero-annulus source; original Clay RH BIDI | Genuine all-admissible-test strict compensation with multiplicities, signs and scale/far/pole residual; independent external proof admission remains conditional. |
| BSD | Existing Kummer/Selmer/Sha and E32 Fricke/Mellin, actual all-curves rank consumer | Arbitrary E/Q, all ranks: analytic order equals torsion/Sha-corrected Kummer rank, retaining ell^n transitions and bad-place fibres. Selected cases are not universal. |
| NS | R225/R388/R596/R568/R653, N2b/c/d, R682/R683 | Uniform first dyadic shell moment for original unweighted positive budget; independently strict R653 surplus, actual trajectory and continuum. Weighted bound does not imply original endpoint. |
| Hodge | Original rational cohomology and cycle map, Gr(2,4), primitive Lefschetz polarization | Produce actual cycles for unresolved rational orthogonal residual on arbitrary smooth projective X, all p. Finite Hodge-star/Schubert cases do not imply general H3. |

Acceptance: inherited local receipts retain their original scope; no new SymPy, CI, kernel, external authority acceptance or original Clay endpoint claimed by this transplant. Phases, deliverables and original exact consumers follow below. Historical 0/6 internal endpoint count unchanged.

---

# Clay six-lane alpha — original endpoints, BIDI and exact remaining lemmas (23 November 2026)


## 24 November 2026 — endpoint-first six-Clay steelman, forward/BIDI reverse solve and R568 positive trace necessity

**Current programme priority (user correction, 24 November 2026): P0 = RH, BSD, 3D NS, Hodge. P vs NP and YM are excluded from this coordinator's P0; Poincare is already an established theorem.** P vs NP remains an independent mathematical donor (#1548/Lean #119, #1549/Lean #120), YM its separate source track (#1536/#1544/#1444). Historical P0 labels below and in donor branch names are local/historical, not current portfolio priority. Preserve all six endpoint quantifiers and source owners; original DASHI prize endpoints remain 0/6. Geometry-forward, bidirectional/reverse-solving, original source and zero/signed residual retained, with explicit time/scale/precision indices where relevant. Endpoint mathematics before certification.

### E0. Six literal endpoints: reverse from the desired theorem, then forward from existing source

| Original Clay endpoint (actual quantifier) | Reverse-solved minimum mathematical producer, no source/CI substitution | Already existing original owners and downstream consumers; active PRs | Missing first genuinely new lemma |
| --- | --- | --- | --- |
| **P vs NP — separate donor:** universal standard deterministic polynomial SAT decision failure, SAT in NP | For each fixed standard SAT decider D and each polynomial clock, a valid length/input that defeats correctness or the clock. A single polynomially costed semantics-preserving normalization suffices to transfer a universal target lower bound, but a finite witness family/restricted model does not | Agda PNotEqualsNPClayCoreExact.SATLowerBoundProducer, PNotEqualsNPDirectSATLowerBoundExact.universalDecisionFailureClosesPNotEqualsNP, fixed-standard CodedStandardHalting* and ObserverCoverage owners; #1548, Lean #118/#119/#120, #1006, #1040, #1129, FRACTRAN/MDL #123 | N1–N3 true standard-machine charged coverage; IN PARALLEL U2 necessity on every actual computation, U3 bounded sharing/overlap charges, U4/A2 superpolynomial universal lower bound; then N5–N6 actual consumer |
| **3D NS — P0:** one ORIGINAL Fefferman A/B global smoothness route or independently valid forced C/D breakdown, in exact data/forcing class | On periodic unforced B, true cutoff-independent a priori criterion sufficient for global smooth solutions for all smooth data; original R568 C1 upper **AND** original R653 C2 strict-surplus lower, then R503/R504 and continuum. C/D external source cannot be borrowed as a B proof | Original R240/R405, R225/R388/R440/R541/R560/R565/R568/R596/R652/R653, R681/R682/R683, R686, conditional R571; #1543; TOE NS #1384, prior merged NS #1501, historical #957 closed; original A kernel/Gram and external C/D adapters separate | **The positive terminal Gram + mixed-helicity L2 spacetime trace budget below**; independent R653 strict surplus on SAME trajectory; native physical time/field/FTC and 3D limit |
| **YM mass gap:** for every compact simple group, a nontrivial 4D quantum YM theory satisfying appropriate axioms, with a positive gap in its *reconstructed* Hilbert-space Hamiltonian | Same original interacting 4D Wilson/Haar family -> original scale-uniform source and marked cluster control -> OS-positive noncollapsed continuum -> one invariant same-H reconstruction -> inf positive spectrum >0 | Canonical ClayYMProofRoadmap; original CMP119/122/116 R445/R320/R333, W3 and OS consumers; #1536, #1544; original donor #1444 | Original COMPLETE physical W3 renormalized absolute rooted source including all interactions, FP/Jacobian/large fields; then uniform continuum and genuine same-H gap N1/G1; a bare Haar jet is not a spectral theorem |
| **RH — P0:** every nontrivial actual zeta zero has real part 1/2 (GRH all-character theorem strictly stronger) | Either independent actual xi/Weil selected signed all-zero obstruction with valid far/pole tails and strict cofinal margin, or independently checked published all-characters proof transported to the literal Clay zeta statement | Existing Weil source W/G2, original completed zeta, MellinSplitFunctionalEquationExact, AlpogeRHOriginalClayEndpointBidiExact; Agda #1533; Lean #113 merged, upstream pinned separate | Genuine universal original-zero strict signed compensation, OR original full external kernel/axiom and semantics receipt; selected numerical zero checks and per-character interface alone do not settle it |
| **BSD — P0:** for every E/Q, ord at s=1 of actual L(E,s) equals rank E(Q); full leading coefficient is a stronger *refined* target | Same E-indexed modular L, arithmetic Mordell–Weil data, then arbitrary rank (including >=2), CM/non-CM, and proof of rank equality on ALL curves; refined universal Sha/period/regulator/Tamagawa separate | BSDUniversalScopeFirewallExact, BirchSwinnertonDyerBoundary, original E32 level-32 Fricke/Mellin and 2-isogeny/Sha owners; merged #1499; Lean #108 merged | S6 all-curves all-ranks analytic/algebraic rank equality, not selected E32 classical Rubin/Tate S5 |
| **Hodge — P0:** for every smooth projective complex X and every p, every actual rational (p,p) cohomology class is a Q-linear combination of actual algebraic cycle classes | Actual comparison H^(2p)(X,Q) ↪ de Rham/Hodge, literal Chow cycle-class map, and surjectivity onto rational (p,p) for ALL X/p, not just cellular X | HodgeLiteralCycleClassMapBridgeExact, HodgeProjectiveKnownCycleResidualBridgeExact, ProjectiveLineGenericCycleClassWeldExact and original classical Gr(2,4) Schubert inverse; merged #1499, Lean #108 | Universal H3 algebraic cycle spanning theorem on noncellular general X and all codimensions; selected P1/Gr(2,4) is classical not universal H3 |

**Cross-lane phase rule** (do not turn into additional per-PR scaffolding): P0 freeze literal endpoint/quantifier/metric and reuse; P1 construct exact same-original-source carrier and *both* forward and inverse/recovery geometry; P2 attack the shortest true mathematical signed/uniform/all-instance producer, testing both a steelman and an adversarial obstruction; P3 close universal quantifier and continuum/standard-machine/infinite-volume limit; P4 connect into the ALREADY EXISTING terminal consumer; P5 native Agda/Lean kernel, non-admitted axioms, attribution and independent review only after the mathematical theorem. P5 is never a substitute for P2/P3. The specialist active PR owns its lane; coordinator #1543 records dependencies without replacing #1548/#119, #1536/#1544 or #1533.


### 24 November — geometry-forward P0 donor crosswalk and next endpoint cuts

Read current branch files, rather than relying on PR descriptions:
- [P vs NP #1548 G65–G69](https://github.com/chboishabba/dashi_agda/blob/research/clay-p0-polynomial-coverage-endpoint-20261124/Docs/roadmaps/ClayP0PolynomialCoverageEndpoint20261124.md), inspected blob 89d6606ba60c7e5626218d4b48f3f21455362374: signed cover and chronological separator contraction, neutral pin evaluation quotient with kernel rank 3^w−2^w, source graph minor/treewidth transport. Width and quotient dimension are not unavoidable complexity. Retain source labels even when a consumer factors through a quotient.
- [Ramified Langlands/GCT #1549 R92–R98](https://github.com/chboishabba/dashi_agda/blob/research/clay-p0-ramified-langlands-gct-20261124/Docs/roadmaps/ClayP0RamifiedLanglandsGCT20261124.md), inspected blob 9eac2e92de0d22baf34ee9a46c6512bf66fafee8: genuine simultaneous precision collisions at a fixed observer, Hermite recovery budgets and canonical-lift carry defects, indexed creation precision. Coarse profiles can lose same-object information. A recovery obstruction for a fixed interface is not an unrestricted lower bound or an arithmetic/geometric endpoint.
- [Pi #1546 COMP5m/n/o](https://github.com/chboishabba/dashi_agda/blob/research/pi-p0-consolidated-gmp-master-20261123/Docs/roadmaps/Paper9PiP0ProjectiveResidualCone20261124.md), inspected blob 3e0ebe418e9422a481c0c838d920683393ce619c: output-aligned enclosure, source-ordered noncommutative product, exact signed-square verifier separating candidate producer from consumer. These are untested prototypes conditional on actual Chudnovsky/tail premises, not certified speedups.
- [Monster #1545](https://github.com/chboishabba/dashi_agda/pull/1545): same-object Hom action and phase-swapping central projectors; actual complex operators/source attachment still open. Useful distinction between multiplicity dimensions and actual maps, not a premise of Clay.

| P0 lane | Forward geometry and reverse endpoint | First mathematical deliverable / negative control |
| --- | --- | --- |
| RH (#1533, original Mellin/Weil G2) | Actual xi/Weil transform; retain zero multiplicity, conjugate/functional reflection, pole/far tail and test-family index; reverse from strict exclusion of off-line zeros or genuine equivalent positivity on the complete admissible family | Construct uniform signed compensation or complete actual external theorem transport; finite test-observer agreement does not exclude a hidden zero or prove RH. |
| BSD (merged #1499, original Kummer/MW/Sha and Fricke/Mellin owners) | Same E-indexed all-place localization, local Kummer fibres including bad primes, actual Selmer and Sha kernels, analytic order of the actual L-function | Reverse from all-ranks rank equality; for every prime ell the classical exact Kummer sequence gives rank E(Q)=dim Sel^ell−dim Sha[ell]−dim E(Q)[ell]. Need an actual comparison to analytic order for arbitrary E, not equality of local dimensions or selected rank-zero evidence. Refined leading coefficient remains separate. |
| NS (#1543, R225/R388/R596/R568/R653, R682/R683) | Positive terminal Gram and time-integrated mixed-helicity trace on the original cutoff/trajectory, retaining within-rate radical and signed surplus | Uniform trace and terminal Gram upper plus independent strict C2 surplus. Heat-fibre estimate below gives an energy-controlled time-average, not a terminal or H trace bound. |
| Hodge (merged #1499, literal cycle class and Schubert inverse owners) | For actual rational Hodge classes, use a rational Hodge-Riemann polarization via primitive Lefschetz decomposition to form Gram projection onto a finite span of actual cycle classes, retain orthogonal residual in the same cohomology group | Prove that residual can always be represented by actual algebraic cycles or is zero when the span is the full algebraic image. Positivity of the Gram matrix does not imply residual vanishing; noncellular arbitrary X/p remains H3. |

#### NS candidate mathematical payment N2b — heat-fibre integrated Gram control (classical, not kernel)

In the mean-zero, normalized periodic physical setting of N0, let v_s^±=exp(nu*s*Delta)u_C^±(t), with auxiliary heat parameter s independent of physical t. Source rates and ordered convolution give the exact identity
\[
Q_C(t)=32\int_0^\infty \|P_C^{\ne0}(v_s^+\times v_s^-)\|_2^2\,ds.
\]
Indeed each weighted mixed-cell sum is four times the projected heat-smoothed cross product; the original Gram factor is two. The orthogonal helicity and output projections commute with heat. Holder and the mean-zero 3D Gagliardo–Nirenberg inequality yield
\[
\|P_C^{\ne0}(v_s^+\times v_s^-)\|_2^2
\le C_{GN}\|v_s\|_2\|\nabla v_s\|_2^3.
\]
Heat contraction bounds the first factor by ||u_C(t)||_2 and one gradient factor by ||grad u_C(t)||_2. The exact heat energy identity gives integral_s ||grad v_s||_2^2 = ||u_C(t)||_2^2/(2 nu). Thus
\[
0\le Q_C(t)\le (16C_{GN}/\nu)\|u_C(t)\|_2^3\|\nabla u_C(t)\|_2.
\]
For the actual unforced Galerkin energy equality, ||u_C(t)||_2<=||u_0||_2 and integral_t ||grad u_C||_2^2<=||u_0||_2^2/(2 nu). Consequently
\[
\int_0^T Q_C(t)^2\,dt\le (128 C_{GN}^2/\nu^3)\|u_0\|_2^8.
\]
Here C_GN denotes an admissible constant for the displayed product inequality (independent of C,t,s). This is a classical estimate on the original Gram, not an asserted new general NS theorem. It uses standard Sobolev/heat/energy facts. Gives an L^2 time bound uniform in C,T and controls the measure of large Q_C times; it does NOT control Q_C(T) at arbitrary T, integrated H_C, C1 upper, C2 strict surplus or continuation. Narrow spikes remain possible under an L^2-time budget. Next reverse cut: use original R388/R682/R683 dynamics to control temporal concentration and the separate mixed-helicity trace, rather than infer a pointwise bound from the average. No new local execution, native kernel or CI in this audit.



### 24 November — N2c critical negative-order output budget; retained zero mode, signed residual, indexed hyperfabric

User priority: RH/BSD/NS/Hodge P0, PNP donor only, YM separate. Keep the original source tuple (C,k,p,q,helicity,physical t,auxiliary heat s) and rate-radical sidecar. The zero mode is retained separately, not erased by a negative-order multiplier: selected periodic B uses mean-zero velocity, and k=0 is explicitly outside the original R568 observer. In other data classes mean/transport must be attached separately.

**Current donor reread at pinned heads:** Langlands #1549 73bf0b2a23a3 (roadmap blob e978a6e333cb9b6125bfe23800a58e97b641e4fb), R99–R106 signed dual-rail moment defect, actual Smith zero/signed spectrum, wrong-chart commutator and six-face transport; #1548 7dcee418032a (blob 89d6606ba60c7e5626218d4b48f3f21455362374), G65–69 signed separator evaluation and neutral kernel; pi #1546 5c3165ce1b2f (blob 84af6bcce1c903a3131d58a41005e204b624ea9d), G8 and COMP5p/q/r indexed positive source scales, exact fixed-prime content, homogeneous observer vs raw reopening, untested prototypes. RH #1533 07e71d1e168e retains independent external proof admission boundary. No donor endpoint is assumed; no new theorem source copied.

**N2c (classical mathematical deduction on original physical finite Galerkin family):** use normalized 2pi torus, mean-zero, nu>0; define Lambda=(-Delta)^(1/2) on nonzero outputs. Set Q_-1=sum_{k!=0}|k|^(-1) Q_k, H_-1 and signed F_-1 analogously, using the exact R596 factor two and R225 mixed-cell factor four. The original per-output differential identity 4 F_k=Q'_k+2 H_k gives exactly 4 int F_-1=Q_-1(T)-Q_-1(0)+2 int H_-1. No pointwise sign or unweighted equality is asserted.

For mean-zero w with orthogonal helicities, dual Sobolev H^(1/2)->L^3 and Sobolev H^1->L^6 imply
||Lambda^(-1/2) P_C^{!=0}(w^+ cross w^-)||_2^2 <= K ||w||_2^2 ||grad w||_2^2.
Indeed test against mean-zero H^(1/2), use L^(3/2) product and Holder L^2 x L^6; orthogonal Fourier projections contract both norms. K is independent of C. Use v_s=e^(nu*s*Delta)u_C(T), with auxiliary s independent of physical time t. R596 Laplace representation gives Q_-1(T)=32 int_s ||Lambda^(-1/2) P_C^{!=0}(v_s^+ cross v_s^-)||_2^2 ds. Heat energy identity gives integral_s ||grad v_s||_2^2=||u_C(T)||_2^2/(2nu). Thus Q_-1(T)<=16 K ||u_C(T)||_2^4/nu. Similarly H_-1(t)=16||Lambda^(-1/2)P_C^{!=0}(u_C^+ cross u_C^-)||_2^2, and physical energy equality gives 2 int_t H_-1 <=16 K ||u0||_2^4/nu. Both together give a uniform weighted positive endpoint budget <=32 K ||u0||_2^4/nu, hence the weighted signed upper and lower. Stronger: writing E(t)=||u_C(t)||_2^2, E'=-2nu||grad u_C||_2^2, integration of E*||grad u_C||_2^2 gives (E(0)^2-E(T)^2)/(4nu); the same refinement in auxiliary heat yields Q_-1(T)<=8 K E(T)^2/nu and 2 int H_-1<=8 K (E(0)^2-E(T)^2)/nu. Combined **8 K E(0)^2/nu**, uniformly C,T. No numerical or kernel proof claimed.

**Exact reverse cut:** define nonnegative indexed measure b_C,T(k)=Q_k(T)+2 int H_k. For dyadic shells A_j={2^j<=|k|<2^(j+1)}, let a_j=sum_{k in A_j} b(k)/|k|. Then sum a_j<=8K E(0)^2/nu, and 2^j a_j <= sum_{A_j} b(k) <=2^(j+1) a_j. Original C1, given smooth bounded initial Q, is equivalent to uniform sum_j 2^j a_j<infty (uniform finite bound, not merely pointwise convergence). A uniform tail estimate a_j<=A 2^(-(1+epsilon)j) suffices, but is stronger than needed. The abstract positive packet b(2^j e1)=2^j shows weighted bound alone cannot recover unweighted bound; this is an observer-level countercontrol, NOT an NSE state or trajectory. Original within-rate radical and signed forcing residual kept; no promotion to C1 or C2. Next real mathematical cut: R682/R683 signed dynamics must supply summable output-shell compensation or a different genuine all-data continuation criterion. R653 strict surplus remains independent.

**Other P0 reverse cuts (not new prize theorems):** BSD S6 keep ell^n Kummer short exact sequences, torsion and Sha[ell^n] with transition maps: log_ell |Sel_{ell^n}|=n rank E(Q)+log_ell|E(Q)[ell^n]|+log_ell|Sha[ell^n]|. This is classical exact arithmetic, not analytic comparison. Cannot divide by n and discard the Sha term without a theorem; actual analytic order vs residual-corrected slope remains open. Hodge H3 use positive rational Hodge-Riemann form on rational (p,p), retaining primitive/Lefschetz indices; exact projection to finite known algebraic span V by inverse Gram matrix gives residual r in V-perp. For ANY enlargement V' of V the projection of r onto V'-cap-V-perp reconstructs the newly resolved portion; positivity alone does not imply r=0. Need actual cycle-class generators for arbitrary X, not an abstract basis. RH retain original zero multiplicities, functional reflection, signed test residual and admissible test-scale/far-tail indices; finite observer collision or truncated positive tests are not universal Weil positivity. Existing #1533 external admission and independent signed-zero compensation remain separate.

No new CI, native kernel, numerical acceptance or Clay endpoint. N2c uses standard classical Sobolev, orthogonal helicities and true finite unforced energy; source owners R225/R388/R596/R568 and consumers R653/R503/R504 unchanged. Historical PNP priority labels below are donor-local, not portfolio priority.


### Historical P vs NP donor owner advance (24 November): concrete selector-3SAT joint overlap and triangular AND-lift geometry

**Live owner reread:** [Agda #1548 at 9cd7ebdc7459](https://github.com/chboishabba/dashi_agda/pull/1548), exact original [ClayP0PolynomialCoverageEndpoint20261124.md](https://github.com/chboishabba/dashi_agda/blob/9cd7ebdc7459ed956f77281642ce62754f8483e2/Docs/roadmaps/ClayP0PolynomialCoverageEndpoint20261124.md), blob 7254ad6c6460bb355e57e7bdbcea4cc18dd6fa61. This head supersedes the earlier same-day P0 roadmap snapshot: **G13a–e now have mathematical proofs/examples or classical reductions in that owner**, distinct from the final universal lower-bound theorem. No new PNP implementation or theorem is duplicated in #1543.

**Actual original-source P0 positive geometry already derived in #1548:**
- G13a finite Boolean-function ambient space V containing 1 and input coordinates, fixed operand a∈V: V+aV=(1+a)V ⊕ aV by disjoint supports, and exact necessary/sufficient restriction criterion for f∈V+aV on the a=0/1 slices. This is an exact ONE-gate shortcut test, not a nonlinear global bound.
- G13b reachable two-AND targets modulo V: **both** parallel ab+uv and serial (ab+u)v with a,b,u,v∈V, including constant 1 in the serial second operand. The earlier restricted-v/constant mistake was fixed on the owner; source reports exact GF(2) finite checks, NOT all-depth completeness.
- G13c a concrete NP-complete selector-of-all-1/2/3-variable clauses F_m on N_m=sum_{j=1}^3 2^j binom(m,j)=Theta(m³) input coordinates. Assignments x induce maximal selector flats H_x indexed by falsified-clause sets Z_x; intersection codimension for H_x and H_y is 2b(m)-b(m-d_H(x,y)), b(m)=sum_{j=1}^3 binom(m,j); arbitrary multi-flat intersections require actual *joint* restrictions, not pairwise distances.
- G13d the existential polynomial quadratic clause witness is NOT a deterministic polynomial solver. A deterministic scalar XOR/free linear and AND-paid circuit corresponds to a *triangular* quadratic lift with y_i=A_i(input,y_<i) B_i(input,y_<i), unique generated evaluation. A superpolynomial lower bound on its multiplicative complexity MC(F_m) would exclude nonuniform P/poly (stronger than P≠NP); this is OPEN, not paid by the mere polynomial existential lift.
- G13e maximal selector flats give exact minimal **DNF** size 2^m, but restricting all width-2/3 selector bits to zero produces the same-family unit consistency U_m=prod_i(1+p_i n_i), with *also* 2^m DNF terms yet exact unrestricted paid-AND complexity MC(U_m)=2m−1. This constructive adversarial shortcut is the decisive no-go for replacing an all-circuits lower bound with assignment-flat count or a DNF size argument. The full selector MC lower bound remains unproved.

**Reverse-solving the FIRST unpaid P0 mathematical lemma after that geometry (do not revert to generic frameworks):**
- P0-G12a / G6a **serialTargetShiftBound**: an invariant/charge that remains valid for arbitrary previous linear functions, unrestricted serial AND operands, target shifts and recomputation on the concrete F_m triangular lifts. Source producers G13a,b, G7/G8, G10/G11; consumer the actual global multiplicative-complexity lower bound.
- P0-G12b / G6b **selectorGoalSeparation**: prove a large simultaneous obstruction arising from width-2/3 selector-clause interactions, rather than the already-falsified unit-only/flat-count metric. Source G13c joint overlap, G13d lift; consumer G12c.
- P0-G12c / G6c **selectorSuperpolynomialGrowth**: for every fixed k and sufficiently large m, the resulting invariant forces MC(F_m) greater than N_m^k **for arbitrary** triangular lifts/circuits, including all sharing/serial bypass. This plus exact NP completeness and standard circuit simulation would yield P != NP; **OPEN**.
- IN PARALLEL original **N1–N3 polynomial charged standard-machine coverage** and **N4–N5/U2–U4 universal deterministic SAT decision obstruction** from the authoritative #1548 / Lean #119 roadmap. Keep direct uniform route alive if the stronger nonuniform G12 route fails; the two approaches are not preconditions of one another. Source finite acceptance and original Agda SATLowerBoundProducer terminal compiler do not substitute for a G12c/N5 proof.

**Forward / reverse two-way checks:** (i) Any proposed invariant must admit actual legal **parallel and serial** AND chords, not just affinely selected cuts. (ii) It must return a low charge on the explicit unit-only shortcut U_m despite its 2^m maximal flats. (iii) Reverse from MC(F_m) superpolynomial in **encoded length N_m**, not in m alone or in 2^m witness choices. (iv) Keep existential assignment x separate from deterministic generated y_i. (v) Verify cost-model and NP-complete source representation through original N1–N3 before consuming the Clay SAT lower-bound owner. The G13 source note reports finite tests, but this #1543 audit only read its exact current Git source, with NO independent rerun of the 1,256/7,424/10,795 tests and no Lean/Agda kernel check. **P0 universal lower bound: OPEN.**

### NS theorem N0 — R568 C1 is exactly a terminal positive Cauchy energy plus physical mixed-helicity trace

**Source algebra and normalization:** start with a genuine REAL/algebraic-helicity R240/R405 Galerkin trajectory, viscosity nu>0 constant, the ORIGINAL complete ordered output fibre I_C(k) for nonzero |k_i|<=C, actual R225 **doubleMixedCell** M_alpha(t)=2(A_alpha(t)-B_alpha(t)), actual R388 **doubleForcing** D_alpha(t), and rate r_alpha=nu(|p_alpha|²+|q_alpha|²)>0. The R388 mixed tangent is M'_alpha=D_alpha-r_alpha M_alpha, **provided** the R560 literal-trajectory derivative calculus is inhabited. R596 already proves 4 F_k = full coherent Gram + weighted flux tangent (using R597 coherentWork=2 Re Hermitian). Do not create another factor-four owner.

Put K_ab=1/(r_a+r_b), define the positive SOURCE-normalized Gram and physical mixed-output trace (all original nonzero outputs):
$$
Q_C(t)=2\sum_{k\ne0,\ |k|_\infty\le C}
  \sum_{\alpha,\beta\in I_C(k)}
    K_{\alpha\beta}\operatorname{Re}\langle M_\alpha(t),M_\beta(t)\rangle,
\quad
H_C(t)=\sum_{k\ne0,\ |k|_\infty\le C}
    \left\|\sum_{\alpha\in I_C(k)}M_\alpha(t)\right\|^2.
$$
Here F_C(t) is EXACTLY R568.globalForcingFull, summing the original outputForcingFull rather than a free proxy or rate-lifted L. For fixed cutoff and t, finite bilinearity plus R388 yields
$$
\frac{d}{dt}(Q_C/2)
 =2F_C-H_C,\qquad
\boxed{\;4F_C=Q_C'+2H_C.\;}
$$
**Proof, not a new assumed inequality:** differentiate each term; the two D terms combine to 2 F_C by Hermitian symmetry, while (r_a+r_b)K_ab=1 makes the remaining signed damping double sum equal to -||sum M_alpha||² per output. R596/R597 provide exactly the displayed source factor 2; no helicity positivity was used to infer the sign of F_C. Under genuine scalar FTC/integration (R495/R565/R570 sockets), integrate the same finite trajectory:
$$
\boxed{\;4\int_0^T F_C(t)\,dt
=Q_C(T)-Q_C(0)+2\int_0^T H_C(t)\,dt.\;}
\tag{N0}
$$
No false assertion that the bare Agda rational Time field automatically supplies differentiable real helicity, continuous time or R565 FTC.

**NEW uniform signed LOWER corollary, not the requested upper:** from (N0), Q_C(T)>=0 and H_C>=0,
$
4\int_0^T F_C(t)\,dt\ge-Q_C(0)
  \ge-\frac{32}{\nu}\|u_0\|_{\ell^1(\mathbb Z^3)}^4,
\qquad
\boxed{\int_0^T F_C\ge-\frac8\nu\|u_0\|_{\ell^1}^4}.
\tag{N0L}
$
For each true finite Galerkin trajectory with fixed smooth mean-zero initial datum this is uniform in BOTH cutoff C and terminal time T (wherever the trajectory/FTC is valid); it is a CLASSICAL substantive one-sided result. It means the negative time-integrated signed source cannot escape to -infinity under these original smooth hypotheses. **Crucial sign firewall:** R568 explicitly asks for an UPPER bound on 4 int F_C, and R653 separately asks for a physical strict-surplus LOWER relative inequality. N0L proves NEITHER; reversing its inequality would be a fatal error. N0L also requires N2's separately proved initial Gram ceiling; it is not a free consequence of R568's bare rational interface. The source R596 finite identity, original double-mixed laws and standard finite ODE calculus are its ingredients, not an invented new nonlinear estimate.

**Geometric positivity:** for actual positive rates,
$$
Q_C(t)=2\sum_{k\ne0}
 \int_0^\infty
  \left\|\sum_{\alpha\in I_C(k)}
       e^{-r_\alpha s}M_\alpha(t)\right\|^2 ds\ge0 .
$$
The auxiliary Laplace variable s is **not physical time t**, the physical output k, Wilson Euclidean time, RG scale or Singh hyperfabric phase. This is the classical Laplace transform of 1/(r_a+r_b), not yet an Agda real-exponential proof. R440 owns prior finite factorization; this statement is the analytic positivity/endpoint interpretation, not a duplicate R440 compiler. The exact distinct-rate radical does not invalidate Q positivity or prove F positivity: many within-rate sum-zero modes are invisible.

**New BIDI reverse solve of the full R568 upper (necessary AND sufficient given FTC):**
$$
4\int_0^T F_C\le B(u_0,\nu,T)
\quad\Longleftrightarrow\quad
\boxed{\;Q_C(T)+2\int_0^T H_C\le B(u_0,\nu,T)+Q_C(0).\;}
\tag{N1}
$$
The right side is a **sum of two nonnegative quantities**, not signed cancellation left to discover after the exact flux derivative is removed. If Q_C(0) has a cutoff-independent ceiling, a cutoff-independent B forces independent cutoff-uniform upper bounds on BOTH Q_C(T) and the integrated H_C. Conversely bounds on both supply the R568 C1 record. A pointwise F↔rate-lift sign transfer is neither necessary nor true (original physical witnesses seeds 61,63). A positive-definite Cauchy kernel alone cannot bound these two quantities.

**Exact original Fourier geometry of the trace:** original R225/R224 has sum_alpha M_alpha = 4 sum_{p+q=k} u_p^+ × u_q^- on the complete fibre. With Parseval-normalized Fourier coefficients and the original nonzero output cutoff projection P_C^neq0,
$$
H_C(t)=16\left\|P_C^{\ne0}\left(u_C^+(t)\times u_C^-(t)\right)\right\|_{L^2(\mathbb T^3)}^2 .
$$
Thus the concrete *necessary* spacetime trace receipt in N1 is 32 int_0^T ||P_C^neq0(u_C^+×u_C^-)||_2² dt. This is a genuinely mixed-helicity, output-projected object, **not** the full u×u (identically zero), an arbitrary R236 covariance, a deleted zero-mode pair, or a sum of fictitious independent representatives. R681/R682/R683 already own a DIFFERENT but complementary p-dot-q rate/cross-gradient normal form on the live R408/R664 source; those identities must be used to seek the quantitative H and terminal Q bound rather than rebuilt.

### NS theorem N2 — cutoff-independent initial Gram payment for the smooth mean-zero source class

For the ORIGINAL cubic fibre and any nonzero retained k, the midpoint identity gives 2(|p|²+|q|²)>=|k|², hence K_ab<=1/(nu |k|²). True helical projectors P± are orthogonal contractions on transverse nonzero Fourier modes. The exact R225 definition M=2(A-B) with A=u_p^+×u_q^- and B=u_p^-×u_q^+ gives
$$
\|M_{p,q}\|\le4\|u_p\|\|u_q\| .
$$
Let a_p=||u_0(p)||, with a_0=0 for the **mean-zero** initial class. Keeping every ordered original p+q=k incidence and no multiplicity deletion,
$$
\begin{aligned}
0\le Q_C(0)
&\le\frac2{\nu}\sum_{0\ne k,\ |k|_\infty\le C}
  |k|^{-2}\left(\sum_{p+q=k}\|M_{p,q}(0)\|\right)^2\\
&\le\frac{32}{\nu}\sum_k[(a*a)_k]^2
 \le\boxed{\frac{32}{\nu}\|a\|_{\ell^1(\mathbb Z^3)}^4}.
\end{aligned}
$$
The last bound uses (i) ||a*a||_2<=||a*a||_1=||a||_1² and (ii) |k|>=1 on the actual nonzero output. For smooth mean-zero u0 on the 2pi-periodic torus and any s>3/2, Cauchy–Schwarz gives
$$
\|a\|_{\ell^1}
 \le\left(\sum_{k\in\mathbb Z^3}(1+|k|^2)^{-s}\right)^{1/2}
 \|u_0\|_{H^s},\qquad
\boxed{Q_C(0)\le \frac{32}{\nu}
  \left(\sum_k(1+|k|^2)^{-s}\right)\|u_0\|_{H^s}^4.}
\tag{N2}
$$
**Mathematical result:** an explicit cutoff-independent initial **R596 Cauchy Gram** bound is paid CLASSICALLY for Fourier-truncated smooth mean-zero initial data with genuine nonzero-mode helical projectors. This is **not** R565's distinct initial selfFlux calibration and not an Agda kernel or proof of the global-in-time bound. If an admissible general-data formulation allows nonzero mean, its zero-mode/Galilean reduction needs a separately stated source-correct transport, not an assumed u0(0)=0.

**Steelman of N1:** seek a uniform H bound by compensating mixed-helicity critical/output interactions through R682/R683, with a terminal Q estimate propagated by the same true physical dynamics. One possible SUFFICIENT but likely too-strong route is a uniform int||u_C||_4^4 via the L4-bounded helicity projectors; this alone is NOT the right necessity theorem and cannot be inferred from Leray energy without new NS-specific work.

**Adversarial geometry / non-promotion:** smooth compactly supported divergence-free phi on the torus, nonzero smooth eta supported away from t=0, and u_epsilon(t,x)=epsilon^{-3/2}eta(t/epsilon²)phi((x-x0)/epsilon) give sup_t||u||_2²=O(1), int||grad u||_2²=O(1), but int||u||_4^4=const*epsilon^{-1}->infinity. This is a functional-analytic counterexample to the **generic inference** "Leray energy axioms alone imply uniform L4 spacetime"; it is emphatically **NOT** a Galerkin NS solution, a counterexample to the special mixed-helicity H trace, or a Clay obstruction. Any estimate of H must use original NS/helicity structure, not inject a false energy→L4 black box.

### NS theorem N3 — reverse-solve the independent strict R653 C2 endpoint on the SAME currency

Define the exact original J_C(T)=int_0^T(R557.selfGram+R557.selfFluxTangent) and original retained-margin physical S_delta,C(T) from R648. R652 ALREADY proves
4 int F_C =2 int R406_C +J_C.
R653 ALREADY proves C2 is precisely 2S_delta,C+J_C <= 4 int F_C, not a third independent inequality. Using N0 and retaining ALL source terms gives
$$
\boxed{
2S_{\delta,C}(T)+J_C(T)+Q_C(0)
\le Q_C(T)+2\int_0^T H_C(t)\,dt
\le B(u_0,\nu,T)+Q_C(0).
}
\tag{N3}
$$
**Both directions:** the left N3 inequality is exactly original R653 C2 provided R652 and N0 hold; the right N3 inequality is exactly original R568 C1. Applying the existing consumers R645/R648/R503/R504 with real full-cutoff and margin hypotheses is separate. There is NO claimed sign for J_C; do not silently identify its R557 *diagonal* selfFlux tangent with the FULL R596 flux-tangent without the existing R560/R570 exact source transport. Initial Q0 payment does not imply left-margin C2. A bound on the C1 right cannot by itself pay the C2 left.

### NS proposed exact remaining lemmas and named existing source consumers (after N0–N3)

| Phase / proposed theorem (NEW identifiers; not Agda declarations) | Existing producer and actual original currency | Exact missing proof / deliverable and consumers |
| --- | --- | --- |
| NS-P0 originalRealHelicityFieldAndTime | R240/R405/R408; original R225/R388/R560, current Agda fixed F=Q; finite true-state #1543 | Construct real/algebraic/Bishop field, correct sqrt|k| projectors, full reality/transversality and genuine R240 derivative/time path. Do not cast a continuous real solution as Q-valued. Consumer: R596/R568/R653 |
| NS-P1 originalR596CauchyEnergyLiveFTC | R596/R597 fixed-system finite identity, R388 tangent, R560 source derivative, R495/R565/R570 scalar FTC | Native same-k/source global Q'_C=4F_C-2H_C, FTC and all C/k sums; N0 already mathematically derived, **formal live receipt OPEN**. Consumers: R568 record and R653 N3 |
| NS-P1 originalInitialCauchyGramUniformSmooth | R225 c=4 source, midpoint-rate inequality, Q positive | **CLASSICAL N2 mathematical bound obtained in this roadmap** for fixed smooth mean-zero u0, s>3/2. Native analytic/Agda rebase and nonzero-mean extension OPEN; do not conflate with R565 initial selfFlux. Consumer: N1 initial baseline |
| NS-P2 originalUniformMixedHelicityTrace | R225/224 source: Msum=4(u+×u-)_k; R681/R682 actual live p-dot-q; R683 vector normal form | For every C and original smooth u0, bound 32 int||P_C^neq0(u_C^+×u_C^-)||_2² by an acceptable **C-independent** budget without assuming global regularity. This is the true positive-trace half of R568 C1; OPEN |
| NS-P2 originalTerminalCauchyGramUniform | R596 Cauchy K positive; R624/R628/R634 self/external, R686 original signed commutator endpoint | For every C and T, bound Q_C(T) on actual same Galerkin flow without circularly assuming a uniform strong norm or importing false R687 sign inheritance. Together with preceding and N2 -> actual C1 upper; OPEN |
| NS-P2 originalStrictPacketMarginN3 | R648/R645 packet structure, R652/R653 SAME finite R406 currency | Produce strictly positive retainedMargin and TRUE 2S_delta+J+Q0<=QT+2int H on exact unforced R240 trajectory. This is the C2 lower, not a consequence of C1; OPEN |
| NS-P3 originalUniformR568R653ToPDE | R568 C1, R653 C2, R503/R504/R415, R571 conditional M2, existing R104 layer-cake | Exact full time/output/cutoff uniformity, bona fide 3D periodic NS compactness/continuation all smooth initial data, and official Fefferman B statement; A independent, C/D external. OPEN |
| NS-P4 originalSourceNativeAcceptance | original source owners and exact head; canonical NSProofControl | Once mathematical proofs exist, native full field/FTC/N0–N3 trust, original type/positive cone and endpoint citation. Deferred; do not replace P2/P3 |

**Both directions of attempted proof:** FORWARD original R240 flow -> real helical P± -> exact R225 M -> R388 tangent + R596 Gram -> N0 -> uniform **N1** (R568 C1) AND strict **N3 left** (R653 C2) -> existing terminal compilers -> actual global 3D PDE. BACKWARD start from the exact Fefferman B smoothness quantifiers -> needed true cutoff-independent critical barrier -> R568/R653 literals -> inverse N3/N1 requiring the positive Q(T)+mixed trace resource, whose initial Q(0) is now bounded by N2; attempt R682/R683 signed cross-gradient compensation for the TWO still unpaid dynamic estimates. Failure handling: if positive trace cannot be controlled from existing source estimates, test special helical/no-go on ACTUAL projected Galerkin solutions, not arbitrary independent D/M or non-physical energy paths; if native F=Q fails, test physical algebraic/real field and original rational source **both** without rewriting merged owners. **Reverse implications for R568 are equivalences of the chosen proof currency, not a metatheorem that no other approach could solve Clay.**

**Executable acceptance:** [NS endpoint trace BIDI checker](../../scripts/check_ns_r568_endpoint_trace_steelman_20261124.py), new Git blob f5e4b640f2d04b13fdf97fc1c29a2d7de6135981. Locally executed exact SymPy 1.14: 18 source-admissible C=1 ordered cells and masses (1:2,3:8,5:8); exact direct-vs-rate-bucket polynomial Q/F; formal Qraw'=2F-H for a nontrivial complex 3-vector polynomial path; exact physical-time integral forward identity and reverse terminal inequality in BOTH true/false budget directions; deliberately wrong 1x vs 2x source factor fails; exact lattice rate lower bound across C=1,2 all nonzero original outputs. Rational fixture receipts Qsource(0)=419/20, Qsource(2/3)=11309/540, 2int H=5921/81, 4int F=29602/405. **This is an ABSTRACT source-type time-polynomial diagnostic, NOT a true R240 trajectory**. The separate [physical source verifier](../../scripts/check_ns_r568_physical_source_weld_exact_20261123.py) already passed 64/64 actual time-zero projected Galerkin signs and R388 tangent at source blob 9b6ea0db5c9698623c92df5bee94b6b087abe721. Combining these diagnostics does NOT create a true physical time trajectory or native FTC. No new Agda/Lean kernel/CI check.

**Relevant branch-owner reconciliation:** source merged Agda #1499 and NS #1501, historical NS #957 closed unmerged; live NS draft #1543, TOE owner #1384 distinct; active Agda PNP #1548, Lean PNP #118/#119/#120; active YM #1536/#1544 and donor #1444; active RH Agda #1533 and merged Lean #113; BSD/Hodge selected source in merged #1499/Lean #108. Preserve exact owners, original attribution and the source-store BIDI manifest. No new independent competing Clay roadmap; this is an addendum on the existing coordinator and must be mirrored in NSProofControl and canonical six-endpoint JSON without changing historical 135 owner symbols or 0/6 original DASHI Clay proof status.



## 23 November 2026 — six-lane coordinator synchronisation after exact physical R568 no-go

Canonical six-endpoint machine-readable record ClaySixFrontierABCExactGates20261114.json is now updated with ns_r568_actual_galerkin_20261123 as a nonterminal **source-physical pointwise SIGN no-go**. No completed/active counts or Clay endpoint statuses changed. P0 source audit, B1 REFUTED unrestricted R820/R823 signed reserve, and selected real-Fourier C1/C2 mathematical closure under original 15-Nov Python/SymPy protocol remain four decided entries; eleven active, 0/6 actual Clay. Portfolio C1/C2 selected R853 tests must NOT be conflated with **local R568/R653 C1/C2**, both true signed spacetime estimates still OPEN. Fefferman forced alternative C/D are a third unrelated namespace.

Native source full Fourier u,N(u), real-algebraic helical ±, original R225/R388 double products, R566 signed forcing and R687 lifted work rechecked 64/64 in four separate exact checkpoint blocks, current script Git blob 9b6ea0db5c9698623c92df5bee94b6b087abe721. Seeds 61/63 provide independently reproduced both sign orientations. Original R596 2x coherent-work Cauchy Gram and its R388 finite tangent identity now additionally tested and normalized; physical R240 time, R565 FTC, original R568 C1 and R653 C2, true signed cross-gradient compensation and 3D PDE theorem remain OPEN. All source original R/RXYZ modules already merged; R682/R683 live cross-gradient/vector geometry ALREADY exists, do not duplicate it. Exact Q(sqrt2,sqrt3,i) finite-helicity witnesses still need native lawful field-extension transport from Agda's rational RealField. Original BSD/Hodge/Karp/RH/YM lanes unchanged.



## 23 November 2026 — NS original source-produced helical Galerkin sign barrier

[**Exact finite real-helicity source and two opposing pointwise signs**](NSR568OriginalGalerkinHelicityRateSignCountercontrol20261123.md): new standalone byte-identical [64-state source-weld regression](../../scripts/check_ns_r568_physical_source_weld_exact_20261123.py), blob `efad812d7699118ccb0396eb0165d4e6ba323fa8`. Uses actual C=1 original ordered cubic p+q=k, divergence-free conjugate-real velocity, same u's projected NS quadratic force, actual helical curl eigenprojectors and R225/R388/R566/R687 double-forcing/product algebra; **64/64** exact tests, source factor-four and factor-eight, direct/bucket/projector and **two exact strict sign-reversal witnesses** (61 F>0>L; 63 F<0<L). Universal pointwise sign transfer between unlifted R568 and rate lift fails **on physically generated finite states**. The genuine source Agda rational field cannot contain sqrt2/sqrt3 helicity values without further field extension; this executable is not a kernel inhabitant and does NOT close C1/C2. New physical analytic route must seek *dynamic/output-integrated signed compensation* (R596/R624/R628/R634, paired R681/R689) rather than forbidden pointwise sign inheritance. Original strict C1 R568 signed upper, C2 R653 lower, R565 FTC, 3D PDE open; BSD/Hodge/Karp/RH/YM unchanged; 0/6 prize claims.



## 23 November 2026 — NS rate-kernel exact radical, corrected physical-output census

[Original R568 midpoint/rate-Cauchy radical exact result](NSRateResolvedCauchyRadicalOriginalSource20261123.md) supersedes the earlier loose rate-bucket enumeration bound. Actual original output requires |k_i|<=C, so valid source arithmetic acceptance is **37/37** full original output fibres / **26,934** incidence checks, not 44/27,452 from broad k-outside-cutoff mathematical test cases. Original rate masses have midpoint symmetry, parity m≡|k|² mod2 and **<=3C²+1** classes. The positive rational Cauchy matrix exactly factors through source rate incidence B with rank #distinct rates R and radical of dimension N−R; entire within-rate zero-sum sector, containing but generally larger than p/q swap-odd, is invisible to both-currency signed R541/R567 pairing. C=5,k=(5,0,0) gives N=726,R=42,null=684. Full original source sidecar is required to reverse the quotient. **Analytic C1/C2 remains OPEN**; the proxy doubleForcing/doubleCell values in local tests are not produced by a physical R240 trajectory. Existing merged R541/R567/R568/R596/R624/R628/R634/R652/R653/R687–R689 owner implementations remain unreplaced. Other Clay lanes unchanged; 0/6 original Clay results.



## 23 November 2026 — R568 alpha correction: exact Cauchy rates and two-sided C1/C2

[New R568 signed rate-bucket BIDI and exact remaining-lemma audit](NSR568RateResolvedSignedBucketBidiSourceMaxCut20261123.md), [byte-identically executed local checker](../../scripts/check_ns_r568_rate_bucket_bidi_exact_20261123.py), Git blob a76e8847a61521a4c4cb88fcc861ebb4a92fb85f. 64 full literal original ordered cubic-fibre rational tests; 726/1352/2250 incidences become 42/67/92 integer rate classes on k=(5,0,0), C=5/6/7, with reversible incidence-sidecar and no loss of source p/q/zero records. **Free vector carrier sign control**, not literal NS flow: source-allowed rates 13 and 17 give unlifted R541/R567 scalar F=46/16575>0 and rate-lift scalar L=−1/5<0, while the Cauchy kernel is positive definite. Do not infer sign transfer from positivity, and do not call a zero-R236-work spectator double-zero in R568.

The exact missing NS analytic target is **both sides** of existing R653 C1/C2 signed sandwich 2S_delta+G+H <= 4F <= B on the same physical R240/R405/R406 source, with R565 scalar FTC/terminal and actual 3D continuum still independent. Reuse original R596/R624/R628/R634 self/external signed source decompositions and R687–R689 rate-lifted cancellation. No new Agda root or CI acceptance. All other five Clay lanes unchanged; the genuine original prize count remains 0/6.



**Authority:** This source-to-endpoint alpha index supplements the canonical six-Millennium, NS, Karp, BSD, Hodge, GRH and YM roadmaps. It reuses the original theorem owners. Mathematical classical theorem, executed finite/SymPy check, source-written Agda/Lean candidate, local kernel acceptance and original Clay prize proof are distinct categories. In this PR no new original Clay endpoint is proved (0/6).

## Verified source and new local receipts

- **NS:** The original instantaneous R236 source has S_C=R_C W_C−N_C V_C and its zero-work padding cocycle is ALREADY proved by NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact. PR #1543's rational Leray-transverse four-cell fixture tests that *source only*. The original R568 source is a DIFFERENT signed, time-integrated, globally output-summed nested forcing-square. The physical R541/R542/R573/R547→R568 same-object BIDI was already source-written.
- **Karp:** Karp21NativeGammaAllLengthCompositePhysicalExact already owns the actual positive-gamma literal finite-table composition: token length 2k+1 takes 2k+2 machine steps. Original binary priority and native four-symbol tape substrate already exist. PR #1543's byte-identical local Python reference gives 9,942/9,942 decision comparisons, with 300 longer histories, up to 16 edges, maximum observed 10,752 local cell/head operations and 1,139 physical tape cells. Python controller branches and addresses are NOT an Agda finite tape table.
- **BSD:** original E32, E:y²=x³−x, its isogenous partner E':Y²=X³+4X, and TRUE dual. Byte-identically locally executed script [E32 isogeny checker](../../scripts/check_bsd_e32_original_2isogeny_bidi_20261123.py), Git blob d43aa30773b572551b749b5ac1b153be4c798ce5: exact bidirectional generic rational-function compositions with doubling, exception checks, 11,616/11,616 group-law comparisons over 11 odd primes. Classical Tate 2-isogeny descent yields rank(E32/Q)=0 from *exact* square-class images. This rank-zero result is classical PRIOR ART; no native Kummer/rank proof yet.
- **Hodge:** actual smooth non-product X=Gr(2,4), Plücker Klein quadric. Byte-identically locally executed [Schubert checker](../../scripts/check_hodge_gr24_schubert_cycle_bidi_20261123.py), Git blob c437b482b547ae0a5773ee9a8f5931b89a2778c0: six literal flag-incidence classes; exact cup/Giambelli/Poincaré dual pairing, 7,200/7,200 rational inverse cycle coefficient recoveries. Critical orientation: sigma_2=lines through a fixed point; sigma_11=lines contained in a fixed plane (not vice versa).

## NS — exact analytic and geometric outstanding

**NS-A [P0 analytic, OPEN]:** Given actual R240/R405 physical Galerkin family T and support R, prove an inequality on the literal R568 object

$$ 4\int_0^t \mathrm{globalForcingFull}_C(s)\,ds\le B(T,R,t) $$

for EVERY cutoff C, with B independent of C and valid original initial-data/viscosity assumptions. Equivalently inhabit existing LiveNested.NestedSpectatorSpacetimeBudget and feed it through already-proved nestedBudgetBuildsR568. Preserve all k, alpha, beta and time indices and *signed aggregation before norms*. The R236 C^5 padding no-go does NOT imply any R568 divergence or a needed R236-to-R568 cancellation. Do not invent that equality.

**NS-B [P0 terminal, OPEN]:** supply the actual scalar FTC/integration R495/R565 contract on R240 trajectories, initial self-flux calibration and genuine R557/R553/R504 terminal estimates. The source status missingConcreteScalarFTC568 differs from the genuinely new analytic missingCutoffUniformLiveCommutatorSpacetimeBudget568; list both.

**NS-C [negative controls]:** preserve exact rational P_kM=M≠0 and active deep-FL initial-source fixture, the earlier axial P_kM=0 control, all zero-work incidences and merged #1539 W2 sign no-go. None proves time-dependent physical regularity.

**NS-D [Clay, OPEN]:** bridge uniformly bounded cutoff dynamics to the actual admissible 3D incompressible PDE regularity/existence-or-breakdown statement. No source finite-time/single-slice result replaces original PDE quantifiers.

## Karp-21 / P versus NP — exact executable and complexity outstanding

**E1-F1 [OPEN]:** compile WHOLE original canonical graph-word gamma/signed zigzag and certificate grammar, malformed source cases, strict u<v<n sorted unique edges, the ACTUAL early 3m suffix-length guard (NOT n-choose-two/3m+1), actual W>0 threshold, history and selected signed ledger into ONE literal local finite TableProgram. Reuse existing all-length positive-gamma table.

**E1-F3 [OPEN]:** original-source ↔ native tape-state BIDI with source word/certificate coordinates, token offsets, chronological 2m endpoint bits, signed ripple registers, first-enabled rule priority, bounded physical stuttering and correct raw-finished vs binary-accepted *threshold observation* rather than false terminal identity.

**E1-F2/F4 [OPEN]:** charge persistent + temporary heap/tape/copy/stack/position/scratch, local head scans and reset, malformed time, carry width and host dispatch elimination. Prove one explicit physical instruction polynomial in TOTAL source-word+certificate bit length. Existing 2m(m−1) comparisons and m+1 priority-source steps do not alone bound tape time. Python measured 10,752 operations is an observation, not a polynomial theorem. Pin Agda 2.9, exact G2/G3/G4 source admission and trust check.

**Original P vs NP [OPEN]:** finite N21 bitword NP membership E2 already belongs to existing classical proof; E1 machine completion is not universal SATNotInP. The all-deterministic-polynomial-decider lower-bound remains mathematically separate.

## BSD — selected classical arithmetic and exact native/universal debt

**Actual forward/dual on E32:** on nonexceptional affine points

$$\phi(x,y)=(x-1/x,\ y(1+1/x^2)),\quad
\hat\phi(X,Y)=((X+4/X)/4,\ Y(1-4/X^2)/8).$$

Both are group homomorphisms CLASSICALLY, with kernels {O,(0,0)} on their respective curves, and \hat\phi∘\phi=[2] (also \phi∘\hat\phi=[2] on E'). E(2-torsion)={O,(0,0),(1,0),(-1,0)}; phi of either ±1 two-torsion is E' (0,0). E' (2,4) doubles to (0,0), and maps by the dual to E (1,0). The rational-function field identities and finite-field group laws were exactly checked, not Agda typechecked.

**Classical Tate rank-zero BIDI (already known mathematically, now attached to actual selected source):** For y²=x³+a x²+b x, alpha(O)=1, alpha((0,0))=b mod rational squares, alpha(x,y)=x mod squares for x≠0. The standard valuation proof shows primes outside b have even x-valuation; hence squarefree alpha images have prime support dividing b. On E b=−1 this leaves {±1}, both realized. On E' b'=4 this leaves {±1,±2}; the real equation Y²=X(X²+4) forces X≥0, so negatives are absent, and O and (2,4) realize {1,2}. Tate's ORIGINAL rank formula

$$2^{r+2}=|\alpha_E(E(\mathbb Q))|\,|\alpha_{E'}(E'(\mathbb Q))|=2\cdot2=4$$

gives **r=0**, independently of BSD/L(E32,1). It is a published theorem instantiated on the selected curve; neither finite tests nor a record-level alpha function prove Tate descent. References: [Dixit–Murty–Pathak, §2](https://www.cmi.ac.in/~siddhi/Rank.pdf); [Dujella, §15.5](https://web.math.pmf.unizg.hr/~duje/pdf/section15-5.pdf). Actual all-place classical Kummer–Selmer–Sha[2] exactness was already established in the separate ClayBSDOriginalS2ActualKummerShaClassicalClosure20261116 roadmap; do NOT re-prove it abstractly.

**BSD-S1/S3 [native OPEN]:** original proper E32 and E' group laws, actual two isogeny maps including O and all exceptional 2-torsion; actual prime-support and real-sign alpha to Q×/Q×² as group homomorphisms; genuine Tate index and MW quotient attaching r=0; actual global/local H¹ and Sha[2] with all completions and genuine Kummer diagram. Do not upgrade a rational function identity to an Agda group theorem.

**BSD-S4 [native OPEN]:** original analytic f_E32=eta(4z)²eta(8z)² all-n level-32 newform equality, actual elliptic L(E32,s) same-source, genuine Fricke/Mellin/Gamma infinite analytic comparison and L(E32,1)>0 using existing EllipticCMLevel32FrickeMellinExact and MellinSplitFunctionalEquationExact. S4 mathematical selected positivity is already CLASSICALLY closed, native OPEN.

**BSD-S5 [selected refined native OPEN]:** published Rubin CM special-case/full rank-zero BSD earlier in repo; native odd-primary Sha, regulator/period/Tamagawa and exact leading-coefficient equality still open.

**BSD-S6 [actual Clay OPEN]:** universal rank equality for *every elliptic curve over Q*. Full Sha-regulator leading coefficient is distinct refined version, not identical prize quantifier.

## Hodge — actual non-product incidence geometry and universal boundary

**Classical literal X=Gr(2,4):** X is smooth projective dimension 4, the lines in P³, Klein quadric in P⁵. Put h=c1(S*), c=c2(S*), with weighted codimensions 1 and 2. Classical Schubert/Chern ring:

$$H^*(X,\mathbb Q)=\mathbb Q[h,c]/(h^3-2hc,\ h^4-3h^2c+c^2).$$

Actual flag-incidence classes: sigma_empty=1; sigma_1=h (lines meeting a fixed line); sigma_2=h²−c (**lines through fixed point**); sigma_11=c (**lines inside fixed plane**); sigma_21=hc (point-and-plane pencil); sigma_22=c² (fixed line = Grassmannian point). Six cohomology basis classes, Hodge diagonal codimension ranks (1,1,2,1,1), off-diagonal zero by original affine Schubert-cell decomposition. Crucially **sigma_2²=sigma_11²=sigma_22, sigma_2 sigma_11=0**, and Plücker degree ∫sigma_1⁴=2.

**BIDI all rational Hodge classes on THIS X:** complementary partition lambda^c gives exactly dual Schubert basis, so for any original rational class alpha, recover unique rational coefficients a_lambda=∫alpha∪sigma_(lambda^c). The literal rational algebraic cycle Z(alpha)=sum a_lambda [Omega_lambda] has cycle class alpha. The 6×6 Poincaré matrix is involutive with determinant 1. This is *classical geometry* combined with exact executable algebra, not a native singular/de Rham proof. Standard original [Schubert/Pieri geometry](https://www.math.uzh.ch/en/fileadmin/user/kresch/publikation/goe07.pdf). It extends CLASSICALLY to actual smooth projective algebraically cellular varieties (e.g. complex Grassmannians), NOT to arbitrary X.

**Hodge-H1 [native OPEN]:** original H^{2p}(X,Q) embedded into complex/de Rham cohomology and actual H^{p,p}, preserving the rational intersection, not an arbitrary rational HodgePiece record. General projective Kähler Hodge decomposition itself is classical prior art.

**Hodge-H2 [native OPEN]:** genuinely construct original Gr(2,4) Plücker projective variety, tautological sequence and literal six Schubert flag algebraic cycles, their singular/cohomology classes, Giambelli/Pieri, perfect cup pairing and inverse cycle map; *same source* Chow→singular→de Rham comparison. Existing P¹ source weld cannot be renamed to this.

**Hodge-H3 [actual Clay OPEN]:** for every smooth projective complex X, all p, and every alpha in the true rational (p,p) intersection, produce a genuine rational codimension-p algebraic cycle. Smooth projective NOT necessarily cellular, rational cohomology NOT merely abstract Q coordinates. Classical Lefschetz (1,1) is not universal H3.

## RH/GRH (P0) and YM (separate) — preserve source owner authority

**RH / all-character Dirichlet GRH:** active [PR #1533](https://github.com/chboishabba/dashi_agda/pull/1533), controlling AlpogeGRHGeometricTransport20261121 roadmap, externally reported independent source checked on pinned Lean v4.33.1/Mathlib, not locally imported. Existing zeta RH ⇄ Clay RH BIDI and original Mellin/G2 owners are already source-written. Exact unpaid: original all-five Lean #113 statement/kernel/axiom admission; root-compatible proof transport, per-modulus/per-character analytic L-identity and original all-character quantifiers; keep zeta RH, Dirichlet GRH and CM/elliptic Hecke different. No promotion from conditional Agda receiver to verified GRH.

**Yang–Mills:** active [PR #1536](https://github.com/chboishabba/dashi_agda/pull/1536) and [PR #1544](https://github.com/chboishabba/dashi_agda/pull/1544); canonical ClayYMProofRoadmap remains controlling. Original SU(N) four-dimensional Wilson/R445 reflection, CMP119/122/116 and W3 restoration jets are source owners. Exact unpaid: literal same-finite-Gibbs original geometry/halfspace reflection, all-coupling field bounds with correct coupling/volume limits, OS continuum nontriviality and strict mass gap, then **every compact simple group**. Finite Haar/jet coefficients, conditional CMP records and Boolean source flags cannot be promoted to original continuum theorem. YM authoring is outside this PR to avoid colliding with active owner branch.

## Attribution and acceptance rule

Each proposed lemma must state source owner and exact current SHA; original object, time/space/phase/zero/exception coordinates; forward relation AND reverse recovery; classical hypotheses; an independent negative control; exact local test/byte hash if present; Agda/Lean kernel and CI status; the specific original gate (not just an iteration number). Do not count already published theorems twice or turn finite regressions into universal Clay conclusions. Original Clay endpoints newly proved here: **0/6**.
