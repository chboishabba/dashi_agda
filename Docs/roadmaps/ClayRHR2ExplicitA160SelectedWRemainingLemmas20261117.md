## 23 November 2026 — P0 bilateral completed-poles → ORIGINAL W holomorphic contour *ACTUAL ZERO SUM* (new specific route to FarExact)

**NEW source-specific exact construction beyond reflected pole algebra:** the original even compact signed four-window physical profile `P_W(v)` has entire cosine transform `C_W(z)`. Set original `r=t/16`, `s0=1/2+i t`, and holomorphic test `f_W(s)=r^-2 C_W(-i(s-s0)/r)`. At a real actual off-line zero `rho=1/2+a+i gamma`, its SAME-γ completed-xi reflected partner `rho#=1-bar(rho)`, source `q=(gamma-t)/r,alpha=a/r` and original kernel identity give exactly
  `f_W(rho)+f_W(rho#)=2*r^-2*W.signedNormalizedPairKernel(alpha,q)`.
The EXISTING Lean `signedLiteralPairSourceTerm_eq_normalizedPairKernel` shows this is the **actual literal zero-side summand** (with original multiplicities), not an invented Fourier-pole connection. Critical-line a=0 fixed zeros contribute once. For a reflection-saturated finite rectangle D with no ξ zeros on boundary, residue theorem gives
  `(1/(2pi i))∮_(∂D) f_W(s)*(ξ'/ξ)(s) ds = Σ_(rho∈D) mult(rho)*f_W(rho)`,
and horizontal ±a pair reassembly equals the pre-existing full original real signed-kernel zero sum. The `FarExact` cutoff `|q|>eta` is NONHOLOMORPHIC; recover FarExact by subtracting true local (including SameOrd) from the FULL contour sum, with source endpoint atoms. On left/right contour deformation `ξ(s)=ξ(1-s)` also maps target ordinate +t to −t, retain negative-height source rather than silently identify histories. Reuse original `RiemannZetaMuExactAbel` and `FourierMass` to compare the deformed ξ'/ξ contour and original µ/prime side. Uniform outer/horizontal contour bounds, signed full complement, strict post-sixth A2 inequality remain OPEN; no RH/GRH.

Independent **actual SymPy residues** for all four poles of a reflected polynomial quartet, original atomic Fourier test and selected finite r,t, pass. [NEW exact proof ledger](https://github.com/chboishabba/dashi_agda/blob/research/alpoge-grh-geometry-bridge-20261121/Docs/proofs/RHGRHBilateralCompletedLogPolePairQuarticAdverseMass20261123.md) (commit 7c37914a), [source polynomial/analytic regression](https://github.com/chboishabba/dashi_agda/blob/research/alpoge-grh-geometry-bridge-20261121/scripts/check_rh_bilateral_completed_xi_logpoles_20261123.py) (7d84996e). Same source local adverse fourth-phase tightening from existing `3/2` to exact `1/2` per zero, original log bound `9/2 A0 log` to `3/2 A0 log`, and original adverse sign-sector cutoff `|gamma-t|<(1+sqrt2)/2` remain ready for source-specific Lean weld (kernels deferred, user requested local SymPy).

---
## 23 November 2026 — P0 new bilateral ξ'/ξ pole and STRICT local adverse P4 MASS sharpening, NOT terminal closure

**User request: treat BOTH sides of Re(s)=1/2 as source poles.** Correct source is POLES of completed xi LOGARITHMIC DERIVATIVE xi'/xi at reflected original zero pair rho±=1/2±a+iγ (not poles of xi/zeta). Exact original-source pair `m/(w-a)+m/(w+a)=2mw/(w²-a²)` has a mediating ZERO at w=0 (zero of pair contribution, not actual xi/zeta zero), a² recoverable separation residual and Laplace cosh form. Reuse existing Lean `BidiMarkedFourth` original 0/2/4 target/reflection and `signedNormalizedPairKernel`; for original signed even compact witness P_W, `K_W(alpha,q)=[C_W(q+i alpha)+C_W(q-i alpha)]/2` exactly, alpha=a/(t/16). Same-ordinate ±a source contributions have same K; original off-ordinate zero-sum already includes BOTH and its original 1/2 factor. Do not double count reflection-fixed critical zeros, or assume the pair has a sign by symmetry. The full quartet includes ±γ under conjugation, with different far q values.

**New significant same-source A2 local improvement:** existing Lean `RiemannProjectiveQuarticFourWindowSignedPoleLocalRemainderBounds.lean` defines `literalLocalFourthAdverseMassAt` and bounds it by `3/2 * literalLocalFourthAdverseMultiplicityAt`, then `3/2 N(t-3/2,t+3/2)` and `(9/2) A0 log(t+5)`. Original quartic physical phase is EXACTLY `P4=a^4-6a²delta²+delta^4=(delta²-3a²)^2-8a^4`. Since original actual zeros have |a|≤1/2, **stronger exact geometric certificate**:
  `AdverseMass <=8 sum_[original adverse zero rho] mult(rho)*heightOf(rho)^4 <=(1/2)*AdverseMultiplicity <=(1/2)*N(t-3/2,t+3/2) <=(3/2)*A0 log(t+5)`.
This reduces the existing subsidiary adverse ledger by exact factor THREE without changing any zero source, multiplicity, endpoint convention, or used count theorem. Source proof weld to replace the 3/2 kernel-bound is still not kernel-written/tested, per local SymPy-only instruction. Original adverse P4<0 implies **strictly** `(sqrt2-1)|a|<|gamma-t|<(sqrt2+1)|a|`, so its original actual zero count is confined to narrower `|gamma-t|<(1+sqrt2)/2<3/2` physical band. A new length-sensitive original RvM bound could strengthen further; a bare window inclusion cannot conjure a new log constant.

**Original RH q4 far source and 4 complex test-root branches:** atomic source F(z)=-(320/351)sin(pi z/4)^4 gives `F(4+iα)=-(320/351)sinh(piα/4)^4`, and original smooth R→0 response has four simple scaled quartic leading roots `x=(6/pi)m2^(1/4) {±1,±i}`; TWO real roots already fixed-R certified, imaginary root branches only asymptotic so far. At t>=1e14 actual |α|<=8e-14, whereas imaginary-leading notch scale at R=1e-10 is ~1e-5; source physical horizontal displacement cannot automatically be identified with those complex Fourier roots. In q≈4 far bucket actual paired LOG pole separation correction relative to a double-line reference <5/t²<5e-28; source already has sign-changing K in far bands. Crucial full `LiteralFarMinusMuUniformHighEstimate`, full mu/prime/spatial zero distribution, post-sixth local slack remain OPEN; 3fold local improvement is real but NOT a RH proof.

**GRH:** Completed primitive Dirichlet character reflection square is on `(χ,ρ)`: conjugation `C:(χ,ρ)↦(barχ,barρ)`, FE `F:(χ,ρ)↦(barχ,1-ρ)`; they commute and `FC:(χ,ρ)↦(χ,1-barρ)`, giving same-χ ±a pair, but NEGATIVE γ lies on conjugate-character sheet for complex χ. Retain conductor, gamma factor, epsilon, parity and actual χ zero/multiplicity; zeta signed witness is not all-character GRH.

[**Full same-source proof and negative controls**](https://github.com/chboishabba/dashi_agda/blob/research/alpoge-grh-geometry-bridge-20261121/Docs/proofs/RHGRHBilateralCompletedLogPolePairQuarticAdverseMass20261123.md), [**new portable SymPy audit**](https://github.com/chboishabba/dashi_agda/blob/research/alpoge-grh-geometry-bridge-20261121/scripts/check_rh_bilateral_completed_xi_logpoles_20261123.py). Source commit 6001bdb7 / stronger check 73f8a6d1 / proof a0dbb488. Independent local SymPy 1.14 exact tests PASS, no Lean/Agda/CI and no RH/GRH promotion.

---
## 23 November 2026 — P0 actual zero FAR bucket sign weld from source same-object theorem (one step beyond Fourier notches)

Original Lean theorem `QuarticFourSignedPolePair.signedLiteralPairSourceTerm_eq_normalizedPairKernel` directly identifies EACH actual off-ordinate ζ-zero summand with `mult(sigma)/(t/16)^2 * signedNormalizedPairKernel(heightOf/r, (Im sigma-t)/r)`. Thus newly certified fixed-R q-window kernel sign estimates have genuine **original actual-zero consumer**: for R=1e-10, t>=1e14, full positive q-core |q-4|<=sqrtR/2 has per-zero kernel >0.11R²; TWO negative q-shells 99sqrtR/50<=|q-4|<=2sqrtR have kernel <-0.6R², uniformly in real zero horizontal height |a|<=1/2. Finite multiplicity-weighted literal signed sums obey `SUM_core>=(0.11 R²/r²)*N_core`, `SUM_shells<=-(0.6R²/r²)*N_shells`. Exact rational independent source check PASS (script extension commit 35b380e7).

Original `Synthesis/RiemannZetaMuZeroCountOneSided.lean` plus original explicit `quarticSignedPoleMuLowerEnvelope(A)=[log(A/2pi)-20/A²]/(2pi)` gives for any bucket (A,B], above existential source onset, `N(A,B)>=(B-A)*muLower(A)-C*(log(A+3)+log(B+4))`. Physical widths: positive core r*sqrtR =62,500,000 at t=1e14; each negative shell r*sqrtR/50=1,250,000. Since widths ∝t, RvM lower count proves BOTH signs of nonempty actual ζ-zero contributions for all SUFFICIENTLY LARGE t, but unknown source C/T0 means not an explicit N>0 theorem at t=1e14. This does **not** mean ζ zeros at Fourier-response roots or off-line zeros. Both positive and negative actual far contributions exist asymptotically; their combined weighted sign, outer complement, µ center-density/variation and local post-sixth slack remain UNPAID. Need original full `LiteralFarMinusMuUniformHighEstimate` to exclude off-line zeros/RH; GRH requires additionally all-character extension. [Full precise source proof](https://github.com/chboishabba/dashi_agda/blob/research/alpoge-grh-geometry-bridge-20261121/Docs/proofs/RHOriginalFixedRadiusPhysicalNotchA2FarSourceCertificate20261123.md) (commit 8a5598c5). No kernel/CI.

---
## 23 Nov 2026 — P0 exact fixed-R/finite-pole/horizontal q4 notch **CLOSED**, but in signed FAR not LOCAL A2

NEW source-specific proof [full analysis](https://github.com/chboishabba/dashi_agda/blob/research/alpoge-grh-geometry-bridge-20261121/Docs/proofs/RHOriginalFixedRadiusPhysicalNotchA2FarSourceCertificate20261123.md), rational runnable [regression](https://github.com/chboishabba/dashi_agda/blob/research/alpoge-grh-geometry-bridge-20261121/scripts/check_rh_original_bump_fixedR_qwindow_20261123.py) (commits ef054f08, c7b0b007). Local full SymPy source-rederived J2/pole/bump-jet and rational inequalities PASS. No Agda/Lean kernel/CI. This **finishes** the previous conditional fixed-radius q-neighbourhood requirement: for SAME original even compact bump, original lambda=1/2,2/3 selected J2 branches, R=1e-10, ALL t>=1e14 and |a|<=1/2, finite pole alpha=16a/t, the original signed normalized pair kernel satisfies
  K(R,t,a,4±0.5sqrtR) > (11/100)R²,
  K(R,t,a,4±2sqrtR) < -(4/5)R².
The actual source Q(q) has frequencies <=7 throughout, original pole <=18; original root perturbation <=600R4, global jet |E|<23e12R4, and same-source q-uniform physical finite pole/horizontal bound |K(R,t,a,q)-K(R,∞,0,q)|<=5455872/t² for |q-4|<=2sqrtR. The original quartic F(q) and exact first jet K1(4)=120/13, |K1'(4)|<20, |K1''|<16e6 leave uniform total normalized error <0.058. By IVT at least two actual real Fourier-RESPONSE zeros exist, one in each bracket, uniform in t,a. No uniqueness and no actual ζ zeros.

**HIGHEST-ALPHA GEOMETRIC CORRECTION:** the source canonical local cone uses q=(Imρ-t)/(t/16) with |q|<=eta=1/(π+1)<1/4; q≈4 is a FAR-ordinate frequency band at Imρ≈5t/4. Thus this completed q-notch lemma is a NEW *far signed-source* decomposition tool, NOT the local A2 sixth/eighth absorption theorem. The existing Lean literal RH terminal remains `LiteralFarMinusMuUniformHighEstimate`, or equivalently same-W `H_W+S_W<4d_W(rho)+I_W`; its actual zero-multiplicity weighted FarExact, µ integral, RvM discrepancy, prime source and nonnegative local slack remain OPEN. Original `Synthesis/RiemannZetaMuZeroCountOneSided` gives a literal interval-count lower bound `N(A,B)>=∫_A^B µ-C(log(A+3)+log(B+4))` above an existential threshold, but counts do not establish SIGNED weighted far absorption. Do not promote observed Fourier response zeros to actual ζ zeros, phase aliases or RH/GRH. Next proper P0 is signed far sum split into the proven two notch bands PLUS complement, then actual mu and post-sixth strict-margin comparison, using original W only.

---
## 23 Nov 2026 — RH geometric P0: source C3×C4 angular/temporal repair and R>0 sqrt(R) *FOURIER* notch splitting

**More precise Lacan/Irigaray readback (do NOT treat code0 as an SSP zero):** ORIGINAL `LacanFregeTernaryRoleChartExact` uses a directed comparison star `code1→code0,code1→code2` with code1 privileged; original `IrigarayLabialRelationalCarrierExact` uses reciprocal contact `code1↔code2`, code0 CLASSIFICATION REFUSAL. Original `LacanIrigarayTernaryGrammarBridgeExact` already proves 6/6 no relabel. The first symmetrized/recharted grammar is P3; the second is `K2⊔K1` with an isolated neither-position (NOT C3, which would ADD two contacts). Their actual finite wave at π differs: P3 and native C3 give `2J/3-I`, but K2⊔K1 gives I, with source spectra `{0,1,3}` and `{0,0,2}`. Reusing a shared three-label carrier is NOT a relation/consumer identity.

**Original RH Fourier q is REAL.** The atomic original 4-window signed stencil is `B_h=-(20/351)(T+T^-1-2)^2` at original h=π/2; `F(q)=-(320/351)sin^4(πq/4)` and q=4n FOURTH-ORDER observed Fourier notches. Native C3 Fourier character requires INTEGER q mod3. At selected integer restriction, `q=1` and `q=4` collide mod3 but F=-80/351 and0, so original atomic RH **cannot FactorsThrough C3-only**. New SOURCE-WRITTEN Agda `DASHI/Analysis/RHFourWindowAngularC3C4SufficientConsumerExact.agda` uses PREEXISTING Phase4+Residue3 and canonical ConsumerDescentMinimalObserverExact, proves selected negative C3/positive Phase4 factorization, C3×C4 single 12-cycle, indexed original RH.Source4 recovery; no duplicate trit, phase owner or H05 cube. New exact SymPy [full proof](https://github.com/chboishabba/dashi_agda/blob/research/alpoge-grh-geometry-bridge-20261121/Docs/proofs/RHFourWindowC3C4AngularConsumerRealQuarticGeometry20261123.md) verifies the 12×12 original C4 RH operator `-(20/351)(Z³+Z^-³-2)^2` commutes with native C3 Uπ `(2/3)(I+Z⁴+Z^-⁴)-I`; RH rank9/kernel3, time +1 kernel1 and -1 kernel2. q4 RH notch has time phase -1, NOT an analytic zeta zero. INTEGER joint phase `(q%3,q%4)` recovers q%12; **not** a literal 12-dimensional RH spacetime or real-q finite character.

**New global ATOMIC real-q analytic source bound:** set d=dist(q,4Z). Exact sine inequalities give `(20/351)d⁴≤-F(q)≤(5π⁴/1404)d⁴`. Positive q-variable smoothing of F strictly negative off notch, but this is NOT the original finite-R angular bump smoothing.

**Crucial original source-positive radius NON-DESCENT:** existing ORIGINAL `check_rh_original_bump_explicit_radius_20261122.py` certifies high-pole `K_R(0,4)>R²/6` for fixed `R=10^-10` (finite-t selected q4 additionally >11R²/300). The original same selected normalized projective high-pole q=0 response vanishes IDENTICALLY `K_R(0,0)=0`; both q=0 and4 map to same four-phase class φ0 and atomic F=0. Thus even original **C4-only** angular phase is NOT `FactorsThrough` the positive-radius source. Winding/frequency, original bump moment/R/t/a/branch and H05 source history MUST remain as a consumer-specific residual. A putative uniform `|K_R-F|<C d⁴` near q4 is REFUTED at q4 itself.

**New actual smooth HIGH-POLE Fourier boundary-layer theorem:** use original J2 selected roots, even normalized bump `e=E[Y²]/2=(m2/2)R²`, `1/24≤m2≤1` and source Fourier Taylor remainder. `K_R(4+x√R)/R²→(60m2/13)-(5π⁴/1404)x⁴`, uniformly x compact. IFT gives actual original-smooth high-pole RESPONSE zeros
`q±(R)=4±(6/π)m2^(1/4)√R+o(√R)`.
Universal sufficiently-small-R bracket `K_R(4±(1/2)√R)>0`, `K_R(4±2√R)<0`, by rational π bounds and original bump m2. These are Fourier RESPONSE notches, **NOT ζ zeros**; proof is exact source math with local SymPy acceptance, not Lean kernel, and fixed R/t OUTWARD sign not yet certified. Original positive radial source remains intact. The precise physical next lemma is a source-uniform q-window finite-t pole/horizontal transfer with the nonzero R² lower-jet residual, NOT a blind quartic sign weld.

**P0 strict gate UNCHANGED:** original Lean paid `D_A(ΔM0,ΔM2,ΔM4)`, RvM V4/left atom, signed M6, eighth debt; unpaid actual `LocalPositiveDebt+FarExact < CompensationThreshold+MuGain`, RH/GRH and all original analytic cube faces. Preserve eight H05 vertices, twelve arrows, six faces, k/time/Frobenius/history/Sign/Residual/multiplicity, finite-q C3/C4 vs real-q circle phase. Scripts `check_rh_angular_c3_c4_grammar_mixed_consumer_20261123.py`, `check_rh_atomic_real_angle_quartic_coercivity_20261123.py`, `check_rh_original_bump_q4_sqrtR_boundary_layer_20261123.py` plus original source bump; source-written Agda pending compiler, local SymPy exact passed.

---

## 23 Nov 2026 — P0 actual temporal/signed-consumer cross-source bridge (verified finite, original RH signed terminal still OPEN)

**NEW exact original temporal operator:** Original P3 hypervoxel `check_hyperfabric_path27_quantum_walk.py` has `U_P3(pi)=2J/3-I=U_C3(pi)` despite DIFFERENT P3/C3 Laplacians. Tensoring on original full T9 hyperfabric gives one true same-source finite `U_P3^9(pi)=U_C3^9(pi)=(2J/3-I)^tensor9`, character multiplier `(-1)^support(q)`. This is a selected time (t∈πZ) equality, NOT all continuous time nor a physically moving graph. Under Griess Singer `G`, `U_k=P_G^k U_0 P_G^-k`; the fixed-graph defect `[P_G,U_0]` rank20 with rational entry 2/9 remains nonzero. Source-signed dual chart transports all 512 original corner/periodic full-support Fourier labels for all 26 k with true inverse and orientation; U9(pi) centre→corner amplitude exactly 512/19683. The ternary source + k is retained: two q with same binary support (1,1,0),(1,-1,0) have distinct k1 eigenphase. Original 13-axis/source history not erased.

**RH finite operator CONSUMER:** original atomic negative biharmonic Laurent polynomial `-(20/351)(T+T^-1-2)^2` evaluates on original C3 shift to `-(20/39)(I-J/3)`, commutes with selected Uπ and native sign reflections. This is an exact *representation of the same polynomial*, NOT equality of original RH q=4 Fourier zero with a C3 character/actual ζ zero. Actual zero/µ/FarExact/compensation and `H_n+E_n+S_W<T_W(rho)` still OPEN.

**New cross-programme finite YM bridge:** original R445 16 site×4 dir×2 half selected link count =128 has an exact signed 2-step path into T9; source midpoint odd sites 1 and3 are TWO separate gauge fibres over the same projected zero. 64 original odd midpoint sites→32 projected nodes, 32 independent residual pairs; SU2 Q8 noncommutative ordered Wilson products and gauge covariance checked on all 64 coarse links. Original `YMClayNativeSideFourTwoLinkPairSameObjectExact` ALREADY proves full SU(N) selected ordered two-link block product and the same weighted Gibbs blocked-link identity. Do not reconstruct it. Full Haar/spectators/plaquettes remain OPEN.

**New original NS R529/530 FactorsThrough:** source already maps Z³ integer modes to same signed ternary voxel and periodic T9 triad. Sign quotient suffices for selected finite Uπ support-phase, but **not** original dyadic h3: same sign for frequencies 8 and9, multipliers 1 vs7/8. Even (sign,h3) fails convolution for 7 vs10. `DASHI/Analysis/RHHyperfabricNSDyadicSelectedConsumerNonDescentExact.agda` source-writes positive/negative original ConsumerDescent results, kernel pending. Unresolved trit, signed antipode, actual phase and binary support not conflated; original Lacan/Irigaray grammar remains a separate semantic relation.

**Source/acceptance:** [detailed exact proof and original provenance](https://github.com/chboishabba/dashi_agda/blob/research/alpoge-grh-geometry-bridge-20261121/Docs/proofs/RHNSYMHyperfabricOriginalTemporalSufficientConsumerSubdivision20261123.md); scripts `check_hyperfabric_original_stroboscopic_P3_C3_RH_YM_NS_20261123.py`, `check_hyperfabric_9d_source_walk_signed_corner_fourier_20261123.py`, `check_ym_r445_hyperfabric_signed_midpoint_gauge_fibre_20261123.py`, `check_rh_ns_ym_original_temporal_sufficient_consumer_20261123.py`. Independent local exact SymPy/rational and finite source-equivalent checks PASS, committed files source-readback only, Agda/Lean kernels and CI not run. No RH/GRH, NS, YM physical Clay promotion.

---

## 23 November 2026 — SOURCE CORRECTION / nine-coordinate Fourier-shell addendum (RH P0)

The first new RH `check_rh_hyperfabric_k_time_spatial_intertwiner_20261123.py` used a shifted residue path `0–1–2` while applying F3³ addition with zero as group origin. **That graph labelling is NOT the native balanced SSP original `-1↔0↔+1` with centre zero.** Count equality does not establish source-geometry identity. The committed script was REPAIRED (RH commits `c276ef63`, `bc0846fd`) to enumerate and act on actual `(-1,0,+1)^3` and `(-1,0,+1)^9`, map `GF3` back to balanced labels, and treat antipode as literal global `x↦-x`. Source-equivalent local corrections pass native 54/81 spatial edges, 729 dual Fourier character pairs, and ALL 118,098 P3^9 source-edge inverse checks. Fixed-graph Singer no-go remains; true indexed-transport intertwiner remains valid.

New FULL periodic nine-coordinate Fourier shell ledger: support-size r in 0..9 has multiplicity `C(9,r)*2^r`, namely
`(1,18,144,672,2016,4032,5376,4608,2304,512)`, summing to 19,683. Maximal-support 512=8³ derives from the **three** native C3³ eight-mode strata. This is the distinct periodic C3^9 torus (177,147 edges), not nonwrapping P3^9 (118,098 edges), nor NS dyadic 1/128 / YM 16×8=128. Exact script updated `724c397e`, newline repaired `7d8c85ce`; detailed [source correction and spectrum](https://github.com/chboishabba/dashi_agda/blob/research/alpoge-grh-geometry-bridge-20261121/Docs/proofs/RHHyperfabricKTimeSpatialFourierIntertwinerAudit20261123.md), ledger `9707ab74`.

**Keep TIME t distinct from refinement k, Fourier wavevector q and H05 Frobenius/consumer history**. Chart-conjugation cannot erase a nonzero `D_(t,k)`. The new Agda is source-written without kernel, the corrected script is read back but no byte-for-byte CI/Agda execution. Original RH signed FarExact/μ/slack, NS continuum and YM mass-gap endpoints remain open. Do not duplicate existing B3 spatial/Fourier intertwiner.

---

## 23 November 2026 — P0 CORRECTION: existing spatial/Fourier intertwiner, real k/time-indexed nine-coordinate hyperfabric

**Source read:** the ORIGINAL `Base369Ternary27SignedSymmetryMonsterIntertwinerExact` + `Base369Ternary27CharacterAdjacencyEquivarianceExact` already prove native P3³ coordinate-reflection adjacency and C3-character `k↔-k` covariance. `TOE369CoarseFineIntertwinerMaxCutExact` also already owns a coarse/fine normalization and distinct phase relation, but DOES NOT prove the source's future RH FarExact intertwiner. Our earlier statement “repo lacks an intertwiner” was too broad: the *specific missing* intertwiner is **original actual ζ-zero/μ/FarExact under the selected source**. Keep this distinction.

**Correct 9D spatial graph + k/time:** original `Base369Ternary27HypervoxelFabricGeometryExact` supplies `TernaryHyperformalPoint=(P3³)^3` = 27³=19,683, with 3×54×729=118,098 nonperiodic edges. Original `Base369PeriodicTernaryTorusPathRestrictionBidiExact` separately supplies periodic C3^9 on SAME nine-trit carrier with 3×81×729=177,147 edges. A Griess Singer (G=-M) moves all 54/54 original P3³ edges and all 81/81 original C3³ torus edges off those **fixed** graphs, but the EXACT source-chart transported Laplacian `L_k=P_G^k L_0 P_G^{-k}` obeys `P_G L_k=L_(k+1) P_G`. A local 27×27 rational exact test shows the original fixed-path commutator has rank 24, so fixed and transported equivariance must not be conflated. Native full 118,098 spatial source edges were exhaustively reindexed and inverted in local source-equivalent Python. Original periodic C3³ Fourier dual mode transport `q→G^{-T}q` obeys 729/729 `chi_(G^-T q)(Gx)=chi_q(x)`; periodic torus Fourier eigenvalue `3×nonzeroCoordinateCount(q)` has multiplicities 1,6,12,8, with **8** highest-support characters. The P3³ path Laplacian is NOT diagonal in these C3³ characters.

**New RH PR #1533 source artefacts:** `scripts/check_rh_hyperfabric_k_time_spatial_intertwiner_20261123.py` (commits `af2ba256`, `53a8c30b`; exact finite-equivalent local checks, but committed file not independently executed), and `DASHI/Analysis/RHHyperfabricKTimeTransportedSpatialIntertwinerExact.agda` (commit `aa496c4a`; written only, no Agda kernel), plus [full indexed proof ledger](https://github.com/chboishabba/dashi_agda/blob/research/alpoge-grh-geometry-bridge-20261121/Docs/proofs/RHHyperfabricKTimeSpatialFourierIntertwinerAudit20261123.md) (`6426d7df`). New Agda uses actual original P3^9 and torus edge TYPES with retained underlying source-edge witness at every refinement k, and a DISTINCT physical Time parameter and source/history/version/sign/residual/mode/observedZero. It does not manufacture time dynamics from k.

**Precise k/time square:** with true source time (T_{t,k}) and refinement (R_{t,k}), `D=R_(t+1,k) T_(t,k)-T_(t,k+1) R_(t,k)`; under invertible chart (P_{t,k}), `D' = P_(t+1,k+1) D P_(t,k)^{-1}`. Therefore a nonzero physical defect CANNOT be erased by chart choice. The finite exact time/space model `U_(t,k)=I-alpha_t L_k` with 2 sample independent t values is a **model fixture**, NOT an actual zeta/NS/YM time evolution or RH consumer. Actual source-specific analytical intertwiners and strict signed zero estimates remain OPEN.

**8/128/16 flag resolved by source, not just cardinality:** NS periodic finite carrier has shell radius R=8, rational hat gain 1/128 from 2^-(R-1), and 8=(2 placements×2 Bony×2 Bernstein), giving 8/128=1/16. This is genuine source dyadic multiplier scaling, not a full NS operator theorem. Separately YM original side-four→side-two 4D block has 16 coarse sites, 4 dirs×2 selected links/site=8, total 16×8=128 selected links (64 coarse, 896 residual of 1024). H05 has 8 vertices, and periodic C3³ has 8 highest-shell modes. Preserve these as distinct typed source patterns until an ACTUAL intertwinining map relates them; no arbitrary 8/128/16 identification.

**Unpaid original RH P0:** construct/consume a truly source-defined (not chart-fiat) k/time zero-side transport preserving actual ζ zeros and multiplicities, sign, `Zeta23.mu` background, FarExact, target defect and local slack. The original post-sixth `H_n+E_n+S_W<T_W(rho)` is still OPEN; no RH/GRH, Agda/Lean kernel, native physical 9DOF action or six analytic commuting-face claim. Preserve original witness θ=π/3.

---

## 23 November 2026 — RH P0 hyperfabric C26 SIGN/RESIDUAL-PRESERVING, nonidentity H05 cube (new exact finite source cut)

**Source-first R2/G3 discovery:** the original C26 actor on **the same native 27-point ternary hyperfabric**, no new toy carrier. Canonical owners original `BalancedTernaryAntipodalOrbitExact`, `BalancedTernaryAntipodalResidualCodecExact`, `HyperfabricPunctured27Projective13OrientationExact` (Agda #1249), original Griess/Sah grade shears (Agda `Griess1990MoufangCoherentSL3SectionSourceExact` / Lean #52), original RH traced four-window `RHFourWindowBiharmonicFiniteCubeExact`, original TOE H05 `GovernedIndexedResidualCubeExact` (#1291). New RH #1533 additions: `DASHI/Analysis/RHFourWindowC26NativeHyperfabricSquareExact.agda` (source-written, no Agda kernel), `scripts/check_rh_c26_native_signed_h05_nonidentity_square_20261123.py` (local source-equivalent exact SymPy + exhaustive 26 state tests), `Docs/proofs/RHHyperfabricC26NonidentityCommutingSquare20261123.md` (full source/provenance and no-go).

**Strong positive finite geometry:** original grade `M(x,y,z)=(x+y,y+z,x+y+z) mod3`, `G=-M`, native code `F3³\\{0} ↔ Axis13×Bool`; `Ghat=encode ∘ G ∘ decode` yields TRUE commuting square and invertible source trace. Canonical first-nonzero-positive representative produces NONTRIVIAL 1-cocycle `omega(a)`: **4/13** axes have M orientation-flip, nine do not; `Ghat(a,e)=(Mbar a,e XOR omega(a) XOR 1)`. `Ghat^13` flips orientation and `Ghat^26=id`. The native original G matrix over F3 has irreducible polynomial `X³-X+1`; cyclic basis `[e1,G e1,G² e1]` has determinant1 mod3, so G is a primitive **GF27× Singer C26 cycle** and projective quotient is C13, with exact sequence `1→F3×~C2→F27×~C26→PG(2,3) Singer C13→1`. The field multiplication is a representation of original **grade labels**, not original native spatial edge action.

**H05 concrete NONIDENTITY six-face instance:** x/y trace the original RH four-site→folded→five-point source (including nonzero π/3 cancellation); z acts by original C26 on Code26, identity on full raw RH source. Two genuine x/y faces + four naturality faces; 8 vertices, 12 arrows, six face witnesses and Q.xyz-zyx. Recoverable raw Source4 and separate metadata `Index (History Time Refinement Frob Version)`, independent RH Sign/Residual/Mode/Observation, and C2 orientation Bool. The rational 26-dimensional grade permutation has complementary **13 even + 13 odd** antipodal eigenspaces `E=(I+A)/2,O=(I-A)/2`; both sectors kept. Independently run local source-equivalent checks PASS 26/26 code/source, 156/156 face equations, 26×26 rational parity algebra, 54/54 original graph edge NON-equivariance. The newly committed exact GitHub script was read back but NOT itself run in a compiler/CI environment.

**P0 strict nonpromotion:** This z action is nonidentity on the grade fibre but identity on the original RH W, so the cube is a product/naturality theorem, NOT covariance of actual ζ-zero, μ, or signed FarExact. The native grade G maps ALL original P3³ nearest-neighbour edges to NONedges; no 9DOF metric or original spatial Laplacian intertwiner. Naive original RH theta=π/13 replacement is already proven to lose positive-pole and strength margin across [1/2,2/3]; retaining the old θ=π/3 witness and adding source-traced C26 as **extra indexed fibre** is the safe construction. To help terminal `H_n+E_n+S_W<T_W(rho)`, one must now produce an actual source equivariant signed far/μ/zero measure and a strict bound in BOTH even and odd sectors including local slack. No RH/GRH, Lean/Agda kernel or all-six physical analytic face certification.

**2600 attribution check:** literal repo 2600 is present in unrelated NS sweep settings and economic CoreWeave DDTL3 observations. Arithmetic `2600=13×200=26×100` is not yet an RH/hyperfabric invariant or Singer cycle length; do NOT assign proof authority to that coincidence. Preserve all original source attribution and no ESD edits.

---

## 23 November 2026 — P0 original 4-window VARIABLE-ANGLE theorem, 27→13 C26 phase, and strict pi/13 witness no-go

**New original-source exact mathematical cut** [full proof and provenance](https://github.com/chboishabba/dashi_agda/blob/research/alpoge-grh-geometry-bridge-20261121/Docs/proofs/RHQuarticGeneralAngleC13C26SourceCut20261123.md), [portable SymPy/27-state regression](https://github.com/chboishabba/dashi_agda/blob/research/alpoge-grh-geometry-bridge-20261121/scripts/check_rh_c13_c26_angle_stencil_20261123.py) (commits `56fd7db5`, `934288f1`, `e7a059a8`; SOURCE WRITTEN, no native kernel). Source owners ORIGINAL Lean RiemannProjectiveQuarticFourWindowAtomic/PoleSameObject/SignedPoleTarget and original native C2 27→13 signed codec Agda #1249 / Griess C13 grade actor Lean #52. Do NOT rebuild native 27/13 carriers.

For ANY substitute fourth centre theta (keeping original 0,pi/2,pi, the raw weights 1,-1,lambda,mu, and pole frequency16), let `z=cos(theta),b=cos(2theta),p=cos(16theta)`. The **original pole determinant equals a scalar multiple of the raw theta-site projective mass**: `Ptheta=(1-p)*(z*A2-b*A1)=(1-p)*Qtheta/4`. Thus the original TWO-ENDPOINT POLE WEDGE cancels theta-site exactly `Ptwo*QthetaHalf-Phalf*QthetaTwo=0` independently of J2 and of theta. If both endpoints solve original atomic J2=0, zeroth/second moment null forces the three unchanged centres' mass ratio `(-3,+4,-1)`, so `Ftheta(q)=-2*Ctheta*(1-cos(pi*q/2))²`. **Biharmonic source shape and C4 Fourier notches survive the angle substitution**; the spacing is still h=pi/2, NOT pi/13 or a new C13-equivariant spatial operator. This source projective *rank-one Pluecker cancellation* is stronger than old special-value cos(pi/3) arithmetic.

**Interpretation of the 13:** native 27=1+2*13 under actual C2 antipode, one centre +13 axes with sign residual and 14 C2 orbit classes. The original source-correct Griess C13 actor M on F3³ has 2 genuine 13-cycles on 26 signed grades. Combining M with antipode gives **one C26 cycle**, G^13=antipode, G^26=identity; the abstract C26 character one-step phase is pi/13 while C13 projective-axis step is 2pi/13. This is NOT the original angular cofactor 13=3²+2² by source identity. The true actor sends **54/54 native P3³ nearest-neighbour edges to NONEDGES**; pi/2 is 13/2 steps of pi/13, so the original four-source support is not an integer C26 orbit. No native graph Laplacian/H05 nine-DOF/RH spectral interchange follows.

**P0 negative control over ENTIRE original coefficient corridor:** for theta=pi/13 and every lambda∈[1/2,2/3], exact rational cos(pi/13) and source J2 root bounds give `-1/10<mu0<0, A1>0, A2<0, Ptheta<0`. The original selected pole-positivity corridor was positive, and the reconfigured target strength is only `S≈0.038775` versus required old original floor `7*pi^4/1600≈0.426165`. Thus **naive pi/13 substitution cannot reuse the original positive-W witness, fixed-radius certificate, or A2 strict terminal**, even though Ctheta>0 and the negative-square Fourier symbol survives. To obtain C13-invariant RH improvement, either PROVE a source-specific independent sign/strength redesign with changed centres/pole and transport, or (preferred) attach the native 13-axis class+orientation as an EXTRA indexed fibre to the original intact pi/3 witness. The latter is only a candidate consumer, no actual ζ-zero/higher Fourier A2 estimate.

H05 8 vertices/12 maps/SIX analytic faces, real source time/history/refinement/Frobenius/consumer, scalar-zero/C3 phase/observed-zero/true analytic ζ zeros, original signed FarExact/μ/local slack and `H_n+E_n+S_W<T_W(rho)` remain separate and OPEN. No RH/GRH or Agda/Lean kernel acceptance.

---

## 23 November 2026 — RH P0/P1 × Bishop fast-π × native H05 *provenance-preserving* finite cube

**New source files, same RH PR #1533 / master target:** `DASHI/Analysis/RHFourWindowBiharmonicFiniteCubeExact.agda` (source-written; NO Agda compiler/kernel); `scripts/check_rh_bishop_pi_biharmonic_h05_square_20261123.py` (local SymPy/rational checks); detailed `Docs/proofs/RHFourWindowBishopPiNineDOFCommutingSquare20261123.md` (commit `7f56c611`). To satisfy a real cross-PR import, canonical `DASHI/Core/GovernedIndexedResidualCubeExact.agda` from H05 TOE PR #1291 was ported **byte-identically** to RH PR #1533 (SHA `42b70ebb7376813076934f2245ce6011b76f10c8`; commit `ee790289`), not recreated. This is source-owner reuse, not H14 kernel acceptance.

**Exact algebraic novelty:** original `(-40/117,0,160/351,-40/351)=(40/351)(-3,0,4,-1)`, raw pi/3 cancellation retains two nonzero originals `8*3=9*(8/3)=24`. Symmetric unfold `(-1,4,-6,4,-1)` with global factor `20/351` gives negative centered discrete biharmonic `B_h=-(20/351)(T+T^{-1}-2)^2=-(20/351)T^{-2}(T-1)^4`, hence exact `F_h(q)=-(320/351)sin(hq/2)^4` for any genuine angular spacing h. **9=3², 4=2², 13=9+4**; interpreting 13 as Gaussian norm of 3+2i is optional algebra, not yet a sourced RH 9DOF metric theorem.

**H05 genuine commuting object:** source-written `finiteH05Cube` is the *original* 8-vertex/12-edge/6-face type with two repeated projection/unfolding faces and four explicit identity-z naturality faces; the z-axis is NOT a physical time/smoothing/pole step. `TracedFold`/`TracedFive` preserve and recover original four-site source; the lossy projection alone has a counterexample: raw sources with scaled (24,24) vs (48,48) give the same folded observer. Index specialization uses the ORIGINAL `Q.Index History Time Refinement Frobenius Version` alongside separate sign, residual, mode, observed zero. These FIVE context indices are not the intrinsic geometric 9DOF Route A/B/C fibre. Unpaid: real nonidentity index transport, all real H07 marks/overlaps, H14 native kernel and all analytic six-face RH identifications.

**Bishop π exact rational alignment:** `BishopMachinPiRationalWindowExact.agda` (pi PR #1529) source bracket `281476/89625 < pi_B < 589067/187500` yields `p*=93841671/29875000`, `δ*=49013/89625000`. At rational h*=p*/2, `F_{h*}(4)=-(320/351)sin(p*)^4`; **conditional on a true source/semantic bridge** `pi_B=Lean.Real.pi`, its fourth-order notch error is `<= (320/351)δ*^4 <8.16e-14`. Pi's existing cross-prover `BishopMachinPiLeanSemanticReceiptExact.agda` has all three kernel/serialized witness flags **false**. Fast binary splitting helps evaluate the same constructive π; no π→RH source equality or analytic zero theorem is smuggled in.

**P0 priority unchanged:** selected positive-radius finite-t, actual ζ-zero same-source multiplicity/localized μ/far, source-specific signed post-sixth slack and `H_n+E_n+S_W<T_W(rho)` OPEN. This finite atomic Fourier notch does not identify an actual ζ-zero and does NOT pay A2's FarExact/compensation inequality. No RH/GRH, Lean/Agda kernel or full analytic cube claim. Maintain attribution to original Lean quartic source, H05 #1291, Bishop fast π #1529 and original historical Machin/Bishop work.

---

## 22 November 2026 — P0 FOUR-WINDOW BIHARMONIC STENCIL & coefficient provenance (new exact atomic geometry)

Exact original-source geometry audit / local SymPy: `scripts/check_rh_a2_biharmonic_stencil_geometry_20261122.py` (commit `602b2c42`). Detailed source-by-source proof: `Docs/proofs/RHA2AtomicBiharmonicStencilCoefficientAnatomy20261122.md` (commit `efb3d5fc`). Lean owners: `RiemannProjectiveQuarticFourWindowAtomic`, `PoleSameObject`, `SignedPoleTarget`, `SignedPoleEighthRemainder`, `SignedPolePostSixthAbsorb`, and `SignedPoleA2ScalarAudit`. No Lean/Agda kernel receipt.

**Unexpected exact geometry at original atomic high-pole vertex:** selected signed projective atomic profile at `c=(0,pi/3,pi/2,pi)`:
```text
(-40/117, 0, 160/351, -40/351)
  = (40/351)*(-3,0,4,-1).
```
The pi/3 column is an **observed determinant cancellation** `1*3-(9/8)*(8/3)=0` between two NONZERO source profiles, not an empty source or ζ(s) zero. Folding symmetric ±π/2 and ±π atoms produces the **negative five-point biharmonic stencil** `(20/351)*(-1,4,-6,4,-1)` on `(-π,-π/2,0,π/2,π)`. Its entire atomic high-pole real Fourier response factors EXACTLY:
```text
F(q) = -(80/351)*(1-cos(pi*q/2))²
     = -(320/351)*sin(pi*q/4)^4 <= 0.
```
It has **fourth-order spectral notches** precisely at `q∈4ℤ`. Thus the original q4 `-5*pi^4*z^4*u^4/1404` boundary coefficient and q1 negative `-80/351` are the SAME biharmonic source, not unrelated accidents. These notches are Fourier observations, NEVER ζ-zero statements. This exact factorization is for the atomic/high-pole vertex only; smooth and finite-pole maps in the 8-vertex/12-map/6-face indexed cube remain separate analytic debts.

**Number classification rather than mystification:** `13/72=1/8+1/18` is the actual J2 projective cofactor of the π/3 and π/2 squared/angular cosine sample; `117=3²*13`, `351=3³*13` are COMPOSITE endpoint/elimination denominators (not primes). Ratios `-3:0:4:-1`, quartic notch order and zero-column cancellation are structural; absolute `40/351` is normalization dependent. The A2 asymptotic bracket `-S/15+π^6η²/2400+Lη²/8500` has `15=6*5/2` from quartic integration, `2400=720*20/(3*2)` from M6 cap, 6! and two-sided count, `8500=17000/2` from a CONSERVATIVE eighth envelope and two-sided count. `160=2400/15`; `15/8500=3/1700`. Source `1/17000` was relaxed from an intermediate `1/17920`, so 17 in 1700/8500 is not a hidden invariant. The 15 inside `Re(a+iδ)^6` is separately binomial `C(6,2)`, not the denominator 15.

**Original A2 P0 unchanged:** the finite-`R,t` selected witness, exact signed `FarExact`, compensation threshold, actual-zero multiplicities, local slack, and `H_n+E_n+S_W<T_W(rho)` remain OPEN. Preserve scalar-zero vs Fourier-zero vs balanced nonempty phase cancellation and independent source histories. Do not treat this C4-period spectral notch as proof of an inherited C3/369 map.

---

## 22 November 2026 — NEW A2 atomic high-pole local SIGN PASS; full signed far/threshold CUT still open

Source-first audit of merged Lean PR #22
(`Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleA2ScalarAudit.lean`,
`...PostSixthAbsorb.lean`, `...V4EndpointAbsorb.lean`,
`...ConeDecomposition.lean`, `...SignedPolePair.lean`)
gives one nonduplicate quantitative reduction:

For `v=t/16`, `eta=1/(pi+1)`,
`ell=log(t)/(2pi)`, `r=eta*v`, the original
actual expanded RvM count has leading `NZ=2*r*ell+O(log t)`.
With `S=W.targetStrength`, `L=W.fourthLipschitz`,
and a fixed/uniformly controlled selected witness family,
the original A2 local budget has leading
```text
LocalPositiveDebt - MuGain
  = eta^5*ell/v * [-S/15 + pi^6*eta²/2400 + L*eta²/8500]
  + lower order;
negative-leading local criterion:
  S > pi^6*eta²/160 + 3*eta²*L/1700.
```
V4 RvM error and quartic r²-count correction are strictly
lower order. The original floor `S>=7pi^4/1600` alone
does **not** bound L or pay the bracket.

New original high-pole ATOMIC exact local SymPy regression
`scripts/check_rh_a2_atomic_high_pole_sign_20261122.py`,
commit `5453c8f9` and full BIDI audit `d7511e9b`:
original same-pole signed profile mass at
`(0,pi/3,pi/2,pi)` is
`(-40/117,0,160/351,-40/351)`. Therefore
```text
S_atom=5*pi^4/234 ~=2.081391;
M6_atom=-25*pi^6/234 ~= -102.713;
L_atom=5*pi^5*(cosh(pi/2)+8cosh(pi))/351 ~=415.196;
local A2 bracket C_atom~= -0.112558;
rigorously C_atom < -1/20 via exact rational bounds.
```
The ORIGINAL atom satisfies the selected strength floor
and M6 cap. This is a genuine **favorable atomic high-pole
leading local sign**, not a smooth R>0 theorem about all t
or the actual zero carrier. R/t source-continuity must keep
the SAME selected signed pole coefficients, J2 roots,
strength floor, signed M6 bound, fourthLipschitz norm,
and quantitative horizontal target radius.

The already-owned far absolute shell
`farShellBound A t J=18A log(t+4)/J+72A/sqrt(J)`,
canonical `J=floor(t/2000)`, retains an O(t^-1/2)
MAJORANT component against a local O(log(t)/t) balance.
This is NOT a lower bound on actual signed FarExact.
The exact outstanding high-zero A2 condition remains
```text
FarExact - compensationTargetThreshold(rho)
  < MuGain - LocalPositiveDebt
```
where `compensationTargetThreshold(rho)
=4*combinedZeroHeightDefect(rho)
+ integral signedOrdinateTest*Zeta23.mu` retains
the crucial local slack and smooth integral. The next
P0 bite is the SAME-SELECTED-WITNESS quantitative R/t
margin plus this literal signed far-vs-threshold payment
(or rigorous no-go for that selected route), not another
operator/zero model or q=4-only positive lobe.

Preserve 8 vertices / 12 signed maps / 6 indexed faces,
source-vs-observer zeros, actual multiplicity,
SameOrd(t) exclusion, half-open boundary left atom,
physical-normalized ordinate chart, balanced ternary
sign and far residual. The RH/GRH terminal
`H_n+E_n+S_W<T_W(rho)` remains OPEN; no Lean/Agda
kernel or GitHub CI acceptance.

---

## 22 November 2026 — P0 priority correction after merged Lean A2 source audit

**Do not rebuild a localized M0/M2/M4 producer as the first A2 task.** The merged [Lean PR #22](https://github.com/chboishabba/dashi_lean4/pull/22) is available on `main`. Original source owners re-read:
`Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleBidiMarkedFourth.lean` (exact same-object zero-minus-mu BIDI moment operator),
`...SignedPoleRvMFourth.lean` (existing actual ordinate-only V4 Abel/RvM discrepancy estimate),
`...SignedPoleV4EndpointAbsorb.lean` (closed local interval versus half-open RvM interval, including the possible LEFT-ENDPOINT ZERO ATOM, not silently dropped),
`...SignedPolePostSixthAbsorb.lean` (complete quartic, signed sixth, eighth debt, signed literal FarExact),
and `...SignedPoleA2ScalarAudit.lean` (exact strict scalar).

The EXACT remaining A2 scalar equivalence, no abs(FarExact), is:

`postSixthTerminalLocalPositiveDebt(EV) + literalFarExactAt(eta0,n) < compensationTargetThreshold(rho) + postSixthTerminalLocalMuGain`,

with `eta0=1/(pi+1)`, `r=eta0*t/16`, and actual expanded multiplicity count `NZ=N(t-r-1,t+r)`. Its source local positive debt includes (1) `S/(6(t/16)^6)*(EV+(3/2)r²NZ)`, (2) signed M6 cap `(3pi^6/20)*sixthEnvelope*NZ/(720(t/16)^8)`, (3) G1-fourth-Lipschitz eighth envelope `(pi+1)^2*W.fourthLipschitz*eighthEnvelope*NZ/(t/16)^10`. Its favorable mu gain is `S/(6(t/16)^6)*(2/5)r^5*muLower(t-r)`; source proves `muGain>0` and dominant selected M6 coefficient paid for t>=200. **Only a TRUE strict overall comparison including signed FarExact and compensation remains unpaid**.

The new reflected-cloud M0/M2 no-go `93198e65` is a source-geometry test forbidding count-only fourth-sign promotion, NOT a counterexample to this RvM-using A2 theorem. The A2 front can employ already-paid V4/H4 and sixth/eighth bounds directly; a separate stronger localized marked-pair estimate is an optional alternative only if it improves this exact scalar. Preserve the original left atom, SameOrd exclusion, actual Zeros multiplicities, signed far, and local slack. Do not switch to q=4 synthetic positivity as a proof of a universal signed zero sum. Indexed cube remains 8 vertices/12 maps/6 faces with proof-relevant history/sign/zero semantics.

**Next research action:** audit the source magnitude/sign of the one A2 inequality, especially NZ, eighth debt and signed FarExact versus the actual compensation threshold and smooth mu gain; derive a source-backed strict inequality or a rigorous asymptotic no-go, not another scalar wrapper. Actual `H_n+E_n+S_W<T_W(rho)` and RH/GRH remain open; no Lean/Agda kernel receipt from this work.

---

## 22 November 2026 — P0 ACTUAL zero-marked fourth max-cut (source owner already paid)

Source-first audit of Lean main `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleBidiMarkedFourth.lean` and Agda `DASHI/Analysis/RiemannQuarticSignedPoleBidiMarkedFourthExact.agda`: original `literalLocalCenteredFourthAngularAt_eq_bidi_discrepancy` is an EXACT source-owned local zero-minus-`Zeta23.mu` 0/2/4 BIDI identity. The zero sum uses the real `centeredZeroFinset`, actual multiplicity and `SameOrd t` exclusion. `localizedBidiMarkedProducer_exact` is only a trivial packaging of the already-defined three moments; it is NOT the missing one-centre analytic marked-pair theorem. The specific short-support cosh-marked literal prime channel is already recorded source-paid as zero. The remaining full signed response/archimedean and far/slack payment is not thereby proved.

New local SymPy regression `scripts/check_rh_marked_fourth_reflected_cloud_obstruction_20261122.py` (commit `93198e65`) constructs two strictly off-ordinate **synthetic** reflection-complete clouds (no actual ζ-zero claim). Both have identical positive integer mass `M0=4`, vertical `M2=100h²` and marked `M2=-100h²`. Source `D_A=1/2 M4 -3 A² M2 +5 A⁴ M0` yields opposite local *zero* fourth-angular signs: `-4375h⁴/4` versus `+4841h⁴/4`, with exact marked M4 difference `4608h⁴`. This improves the previous unreflected M0/M2 negative controls: reflection, positivity, local support, and SameOrd exclusion still cannot certify the required fourth-moment sign. A shared smooth `mu` background preserves the difference but may shift BOTH centred signs.

Sharp local positive-measure cone: for `V0>0`, `|δ|<=L`, `V2²/V0<=V4<=L²V2`. In a constant-|a|=A subfamily, fourth-angular sum lies in `[V2²/V0-6A²V2+A⁴V0, L²V2-6A²V2+A⁴V0]`; this band crosses zero on the two clouds. For full physical strip `|a|<=1/2`, `-8L²V2<=Σ mult*P4<=L²V2+V0/16` is a universal bound, but not a strict RH payment.

**Exact new execution target (not more low-moment algebra)**: derive the genuine ACTUAL-zero localized marked fourth correction `ΔM4` relative to original `ΔM0,ΔM2` and `Zeta23.mu`. If the required local lower angular charge is `D_A(Δ)>B`, the exact reverse target is `ΔM4 > 2B+6A²ΔM2-10A⁴ΔM0` (inequality reversed for an upper charge). Couple the actual finite zero source to the merged Lean #22 A2 strict scalar `localPositiveDebt+signed FarExact < compensationTargetThreshold+localMuGain`, keeping full sign/multiplicity and local slack. A2 remains OPEN, as does `H_n+E_n+S_W<T_W(rho)`. No RH/GRH or Lean/Agda kernel claim.

**Geometry/attribution**: preserve eight vertices, twelve maps, six faces with reflection/smoothing/pole axes, time/history/refinement/Frobenius/consumer, balanced ternary sign, actual-Zeros target vs excluded off-ordinate distinction, full far source and separate scalar-zero/exponent-zero-C3/Fourier-zero semantics. This is a finite **nonpromotion test** and mathematical moment cone; it is not an analytic commuting-cube theorem or a zero distribution theorem. Full details and exact provenance in `Docs/proofs/RHR2G3AgdaBIDIReverseExactRemainingLemmas20261122.md`, ledger commit `14b2ca29`.

---

## 22 November 2026 — P0 concrete original-bump q=4 witness, still NOT the RH signed terminal

**New original-source quantitative result**, source-written on
[PR #1533](https://github.com/chboishabba/dashi_agda/pull/1533):
`scripts/check_rh_original_bump_explicit_radius_20261122.py`,
and full proof ledger in
`Docs/proofs/RHR2G3AgdaBIDIReverseExactRemainingLemmas20261122.md`.

Mathlib `ContDiffBump.neg`, `ContDiffBump.le_one`,
`ContDiffBump.one_of_mem_closedBall` plus original Lean
`RiemannQuantitativeScaledBump` and the original projective
four-window pairing show the **actual fixed unit bump** is even,
bounded by 1, equal to 1 on the inner half-radius and affinely
scaled. This gives `E[Z²]>=1/24`; the original J2 equation
is QUADRATIC in smooth mu, so source-selected endpoint roots
are explicitly bracketed around the original atomic roots:
`|mu_exact-(mu0+mu1*eps)|<=600R^4`
with the strict J2 derivative >=10 in the small-radius regime.
The original corridor and `J4<-1/4` survive at R=10^-10.

At the explicitly selected `R=10^-10` the computed rational
majorant is `C=22848813692672` multiplying R4.
Therefore the exact original high-pole `q=4` smooth margin
`kappa_R>R²/6`, and via original uniform source transfer,
`t>=10^14, |a|<=1/2 ==> K_t(a,4;R)>11R²/300>0`.
These are mathematical source bounds checked with local SymPy,
NOT Lean/Agda kernel-certified (and no CI).

**Negative control / strict scope:** atomic high-pole
`K_inf(0,q=1)=-80/351<0`, so **the original source remains
sign-changing in normalized q**. q4 corresponds to moving
physical ordinate gamma=5t/4, not an actual-zero population
or universal sign. This fixes the earlier P0 ledger's statement
that the original smooth selected W was entirely unquantified:
a local single-q margin is now quantified, while a universal
actual-zero signed/W prime compensation theorem remains open.

**Geometry preserved:** an 8-vertex/12-directed-map/6-face
indexed cube with reflection/smoothing/pole axes is a bookkeeping
and non-promotion carrier. Keep ordered history/time/refinement,
Frobenius and consumer indices, balanced ternary sign, multiplicity,
and distinctions among zero scalar, unit C3 phase, nonempty
cancelled phase orbit, Fourier observed zero, and actual ζ-zero.
No six-face analytic transport is inferred from symbolic parity.

**Next nonduplicate P0:** original actual-zero localized
M0/M2/M4 marked-pair estimate and prime-side sign/coupling;
control all real q, actual ordinates/multiplicities, signed
near/far and local slack; pay the exact terminal
`H_n+E_n+S_W<T_W(rho)` (still OPEN). Avoid further
single-q Taylor work unless it actually supplies that payment.

---

## 22 November 2026 — exact selected atomic sign bifurcation and BIDI marked-fourth cut

**New local SymPy result committed, WITHOUT promotion to actual selected W or actual ζ zero distribution.** The original selected four-window *atomic* response, formed with `μ_0(λ)=(13λ−8)/(144−54λ)`, `λ=1/2,2/3` and original high-`t` pole coefficients `P∞(λ)=3(2−λ)/4`, obeys for **every real q**
```text
K∞(0,q)=−(80/351)*(1−cos(πq/2))² <= 0.
K∞(α,q)= (160/351)*cos(πq/2)*cosh(πα/2)
         −(40/351)*cos(πq)*cosh(πα)−40/117.
```
For `α!=0`, let `h=cosh(πα/2)>1`; the same exact kernel is **strictly positive** at a q with `cos(πq/2)=h/(2h²−1)`, and **strictly negative** at `q=4k`. Thus the source's *BASE* globally nonpositive square cannot be used as a full horizontal pointwise signed estimate. Horizontal reflection `α↦−α` preserves, not removes, this sign conflict.

Stronger: using the ORIGINAL **finite-`t` atomic pole determinant** (rather than high-`t` pole coefficients), physical `a=β−1/2`, normalized `α=16a/t` and `u=π/t`, exact local SymPy Taylor algebra gives
```text
K_{t,atom}(a,4)=(5120/351)*(1−16a⁴)*u⁴+O(u⁶)
K_{t,atom}(a,1)=−80/351+O(u²).
```
For each **fixed** `|a|<1/2`, this proves opposite signs for sufficiently large t **only in the atomic model**. The original Lean source owner `RiemannProjectiveQuarticFourWindowPoleSameObject.lean` supplies the actual finite pole weight `cosh(8v/t)cos(16v)cos(cv)`. The selected smoothed W remains `R>0` and the actual ζ-zero ordinates are **not** generated by choosing arbitrary q. A fixed-width `O(R)` localization estimate by itself cannot preserve an `O(t^-4)` sign for all unbounded t. Neither atomic sign is a theorem about actual W or actual ζ zeros.

**Existing Agda producer recovered (not missing mathematics):** `DASHI/Analysis/RiemannQuarticSignedPoleBidiMarkedFourthExact.agda` has the exactly owned reflection-centred `P4` decomposition into only **even marked moments M0/M2/M4**. Its `localizedOneCentreMarkedPairProducer`, `markedPairPrimeSideSignOrBound`, `centredFourthAngularBias` and `fourthAngularFarCouplingPaysG3` remain false/open. SymPy confirmed the exact P4 target/reflection identity. Two synthetic vertical lists `[-1,-1,1,1]` and `[-sqrt(2),0,0,sqrt(2)]` have the SAME `M0=4,M2=4` but opposite comparisons to a fourth-moment threshold 6 (`M4=4` versus `M4=8`). These are **not actual ζ zeros**; they prove M0 and M2 alone do not determine the fourth-order signed payment. This is why the already-paid RvM upper count / reflection geometry cannot settle the marked signed terminal.

**Exactly remaining math**, with original attribution:
1. Retain full terminal `H_W+S_W < T_W(ρ)=4d_W(ρ)+I_W` for every hypothetical high off-line actual ζ zero. Alternative literal finite signed certificate `H_n+E_n+S_W<T_W(ρ)` over the ORIGINAL half-open `(t-n,t+n]`, or eventually sharpened signed `B_n^sharp+S_W≤T_W(ρ)−ε`. A loose signed `H_W<T_W` **without local slack** is insufficient.
2. Original positive-width selected W, its true `μ_{½},μ_{⅔}`, actual finite ζ-zero ordinates and multiplicities, and quantitative signed finite source remain **OPEN**. Source Fourier, bounds, exact source cone/good/far partition, and actual RvM count remain reusable.
3. Alternatively source-locate the existing Agda/Lean **marked-fourth** M0/M2/M4 identity, prove the genuinely missing same-target localized actual-zero/prime-side marked-pair bound and couple its actual `μ` background and signed far source. Do NOT rebuild even-moment algebra.
4. External all-character trusted admission and independent Agda literal near+far+Gamma<ClusterResponse are separate avenues, not synonyms for this selected-W inequality.

**Executable original-source test:** `scripts/check_rh_selected_finite_t_atomic_sign_20261122.py`, commits `964db866`/`ed54cef3`, readback blob `af78e6365b55b194bc23d6dd5efb14ad979f580b` **matches exact locally executed Git blob**. SymPy 1.14.0 exact high-`t` all-real-q factorization, full horizontal positive/negative extrema, exact finite-`t` Taylor coefficient cancellation/order, even reflection, 16/16 untruncated high-precision finite-`t` signs, and 0/2/4 marked identity/negative controls **PASS**. High-precision signs aren't rigorous interval certificates. Source-authored math BIDI register updated `Docs/proofs/RHR2G3AgdaBIDIReverseExactRemainingLemmas20261122.md` (commits `ec86352c` / `7b0480f1`). **No** Lean/Agda kernel, CI, actual ζ off-line zero sample or RH/GRH theorem.

---

## 22 November 2026 — FULL post-sixth BIDI min-cut (corrected P0)

**Current theorem target supersedes the weaker G3 completed-residual-only threshold.** Original source `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourierTerminal.lean` proves
`postSixthCanonicalSignedHighCut_iff_completed_plus_localSlack`,
with `canonicalLocalBudgetSlack_nonneg`. Original `FourierMass`/joint-source gives `completedSignedResidual=(H-I)/2`.
For each actual selected `W`, original nontrivial ζ zero `ρ` at target ordinate `t`, and `EV=quarticSignedPoleCanonicalV4Error CV t`, let
`H=∑'W.signedLiteralPairSourceTerm`,
`I=∫W.signedOrdinateTest·Zeta23.mu`,
`d=W.combinedZeroHeightDefect ρ`,
`S=W.canonicalLocalBudgetSlack EV≥0`,
`T=4d+I`. **The literal complete post-sixth terminal iff `H+S<T`.**
Earlier `UniformSignedCompensationGap ρ` and its existing stronger `UniformSharpenedSignedCompensationGap ρ` as stated only imply **`H<T`**, not necessarily `H+S<T`; `H=3,I=0,d=1,S=2` is an exact counterexample. Never drop `S` at the final endpoint.

**Already-paid improved cone geometry was overlooked.** The existing same-original-zeros `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleConeDecomposition.lean` proves `literalConeExactAt_eq_debt_sub_gain`, `literalSharpenedJointBudgetAt_le_jointBudgetAt`, `literalOffOrdExactAt_le_sharpenedJointBudget`, `UniformSharpenedSignedCompensationGap`, and old→sharpened. A negative cone term is **useful signed gain**; replacing it or a negative far term by absolute value loses precisely the candidate compensation. Good-lane absolute remainder can still be slack. Reuse that source, don't reimplement another cone theorem.

**Reverse-solved exact weaker/stronger alternatives (conditional on existing source far-tail inequality):**
- **Direct finite signed certificate**: `H_n=W.literalOffOrdExactAt n` over original **half-open** `(t-n,t+n]` with actual ζ zero multiplicities; if `E_n≥|H-H_n|` and `E_n→0` for `n≥ceil(t+7)`, then
  `H+S<T ⇔ ∃n≥ceil(t+7), H_n+E_n+S<T`.
  Forward uses gap `g=T-H-S>0` and `2E_n<g`; converse `H≤H_n+E_n`. The existing R2 `O(log t/t)` bound is a candidate **absolute** `E_n` using the pre-existing multiplicity-weighted RvM interval theorem and fixed-W symbolic derivative constants. Actual finite signed H_n must be evaluated/estimated on the original zero carrier. For each fixed t, E_n→0 as n→∞; no uniform fixed-n global assertion.
- **Sharpened sufficiency**: if eventually `W.literalSharpenedJointBudgetAt η n + S≤T-ε` with `ε>0`, then the exact cofinal theorem implies `H+S<T`. This is NOT necessary because the sharpened upper budget can exceed the exact finite source (absolute good remainders).
- **Core at fixed W**: `UniformQuarticFourPoleDeterminantCompilerTarget` remains source-written but kernel-UNPAID; previous SymPy radius `δ*=5.53270840772e-7` is mathematical input only. Original `UniformQuarticFourSignedPoleCore` is a conditional compiler; still need target-radius/sixth-moment/case conditions. Source actual ζ RvM/Weil supplies counts, not the signed finite values.

**Agda BIDI comparison was now checked against actual source**: `RiemannG2ClayTerminalBishopLocatedExact` and `RiemannG2UniformLiteralPhaseHighProducerExact` require an analytic **per-high-off-line-zero producer** plus Bishop low same-substrate inputs. The latter needs independent `literalNear+far+Gamma<ClusterResponse` and a **separate final balance attachment**. `RiemannG2ZeroSideHMBypassBidiExact` already compiles `H_X→H_T` and literal selected window→`H_W` without mandatory historical `H_M`; `RiemannG2HASingleSourceProducerBidiExact` already packages `H_A` as one dependent source-native producer. But Agda's literal cluster response is NOT yet proved equal to Lean's selected-W `H+S<T`; separate actual-zero, test/taper, scalar order and quantifier same-object welds would be needed. Avoid declaring this cross-language equivalence via shared terminology.

**Committed audit/acceptance**: exact full source-to-consumer ledger `Docs/proofs/RHR2G3AgdaBIDIReverseExactRemainingLemmas20261122.md` (commit `1ac70327`), Python `scripts/check_rh_bidi_reverse_terminal_20261122.py` (commits `f44d4390`, `3c0f7977`, blob `6eb3222e13d178ccc855f6ae24f1641221bb79d8`). Local SymPy 1.14.0 **108/108 exact terminal substitutions**, cone/good/far negative controls, real original selected atomic `μ(1/2)=-1/78,μ(2/3)=1/162`, source atomic `K(0,2)=-320/351`, finite-tail BIDI criterion and adversarial margin checks PASS. Exact local script Git blob equals committed GitHub blob, `py_compile` PASS. Earlier radius/actual-ζ count symbolic source test rerun PASS. **Not run** Lean/Agda kernel or CI. Not actual zero census; no strict signed theorem paid.

**Priority order**: P0 original mathematical `H_n+E_n+S<T` (or sharpened `B_n+S≤T-ε`) for every hypothetical high off-line ζ zero with its **same** original W, while paying source-selected W witness conditions; not another compiler. Parallel: Agda literal final scalar independent route and external all-character Lean theorem trust; avoid claiming any is already RH/GRH resolution.

---

## 22 November 2026 — uniform pole radius and actual-zeta logarithmic two-sided tail

**Source FIRST; original named finite analytic target mathematically
reduced; kernel acceptance pending.** This adds to the 22 Nov source
correction that the literal selected signed-W integral identity is
already theorem-bearing in Lean main.

### Original same-source owners recovered

- Synthesis/RiemannProjectiveQuarticFourWindowUniformPoleWeight.lean
  (blob 065baf7769b121c05611f92f5be55386e38e0074):
  actual high-t normalized pole weights have t-uniform
  Lipschitz K = 19 cosh(1) on [-6,6], t>=200, c=1,2.
- Synthesis/RiemannQuantitativeSymBumpLocalization.lean
  (blob f5ec98fa832e91b661193ae45259b0444c370201):
  positive normalized exact-mass symmetric radius-R bump.
- Synthesis/RiemannProjectiveQuarticFourWindowLocalization.lean
  (blob 28eaab93e1d05c214bc2b9541b5f12ef6379bba1):
  coefficient rectangle 1/2<=lambda<=2/3, |mu|<=1/10.
- Synthesis/RiemannProjectiveQuarticFourWindowPoleSameObject.lean
  (blob 60cc239d3968e25b8a42cebc18bf4744907facd3):
  actual signed pole coordinate is the determinant of four
  normalized source pairings, not a synthetic test.
- Synthesis/RiemannProjectiveQuarticFourWindowPoleLocalization.lean
  (blob 45eeecdd828d903b6c3d7406ea1c616d4852e9ae):
  each atomic determinant coordinate has abs <= 5 for t>=200.
- Synthesis/RiemannProjectiveQuarticThreeWindowRobustness.lean
  (blob 53bc06356d778d52582244bf5dc4b3af1b9c79f7):
  existing exact determinant perturbation theorem
  |D-D0| <= (4M+2)*xi for entry errors <=xi<=1.
- Synthesis/RiemannProjectiveQuarticFourWindowUniformPoleLocalization.lean
  (blob 2fbcdf785511ffc064d393d7f62d6c6de5ad212d):
  conditional fixed-width selected-W core compiler already exists.
  Its named remaining input, UniformQuarticFourPoleDeterminantCompilerTarget,
  remains UNINHABITED in UniformPoleLocalizationPaid.lean.
  Never count this mathematical source derivation as a kernel receipt.

### Explicit uniform determinant localization

For every source normalized bump, nonnegativity, exact mass and
support within R imply that the normalized pairing of an even
K-Lipschitz weight differs from its atomic-center evaluation by
at most K*R. This applies also to on-line cos(cx), c=1,2,
since Lipschitz <=2 <=K. The original FOUR-window absolute
coefficient sum is B=1+1+2/3+1/10=83/30.
Thus each of the four original smooth determinant entries differs
from the source atomic entry by at most xi=B*K*R.
Using M=5 and source perturbation theorem (4M+2)=22,
the determinant error <=22*B*K*R, for xi<=1.

The ORIGINAL determinant tolerance is
  eta0 = min(1, (7*pi^4/800)/(2*(4*(10+pi^4)+2))).
Consequently an explicit positive radius INDEPENDENT OF t is
  delta* = eta0 / [22*(83/30)*19*cosh(1)]
         = 5.53270840772e-7 approximately.
For every t>=200, 0<R<delta*, allowed lambda,mu,
the smooth/atomic determinant difference is <=eta0.
This is an exact mathematical derivation from original source
premises, not a newly admitted Lean theorem. Once its named
Lean statement is kernel-checked, the EXISTING source compiler
constructs one fixed R and selected muHalf/muTwo with original
signed target strength floor for every t>=200.

### Actual selected W full horizontal weighted C4 control

Let b_j = ||unitBump^(j)||_1 / ||unitBump||_1, b_0=1.
These are finite but numerically UNMEASURED source Mathlib
ContDiffBump values. For B=83/30, the original profile
  G = [B_0 - B_{pi/3} + lambda*B_{pi/2} + mu*B_pi]/(2R*B0)
satisfies ||G^(j)||_1 <= B*b_j/R^j.
The existing source profile is
  P_G(x)=4G(x)[A1*cos(2x)-A2*cos(x)],
with |A1|, |A2| <= B.
For original signed selected combination
  P_W = pTwo*P_half - pHalf*P_two,
the determinant pole coefficients are each <=72 in abs
(smooth response entries <=5+xi<6).
Therefore, for j=0..4,
  M_j(W)=||P_W^(j)||_1
    <= Mstar_j(R)
     = 576*B^2 * sum_{k=0}^j binom(j,k)
                   *(2^(j-k)+1)*b_k/R^k.
In particular Mstar_0=1152*B^2=220448/25.

At source t>=200, the true horizontal parameter
alpha=(Re(s)-1/2)/(t/16) satisfies |alpha|<=8/t<=1/25,
both sides of the half line; original support L<=pi+R<pi+1.
Define
  Dstar(R)= exp((pi+1)/25) *
    sum_{j=0}^4 binom(4,j)(1/25)^(4-j) Mstar_j(R).
Then the existing actual selected-W cosh-cos Fourier identity and
four integration by parts give
  |K_W(alpha,q)| <= Dstar(R)/|q|^4
for q!=0 and the true source alpha.
The literal actual-zero summand carries its exact multiplicity:
  |sourceTerm(sigma)| <= mult(sigma)*(t/16)^2*Dstar(R)
                         /|Im(sigma)-t|^4.
Dstar is finite and t-independent GIVEN the fixed-width core;
it is not a practical numerical constant and is not signed.

### Sharper ACTUAL zeta, both positive and negative ordinate tails

Do NOT reuse the obsolete A=160 total-count upper bound when
the stronger original source already exists:
  Synthesis/RiemannZeta23RvMArbitraryEndpointCountBound.lean
  (blob 5fcf3260c204e873ae4cb91de04b34d8c4d1e669)
proves existence of C_N>=0 such that
  N(A,B) <= C_N*(B-A+1)*log(B+4), 5<=A<B
on actual zeta zeros WITH multiplicity.
Synthesis/RiemannZeta23RvMTwoSidedDiscrepancy.lean
(blob c4a78b921820a0a3846659fbcb98662d4f7e8a51)
preserves count/multiplicity for negative heights by conjugation.

For t>=200, choose an integer cofinal cutoff n>=t+7.
Right original half-open shell (t+k,t+k+1] has at most
2*C_N*log(t+k+5) multiplicity. The left shell
(t-k-1,t-k] reflects into a subset of
(k-t-1,k-t+1] of width 2, including all boundary multiplicity,
so its count <=3*C_N*log(k-t+5).
For every integer k>=n, total both sides <=
5*C_N*log(t+k+5) <= 5*C_N*log(2k).
Thus the *complete positive+negative height* ABSOLUTE far tail obeys
  sum_far |literalSourceTerm(sigma)| <=
  5*C_N*(t/16)^2*Dstar(R)*[
    log(2n)/n^4 + log(2n)/(3*n^3) + 1/(9*n^3)].
The exact antiderivative is
  int_n^infinity log(2x)/x^4 dx =
    log(2n)/(3*n^3)+1/(9*n^3).
For n(t)=ceil(t+7), the RHS is O(C_N*Dstar(R)*log(t)/t)
and tends to zero as t tends to infinity.
This is a new source-grounded t-VARYING cutoff tail; it is NOT
uniform in t at fixed n. It is NOT a signed cofinal surplus,
nor a theorem forbidding an actual off-line zero.

### Tested local receipt; comparison with external theorem

Source-specific script newly committed on Agda #1533:
  scripts/check_rh_r2_uniform_pole_and_two_sided_tail_20261122.py
  commit 98eaf7e62db888fd04803888d9d49e1dfcf8e0c8,
  readback blob 76073cd50eb9befd03cb57bd61f771fef9b098a5.
Local SymPy 1.14: 256/256 exact determinant corner adversaries;
12,010/12,010 source pole-weight derivative numerical stresses;
exact coefficient algebra, full cosh-weighted 4th Leibniz derivative,
logarithmic tail antiderivative, and t^2 F(t+7)->0 PASS.
Negative controls deliberately reject dropping quadratic determinant
error and fixed-cutoff t-uniform estimates.
Locally executed mathematically matching script; committed text
was read back but not byte-compared with local test.
Original all-character source checked syntactically in
pinned MainTheorems.lean + MainConclusion.lean:
  allChi := UpperTheory.FinalTheorems.everyCharacter,
  rhOfAll := Formalism.VW.rh_of_every allChi,
  root Main.lean has unconditional *declared* RH/Dirichlet GRH
  theorem signatures. The original claim is stronger in stated
  quantification; *trusted kernel admission* is NOT established
  by any of these symbolic/finite tests. The existing DASHI
  signed compensation is still literally an assumed premise.

**P0 REMAINS:** kernel-implement uniform determinant lemma on original
Lean source; obtain an effective source bump norm witness or accept
finite symbolic constants; prove the actual signed cofinal
UniformSignedCompensationGap rho (or sharpened exact same-source variant)
including original zero multiplicities, source target threshold and
quantifier order. There is no RH/GRH claim from these tests.
No Lean/Agda or GitHub CI was run.

---

## 22 November 2026 — selected-W FULL horizontal-weighted q^-4 formula (symbolically discharged, constants/uniformity OPEN)

Following the source correction, the original Lean theorem
`QuarticFourSignedPolePair.signedNormalizedPairKernel_eq_combinedIntegral`
and the original actual selected-W compact-`C⁴` theorem
give a concrete **human-level symbolic full-horizontal kernel
tail** at any fixed selected `W` and `t`, not just the
unweighted base channel.

Let `P_W=quarticFourSignedPoleCombinedProfile
W.R W.muHalf W.muTwo t`, supported in
`[-L,L]` (take `L=π+W.R` from the
source four-center bump support), and define
`M_j(W)=∫ |∂_x^j P_W(x)| dx` for `0≤j≤4`.
For `q≠0`, `|α|≤a`, put
`P_{W,α}(x)=P_W(x)cosh(αx)`. Product
differentiation gives the **exact formula**
```text
(P_W cosh(αx))'''' =
    P_W'''' cosh(αx)
  + 4α P_W''' sinh(αx)
  + 6α² P_W'' cosh(αx)
  + 4α³ P_W' sinh(αx)
  + α⁴ P_W cosh(αx).
```
On `|x|≤L`,
`|cosh(αx)|,|sinh(αx)|≤exp(aL)`.
The already source-proved compact Fourier
fourfold integration-by-parts lemma therefore
yields the precise conditional-norm inequality
```text
|W.signedNormalizedPairKernel(α,q)|
 ≤ exp(aL)/|q|^4
    ·[M4 + 4a M3 + 6a² M2 + 4a³ M1 + a⁴ M0].
```
For an actual off-ordinate zero `σ` in the
critical strip, the source identifies
`r=t/16`, `α=(Re σ−1/2)/r`,
`q=(Im σ−t)/r`. Hence for `t>0`,
`|α|<8/t`, and
```text
|W.signedLiteralPairSourceTerm σ|
 ≤ mult(σ) (t/16)^2 exp(8L/t)
   · [M4+4(8/t)M3+6(8/t)^2M2
        +4(8/t)^3M1+(8/t)^4M0]
   / |Im σ−t|^4.
```
The `mult(σ)` is the actual original zeta
zero multiplicity, NOT dropped for a
scalar surrogate. The estimate applies to
**both horizontal sides** because the
kernel is cosh-even in `α`; it is
an ABSOLUTE tail envelope and proves
NO desired signed surplus by itself.

**Local executable mathematical check:** the EXISTING
`scripts/check_rh_r2_explicit_zero_shell_fourier_20261117.py`
was extended in place (commit `e3c25a13`) to audit
the exact source identity status, the five-term
weighted fourth Leibniz derivative,
horizontal reflection, `α=0` base recovery
and true strip `8/t` radius. Independently
executed local SymPy 1.14.0: **7/7**
new exact derivative/normalization assertions
PASS. The full revised file has been
committed and source-readback verified but
not executed end-to-end in this runtime;
do not state a complete script receipt
or native Lean kernel result.

**Precisely UNPAID:** obtain numerical/source-quantified
uniform bounds for the **actual**
`W.R,W.muHalf,W.muTwo,W.poleHalf,W.poleTwo`
and `M_j(W)`; prove those are strong enough,
with actual two-sided ζ-zero counts and
tail/cutoff quantifiers, to pay the
correct-polarity cofinal
`W.UniformSignedCompensationGap rho`.
An arbitrary fixed-t positive finite-core
estimate, absolute convergence, symbolic
`q^-4` formula or same-ordinate local
positive signal does not imply the
universal strict RH inequality. This
update is a proof-of-algebraic-estimate
at paper level, **not** a new kernel-accepted
original analytic GRH/RH result.

---

## 22 November 2026 — SOURCE RECLASSIFICATION: selected-W integral already proved

This dated source audit **supersedes the first 17 Nov open
lemma** `selectedQuarticFourWActualProfileIntegralExact`,
as phrased there: **the literal same-selected-W
weighted Fourier/cosh representation is ALREADY
theorem-bearing in original Lean main**, not an
unconstructed theorem. Do not write a new replacement
theorem or copy the same proof into this branch.

Inspected exact source paths and Git blobs:

- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean`
  blob `4d0437ffb058c7e8b6961521a611608b1494ba3f`,
  **lines 1142–1203**:
  `QuarticFourSignedPolePair.signedNormalizedPairKernel_eq_combinedIntegral`
  proves directly, for the ACTUAL selected
  `QuarticFourSignedPolePair t`,
  ```text
  W.signedNormalizedPairKernel α q =
     ∫ x, quarticFourSignedPoleCombinedProfile
                W.R W.muHalf W.muTwo t x
             * cosh(α*x) * cos(q*x)
  ```
  including both original signed pole coefficients
  and the two actual source windows; the proof
  establishes integrability and expands the true
  source definitions, not an abstract W.
- In the **same** source, lines 415–440:
  `W.signedLiteralPairSourceTerm_eq_normalizedPairKernel`
  identifies the genuine original non-same-ordinate
  zero summand with
  `mult(σ)/(t/16)² * K_W(heightOf σ/(t/16),
      (Im σ−t)/(t/16))`. The necessary analytic
  `Re(s)−1/2` reflection is already visible
  through the cosh-even dependence.
  `W.signedNormalizedPairKernel_eq_jointJet`
  and `_eq_quarticJet` also source-write
  the exact base/horizontal/remainder split.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleTarget.lean`
  blob `16110e433efd16379c6b93bdc13420036b1d6411`
  defines the **literal** combined profile and
  exact zero- and second-moment identities.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourthOrderQuotient.lean`
  blob `6b30db459d28a2b5707cec004b570ff7061e1a8a`
  proves source-selected
  `quarticFourSignedPoleCombinedProfile_contDiff_four`,
  `compactCosineTransform_abs_le_invPowFour`
  and the **literal base ordinate channel**
  `W.signedOrdinateTest_abs_le_gap_four`,
  ```text
  |W.signedOrdinateTest x|
    ≤ (t/16)² * ∫ |P_W''''(u)| du / (x−t)⁴
  ```
  for x≠t and t>0. The original proof
  already uses the actual combined W profile,
  not an arbitrary test substitute.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleConeDecomposition.lean`
  blob `2fb66d2e7c4345673e1dda82e67823bf2d7e0481`
  proves the actual cone/good/far
  **algebraic** split and convergence compiler,
  but `W.UniformSignedCompensationGap rho`
  at lines 941–953 remains an **ASSUMED
  strict eventually quantified inequality**.
  Its theorem
  `completedSignedResidual_lt_target_of_uniform_compensation_gap`
  at lines 960+ consumes, rather than constructs,
  that analytic payment.

**Revised R2 priority:**
1. **PAID SOURCE-WRITTEN:** exact selected
   W ↔ weighted cosh-cos integral,
   source multiplicity/scaling and both
   horizontal sides, exact `C^4`/compact
   selected W, fourth-power base-channel
   `signedOrdinateTest` decay.
2. **OPEN QUANTITATIVE:** explicit *selected*
   `W.R,W.muHalf,W.muTwo,W.poleHalf,W.poleTwo`,
   actual derivative-norm and
   horizontal-weighted `P_W(x)cosh(αx)`
   bounds and their uniformity in t,
   original ζ zero multiplicities and
   cutoff. Do not incorrectly promote
   the `α=0` **base** tail theorem
   to the full `α≠0` horizontal source.
3. **OPEN ORIGINAL SIGN:** a **strict
   correct-polarity cofinal margin**
   `W.UniformSignedCompensationGap rho`
   or its source-valid sharpened version,
   with actual original ζ-zero configurations,
   completed residual and the exact
   quantifier order (not test-specific floats).
4. **OPEN TRUST:** no new exact-head Lean
   kernel receipt was run by this
   Git source-readback audit.

**Acceptance distinction:** source declarations, bodies
and dependency edges were read directly from the current
`dashi_lean4/main` tree, but no Lean/Agda typechecking
was executed in this runtime. This corrects a
stale research-status classification rather
than newly proving an R2 estimate.

---

# RH R2 — explicit unconditional shell count A=160, parameterized C, exact remaining lemmas (2026-11-17)

**Classification:** classical unconditional external zero-count theorem plus elementary analytic deductions; local SymPy checks of algebra. **R2 OPEN. No new Agda/Lean kernel theorem.** The explicit value A below is universal but deliberately generous.

## 1. Verified zero-count source and constant

Use Chiara Bellotti and Peng-Jie Wong, *Improved estimates for the argument and zero-counting function of the Riemann zeta-function*, Math. Comp., published electronically 2025-11-14, DOI 10.1090/mcom/4133, with
`|N(U) - U/(2pi)*log(U/(2pi*e))| <= 0.10076 log U + 0.24460 loglog U + 8.08344` for `U>=e`. Count includes multiplicity; no RH required.

For `U>=e`, using `loglog U<=log U`, `U log U>=e`, and `U/(2pi)log(U/(2pi*e)) <= U log U`, one obtains
`N(U) <= (1+0.34536+8.08344/e)*U log U <5U log U`.
For `0<=U<e`, monotonicity gives `N(U)<=N(e)<5e<20`.
Thus for all `U>=0`,
`N(U)<=20(1+U)log(e+U)`.

For `t>=0`, integer `k>=1` and `X=1+t+k>=2`, symmetry of the actual nontrivial zeta zeros about the real axis gives the **multiplicity-weighted** shell count
`Z(t,k)=#{rho: k<=|Im(rho)-t|<k+1} <=2N(t+k+1)`.
Using `1+t+k+1=X+1<=2X` and `log(e+X+1)<=2log(e+X)` gives
**`Z(t,k)<=160*(1+t+k)*log(e+t+k)`**.
At the inclusive shell boundary use `N(t+k+1)` as an upper bound, so endpoints cannot invalidate the inequality. This count is **not** a proportion of off-line zeros and does not assume RH.

Note: the previously supplied Hasanalizade–Shen–Wong JNT DOI was incorrectly given as `...06.028`; the verified DOI is **10.1016/j.jnt.2021.06.032**. The cited Carneiro–Chandee–Milinovich 'Mollifiers and the zeros...' title/identifier was not verified and is not used as a source of this bound.

## 2. Parameterized fourth-derivative kernel constant, NOT yet instantiated

For `P∈C_c^4(R)` supported on `[-L,L]` and
`F(alpha,q)=integral P(u)e^(alpha*u)e^(i*q*u)du` with `|alpha|<=a`, four integrations by parts give
`|F(alpha,q)|<= e^(aL)/|q|^4 * sum_(j=0)^4 binom(4,j)*a^(4-j)*||P^(j)||_1`.
In particular with `r=t/16`, `alpha=(beta-1/2)/r`, the zeta critical strip gives `|alpha|<=1/(2r)=8/t`, and for `|gamma-t|>=k>=1`, using `((k+1)/k)^4<=16`, the multiplicity-normalized physical term has envelope
`C(t,P)/(1+k)^4`, where
`C(t,P)=16*r^2*exp(L/(2r))*[M4+4a M3+6a² M2+4a³ M1+a⁴ M0]`,
`a=1/(2r)`, `M_j=||P^(j)||_1`.

**Important:** the original `W.signedNormalizedPairKernel` is defined as a signed linear combination of `genericProjectivePairKernel` terms for two distinct profiles. Before inserting this `C(t,P)`, one MUST prove the appropriate exact integral representation with its signed pole factors, distinguish possible `cosh(alpha u)`/base subtractions, and bound each term. The formula is a **conditional donor**, not an evaluation of the selected witness.

The original Lean identity is
`signedLiteralPairSourceTerm sigma = mult(sigma)/r² * W.signedNormalizedPairKernel ((beta-1/2)/r) ((gamma-t)/r)`.
Original finite far source is `W.literalFarExactAt eta n` with `eta=1/(pi+1)` and `centeredZeroFinset t n` iff `t-n<gamma<=t+n`. The original `literalGoodQuarticGainAt` uses `S*(alpha²q²-q⁴/6)`, **not** the newer complete quartic with an additional `-alpha⁴/6`.

## 3. Local executable check

`scripts/check_rh_r2_explicit_zero_shell_fourier_20261117.py` checks:
- the 2025 published coefficients imply the generous factor 5 via exact rational/SymPy inequalities;
- the two-sided unit-shell count admits A=160;
- binomial fourth derivative envelope and physical rescaling;
- the exact fixed-t tail integral and monotonicity.

It does **not** numerically integrate the selected W or formally prove the cited N(U) theorem. These remain separate acceptance gates.

## 4. Exact remaining lemmas / producers

1. **`selectedQuarticFourWActualProfileIntegralExact` (OPEN):** extract the constructed `QuarticFourSignedPolePair t` and show the exact selected `signedNormalizedPairKernel` equals the claimed Fourier integral or a finite combination, including pole coefficients, horizontal factor and source normalization, for every `alpha,q`.
2. **`selectedQuarticFourWDerivativeNormsExplicit` (OPEN):** determine actual W parameters and compact support `L`, calculate/certify `||P_j^(m)||_1` for `m=0,...,4`, bound `cosh`/horizontal terms, and construct an explicit valid `C(t,W)` on `0<=beta<=1`. A symbolic expression with unknown norms does not close this lemma.
3. **`originalActualZetaUnitShellCountA160` (CLASSICAL COROLLARY; NATIVE OPEN):** instantiate Bellotti–Wong 2025 zero count in Lean for the original `Zeros` type, multiplicity, real-axis reflection and interval endpoints; deliver the numeric universal constant `A=160`.
4. **`originalLiteralFarExactCertifiedFinite` (OPEN):** certified interval value of `W.literalFarExactAt eta n` for the source selected W and actual zero ordinates, preserving sign; verify `OffOrdExactAt=ConeExactAt+GoodExactAt+FarExactAt`.
5. **`originalSelectedTargetThresholdCertified` (OPEN):** calculate actual `T_W(rho)=4D_comb(rho)+∫Psi_t dmu` from the literal selected witness, not generic surrogate.
6. **`originalSelectedFiniteSignedSurplusStrict` (OPEN):** construct a rational `epsilon>0` and finite cutoff with a **certified** positive surplus in the *correct polarity*, including local remainder and target threshold; explicitly handle same-height exclusion and multiplicities.
7. **`originalSelectedUniformCofinalTail` (OPEN):** combine an instantiated `A,C(t,W)` with a rigorously uniform cutoff and the literal signed far term; the supplied majorant only converges with n for fixed t.
8. **`originalR2EventualSignedCompensationGap` (OPEN):** prove `exists eps>0, N, forall n>=N: LocalDebt_n-SignedCompensation_n<=T_W(rho)-eps` for the originally quantified t,rho,W. For fixed t and W, a certified total surplus and a tail smaller than half that surplus suffice; a margin depending on t or rho does **not** imply the universal target.
9. **`originalR2NativeKernelWeld` (OPEN):** typecheck and import the actual proof at exact Lean/Agda heads, then update gate ledger only after the original acceptance predicate is discharged.

**Accounting:** Classical external A bound established, but the native carrier and all selected-W signed-gap producers OPEN. Portfolio remains **13/28 settled, 15/28 open**; **0/6 original Clay endpoints**.
