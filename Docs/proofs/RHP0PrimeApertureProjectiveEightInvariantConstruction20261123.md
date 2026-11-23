# RH/GRH P0 — geometric construction audit: exact two-prime aperture with eight preserved projective invariants (23 November 2026)

**Status:** genuine mathematical finite-codimension **existence construction**, plus executable exact SymPy and numerical smooth-fixture tests; **NOT yet a Lean/Agda kernel theorem**, **NOT** an inhabitant of the unmodified four-window `QuarticFourSignedPolePair t`, **NOT** a new strict RH/GRH signed estimate. This is a forward geometry/reverse-solve audit of the ORIGINAL source, not a replacement Fourier-model/Monster construction. Preserve t, projective endpoint and sign, pole owner, absolute-tail derivative cost, and the full signed post-sixth slack.

## 1. Original geometry and the actual obstruction

Merged original `chboishabba/dashi_lean4` **main** owns:

- `Synthesis/RiemannProjectiveQuarticFourWindowHighWitness.lean`: `quarticFourPhysicalDetector R λ μ t u = quarticFourWindowProfile R λ μ ((t/16)u)`; its support is `|u|<16(π+1)/t`, in particular **strictly below log 2 for t≥200**. Hence all prime-power values of this original detector are zero.
- `...CircularHyperbolicDuality.lean`: for ANY admissible even smooth detector g, `P_g(u)=4g(u) B_g(u)`, where `A1(g)=∫g(u) cos(ru)du`, `A2(g)=∫g(u)cos(2ru)du`, `B_g(u)=A1(g) cos(2ru)-A2(g)cos(ru)`, `r=t/16`. `∫P_g=4(A1 A2−A2 A1)=0` exactly.
- `...FourWindowPoleSameObject.lean`: the two original pole-response weights are `cosh(u/2)cos(tu)cos(c r u)`, c=1,2. The selected signed two-endpoint coefficient/determinant and local target strength are owned by `...SignedPolePair.lean`, `...SignedPoleTarget.lean`.
- `...SignedPoleCutset.lean`: `combinedCluster_eq_offGamma`, `combinedCluster_eq_tsum`; `...SignedPoleFourthOrderQuotient.lean`: `completedSignedResidual_eq_jointPairSource`. The original short-support **prime-blind** signed identity `H_W−I_W=2D_W(t)` is exact, and under a hypothetical offcritical target gives `H_W−I_W+S_W−4d_W(target)=2(D_W−2d_W)+S_W≥0`. It cannot be recycled as an independent strict upper bound.

The original `R`, `muHalf`, `muTwo` are selected existentially. Do NOT claim an explicitly numerical native original W from the atomic corridor or from a substitute C∞ bump.

## 2. Exact finite-constraint geometrical extension of the two ORIGINAL endpoint detectors

For a **fixed** t≥200 and one endpoint of the original selected W, take the original PHYSICAL even C∞ g, its A1,A2,B_g as defined above. Set the open, symmetric physical aperture

    U=(0.36,1.25) union (-1.25,-0.36).

The old source support is in `|u|<16(π+1)/t≤0.331328...`; hence `supp g` and U are disjoint. U contains **±log2 and ±log3** but excludes ±log4 and every subsequent prime-power location. Choose even C∞ compact h supported inside U, and impose these EIGHT exact linear conditions:

    L1(h) = ∫ h(u) cos(r u)du = 0
    L2(h) = ∫ h(u) cos(2r u)du = 0
    L3(h) = ∫ h(u) u^2 B_g(u)du = 0
    L4(h) = ∫ h(u) u^4 B_g(u)du = 0
    L5(h) = ∫ h(u) u^6 B_g(u)du = 0
    L6(h) = ∫ h(u) u^8 B_g(u)du = 0
    L7(h) = ∫ h(u) cosh(u/2)cos(tu)cos(r u)du = 0
    L8(h) = ∫ h(u) cosh(u/2)cos(tu)cos(2r u)du = 0.

**Exact effect, not linearization error:** `A1(g+εh)=A1(g)` and `A2(g+εh)=A2(g)` for ALL real ε, therefore `B_{g+εh}=B_g` EXACTLY, and

    P_(g+εh) = P_g + 4 ε h B_g.

All original projective even moments M0,M2,M4,M6,M8 are identical before/after perturbation: M0 cancels algebraically, and the other four are L3–L6. The two original pole response scalars are unchanged by L7,L8; the original signed endpoint pole coefficients, pole cancellation, J2 null, signed fourth target strength, and raw sixth/eighth **signed moments** survive for the *extended* pair. This does NOT preserve an original numerical derivative-envelope theorem: such norms are nonlinear and depend on support.

Apply the construction independently to both original signed endpoints. The corrected pair is a NEW `ExtendedQuarticSignedPolePair` carrier (name proposed, not a checked Lean declaration); it is **not** the original four-window W. An exact generalized Weil/prime-channel source identity must be built to replace `combinedCluster_eq_offGamma`, because the short-support hypothesis is deliberately broken.

## 3. Exact two-prime evaluation theorem: no finite number of smooth integral constraints can close the aperture

Let X be the vector space of even C∞ compactly supported functions on U; let `L:X→R^8` be the eight functionals, each integration against a continuous even weight. Define evaluation `E(h)=(h(log2),h(log3))`.

**Mathematical theorem:** E maps `ker L` **onto R²**, for each fixed original selected endpoint and every t≥200. No nondegeneracy or numerical rank assumption is required.

**Proof (finite-dimensional duality + original smooth bump construction):** if E restricted to `ker L` were not onto, a nonzero combination `a h(log2)+b h(log3)` would vanish on `ker L` and hence factor through finite-dimensional `im L`: it would equal `∑_{j=1}^8 c_j L_j(h)` for ALL h∈X. Choose an even height-one C∞ bump `h_delta` of arbitrarily small support about ±log2 with `h_delta(log2)=1` and `h_delta(log3)=0`. Since all eight weights are continuous on a compact neighborhood, each `L_j(h_delta)=O(delta)→0`, forcing a=0. A bump about ±log3 similarly forces b=0, contradiction. Thus there exist actual smooth even `h_2,h_3∈ker L` with

    E(h_2)=(1,0), E(h_3)=(0,1).

This same proof works for ANY FINITE list of additional original smooth moment/pole constraints, not just eight. The source's own `quantitativeSymBump`/`scaledUnitBump` machinery furnishes suitable smooth bump functions; the existence argument does not assume an independent new analytic species.

Therefore for any small real ε2,ε3, `g+ε2 h_2+ε3 h_3` has independently controllable prime sample values, and all eight original finite constraints stay **exactly** fixed. Sign and zero/neutral coordinates of each port are retained.

## 4. Retaining strict off-line target positivity: tenth-order stability (not uniform tail certification)

For the signed combination of the *extended* pair, denote the original same-object signed profile by `P_W`, its original positive target defect by `d_W(a)`, with PHYSICAL horizontal coordinate `a=β−1/2∈[-1/2,1/2]`. Because the original NORMALIZED source has `M0=M2=0`, `M4=-4 T_W<0`, while the PHYSICAL detector profile has fourth moment `M4^physical=-4*T_W/r^6` (including the `1/r` projective bracket factor),

    d_W(a)=-1/4∫ P_W^physical(u)cosh(a u)du
           = (T_W/r^6) a^4/24 + O_t(a^6) >0   for 0<|a|≤1/2,

when the original W has been selected with its source `8/t<eps` property. The new perturbation `ΔP` has `M0(ΔP)=M2=M4=M6=M8=0`, therefore

    Δd(a)= -1/4∫ ΔP(u)
      [cosh(a u)-1-(a u)^2/2!-(a u)^4/4!-(a u)^6/6!-(a u)^8/8!] du
          = O((|ε2|+|ε3|) a^10).

Since original `d_W(a)/a^4` extends continuously with strictly positive limit `T_W/(24*r^6)` at a=0, and is strictly positive on the compact nonzero strip, it has a positive minimum for any FIXED t/W. Selecting small enough amplitudes preserves target positivity for all `0<|a|≤1/2`, the exact pole coefficient, and the original fourth target strength. **No uniform-in-t lower bound for the allowed amplitudes is established.** The post-sixth/local sixth/eighth signed-moment entries are retained, but their support/absolute-derivative/Schwartz bounds and their application to the full P0 terminal must be re-certified for this enlarged support.

## 5. Arithmetic signal and the reversible-sign countercheck

The standard Weil/Guinand explicit formula samples smooth physical test functions at `±log(p^k)`, weighted by `Λ(p^k)/sqrt(p^k)`; see Suzuki, *Journal of the London Mathematical Society* (2023), equation (5.15): https://doi.org/10.1112/jlms.12785 . For tests supported in U together with the original core, only p^k=2,3 are now potentially visible. The centered physical modulation supplies cos(t log p) phases in the ordinary even-pair normalization. **Exact sign and scalar of the original signed-projective prime channel require a NEW source-native explicit-formula weld; the sampling rule alone is not that weld.**

For every real t>0, `cos(t log2)` and `cos(t log3)` cannot both vanish: otherwise `log3/log2=(2m+1)/(2k+1)∈Q`, contradicting unique prime factorization. Thus at least one basic arithmetic phase exists at every positive height. At the test-function level the port signs can be reversed **without changing any of the eight integral constraints**. Consequently **the finite quartic/pole geometry alone cannot imply the independent strict global RH sign**. The new arithmetic amplitude must be quantitatively coupled to all original zero and Gamma channels and the post-sixth slack, rather than selected by fiat.

Atomic source corridor controls (NOT native selected W): exact SymPy `mu0(1/2)=-1/78`, `mu0(2/3)=1/162`, `(A1,A2)_half=(20/39,77/78)`, `(A1,A2)_two=(40/81,68/81)`, determinant **−20/351**. The t→∞ atomic original pole residuals are **9/8** and **1**. Two endpoint projective prime-port coefficients at log2/log3 were independently nonzero in the four executed numerical height fixtures, but this is **not** a global selected-smooth-W transversality proof.

## 6. Analytic cost/no-free-lunch: aperture point values are not high-derivative control

The original normalized profile support `|v|<π+1` is lost: `v=r u` at the new prime ports has `|v|=(t/16)log p=O(t)`. Thus the source's `combinedProfile_support_abs_le_pi_add_one`, `fourthLipschitz_le_explicitK0`, local uniform 6th/8th Taylor envelope, and the original `farShellBound` constants CANNOT automatically be imported.

A height-one smooth bump `b((u-c)/delta)` satisfies exact affine derivative L1 scaling

    ||∂^k b((u-c)/delta)||_1 = delta^(1-k) ||b^(k)||_1.

For k=0 this tends to zero as delta→0 despite fixed nonzero prime evaluation; for k=2 it grows like `delta^-1`, and for k=8 like `delta^-7`. The original source `RiemannQuantitativeScaledBumpMass.lean` already proves the 0/1/2 scaling, and the C∞ chain rule extends it to higher k. This is the **real tradeoff**: an almost-invisible mass/moment perturbation can be large at a discrete prime sampling point, but it can incur rapidly increasing Fourier-tail derivative expenses. Re-derive source-specific tail constants on the extended test; moment cancellations do not pay the absolute smoothness norm.

## 7. Local test evidence and exact scope

Executed locally, not GitHub CI: `scripts/check_rh_p0_prime_aperture_geometry_20261123.py` (SymPy, NumPy, 96-point Gaussian quadrature). Git blob SHA **c2dff1d56db20aa4a9d9f51e46dcb80b13937255** was verified identical to the locally py-compiled and executed version. The code checks exact symbolic source projective/moment/pole invariances, tenth-order first perturbation, affine derivative scale, exact atomic corridor fractions/determinant; then both endpoint test geometries at t=200, 1000, 80000, 1000000. Each of 8 numerical **8×22** smooth-fixture constraint matrices has full rank, condition number approximately 858–1519, max residual **1.735×10^-18**, and two disjoint prime-point evaluation ports (1,0)/(0,1). It also tests basic prime-phase sign reversibility and actual **ATOMIC-limit projected** port coefficients. The bump `exp(-1/(1-x²))` is only a numerical C∞ fixture; native Mathlib-selected smooth R(t), μ(t) and original Lean test were NOT numerically reconstructed. **Exact mathematical existence proof is above; matrix residuals are not exact kernel proof receipts.**

## 8. Reverse-solved P0 and exact next original-source welds

**What is paid:** geometric reach of prime logs 2,3; finite eight-constraint projective orthogonality; same-moment signed target geometry and its tenth-order perturbative persistence for sufficiently small amplitudes; per-height prime-phase nontriviality in the basic even-channel. This is a genuine alternate **construction**.

**Still unpaid:** (A) new generalized physical endpoint/extended signed-pair Lean/Agda carrier with original `paperFT/sampleTest` and literal Weil source admission; (B) derive and type-check the correct prime-power coefficient, t/zero/multiplicity/phase normalizations and pole cancellation, rather than importing the prime-blind `combinedCluster_eq_offGamma`; (C) re-pay absolute-sixth/eighth/Schwartz/far-shell costs with unknown t-dependent perturbation scale; (D) prove an **independent signed arithmetic–zero/Gamma upper estimate** (or an accepted external proof) that yields strict `H_{W'}-I_{W'}+P_{W'}+S_{W'}<4d_{W'}(target)` for every hypothetically off-axis target in the extended same-object source, with the **actual coefficient and sign of P** determined by the new Weil weld. No such estimate, and no root-proof import or all-character GRH proof, is established here.

The old RH P0 target `H_W-I_W+S_W<4d_W(target)` CANNOT simply be claimed for the extended W'. Its original identity exactly forces a nonnegative gap under a hypothetical target; the extended test introduces a new prime term and needs a wholly recertified original-source compiler. Keep the original R2-S0/R2-S1 lane open in parallel, but do not reapply original short-support theorem to the new aperture.

**Attribution:** original Lean selected four-window signed source/pole and projective moment theorem owners; classical smooth point-evaluation/finite integral functional duality; standard Weil explicit formula; locally derived eight-constraint two-prime construction, inverse/source tradeoff and numerical acceptance. **RH/GRH OPEN**; no false proof admission or new Lean/Agda kernel receipt.


## 9. Independent positivity route cannot be a re-label of this signed witness

The same original selected W has `M0=0`, `M2=0`, `M4=-4*T_W<0`. Its REAL-axis Fourier cosine response therefore satisfies

    K_W(0,q) = -(T_W/6)*q^4 + O(q^6) < 0
    for all sufficiently small q != 0.

By contrast an even Hermitian autocorrelation `Q=f*tilde(f)` has `hat Q(q)=|hat f(q)|^2≥0` on every real q. Therefore no source-original signed profile with `T_W>0` can itself be such a Gram-positive autocorrelation, and preserving M4 in the eight-invariant prime-aperture extension **preserves this incompatibility**. This is an elementary exact sign obstruction, not a new RH theorem or a refutation of Weil's positivity criterion.

If pursuing a known Weil quadratic-positivity construction, introduce an **independent** companion arithmetic test, prove its own source identity and quantitative sign without assuming RH, and supply a genuine linear/cross-pair comparison with the signed W. Do not call the negative-quartic W "positive definite" or import a globally positive Weil functional by an RH-equivalent premise. The executed SymPy script now checks this quartic/Gram sign separation and has readback blob **c2dff1d56db20aa4a9d9f51e46dcb80b13937255**.
