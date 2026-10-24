> **Superseding 2026-10-24 proof consistency result:** Ri's
> viscosity-INDEPENDENT Theorem 1.1 bound (1.3), in its stated
> all-viscosities/all-smooth-data form, is inconsistent with OpenAI's
> released unforced Euler C¹ blowup (for s>5/2), using standard smooth
> pre-blowup inviscid convergence and Sobolev embedding. This is a
> conditional mathematical incompatibility assuming the released Euler
> result, NOT a disproof of fixed-positive-viscosity NS regularity.
> See `Docs/research/ns_ab_ri_euler_no_go_and_physical_stretch_20261024.md`
> and source-written Lean
> `dashi_lean4/NSEulerRiUniformViscosityNoGo.lean` (kernel unchecked).
> Earlier text below assigning Ri's global A3 estimate as a candidate
> import is superseded; only his independently validated local
> frequency identities remain potential donors.
>
> **B acceptance witness:** `tests/test_ns_physical_vorticity_production_exact.py`
> computes an actual nonzero physical 3D triad with exact enstrophy
> production +8, independently matching twice the vorticity
> stretching integral; zero-padding leaves it invariant. The same
> smooth datum has positive *instantaneous* enstrophy derivative for
> a large amplitude at ν=1. This forbids a naive uniform
> dissipation-only pointwise stretching estimate, NOT subtle
> integrated compensation or global B regularity.

# NS A/B four-paper primary-source integration ledger — 2026-10-24

**Authority rule.** Original authors own every theorem below. arXiv HTML pages are primary manuscript versions, not independent theorem validation. DASHI owns only the mappings, logical discriminators, exact elementary checks, and eventual independently checked formal proofs. Do not describe a claimed theorem as a kernel result or transfer hypotheses between problems.

## Full manuscripts retrieved (primary HTML, not just abstracts)
1. Myong-Hwan Ri, *Global regularity for the Navier-Stokes equations with application to global solvability for the Euler equations*, arXiv:2601.15685v1 (2026-01-22), https://arxiv.org/html/2601.15685v1 . Theorem 1.1, Section 3. Claims that for all d>=3, s>=d/2-1, Leray-Hopf solution with divergence-free H^s datum obeys a global L-infinity H^s and L2 H^{s+1} estimate with C(s) independent of viscosity and dimension. Status: **author-claimed, not independently validated**. A: audit frequency-space averaging/smallness under rescaling, exact constants, homogeneous vs inhomogeneous norms, viscosity dependence, passage from local mild to arbitrary Leray-Hopf, high-frequency summation and continuation. Do not import Theorem 1.1 as axiom to close A3.
2. Rishad Shahmurov, *Threshold Decomposition of Vorticity Stretching and Palinstrophy*, arXiv:2605.01873v3 (2026-09-10), https://arxiv.org/html/2605.01873v3 . The current actual title and abstract explicitly disclaim unconditional 3D regularity. **Earlier claim that this arXiv ID names a completed Large-Data Global Regularity Part II theorem was WRONG and is superseded.** B: threshold-resolved stretching, direction-gradient viscous term, level-surface dissipation, p=3/2 transform Z=|omega|^(-1/4) omega; check exact boundary/regular-value and temporal integrability hypotheses before importing. At nonzero vorticity |Z|^2=|omega|^(3/2); define Z=0 at omega=0. Structural identity is NOT a uniform positive bound on vortex stretching and NOT B7.
3. Alexey Cheskidov and Hedong Hou, *Global existence of smooth solutions to the Navier-Stokes equations for initial data with infinite energy*, arXiv:2610.18797v1 (2026-10-13), https://arxiv.org/html/2610.18797v1 . Theorem 1.1 starts on T^d with divergence-free H^{-s}, s>=1, and produces u smooth for t>0, continuous at t=0 in H^{-s}. Theorem 1.3 gives a weak solution in W^{-1,p}. B: torus existence / oscillatory construction donor only; negative-norm initial trace DOES NOT imply classical bounded-energy, initial-time smoothness, uniqueness or Clay B. Inspect solution class and energy inequality before welding.
4. Peter Constantin, Mihaela Ignatova and Vlad Vicol, *Regularity of asymptotically axisymmetric solutions to the 3D Navier-Stokes equations with analytic forcing*, arXiv:2609.20803v2 (2026-09-29), https://arxiv.org/html/2609.20803v2 . Theorem 1.1 needs suitable weak solution, anisotropic Type-II mean bounds, exact collapsing-core axisymmetry, locally bounded C^2 force AND analyticity hypotheses. Conditional rigidity excludes relevant forced profiles if force vanishes/is analytic under THESE hypotheses. B: profile exclusion, not generic unforced blowup prohibition. Preserve OpenAI as source for C/D construction and Constantin–Ignatova–Vicol as source for this independent rigidity result.

## Operational proof joins to existing source owners
- A target: `NSTriadKNEuclideanCanonicalProjectedInteractionExact` and `NSWholeSpaceFiniteConvolutionSingleLimitExact` → actual continuum-solution Fourier/Plancherel carrier → signed A2 → scale-critical A3. Ri's high-frequency weighted argument is a *candidate lemma route*, not a purchased A3 solution. Compare the homogeneity to existing `scripts/ns_a_schwartz_fourier_same_object.py`; supercritical finite-time L2 source response does not itself yield a Serrin bound.
- B target: R236 original selected critical-production functional → R685 commutator-minus-tangent and R690 global signed rate, with Leray projection, exact compensating residual and noncore/core boundary. Shahmurov's physical vorticity threshold decomposition is a **different carrier** from the helical triad count-centered R440 defect; source-equal bridge required. Existing projection discriminator: `tests/test_ns_b_projection_same_shear_discriminator.py`.
- B candidate/profile: Constantin–Ignatova–Vicol's constrained core-profile exclusion can be used ONLY after proving anisotropy, Type-II, analytic force and core axisymmetry on the SAME hypothetical unforced candidate. Its zero-force special case does not remove the other hypotheses.
- B negative-control: Cheskidov–Hou's global positive-time solution construction is not uniqueness or a continuation criterion; weak initial trace is not smooth initial-time B.
- C/D released OpenAI proof machinery: import exact lemmas with original source provenance; forced construction does not imply an unforced theorem by setting f=0.

## Acceptance tests / phase
P0 source title, version, theorem and quantifier disambiguation: complete for all four from full primary HTML.
P1 exact reproduction of paper's main analytic proof chains: open. Prioritize Ri proof Section 2→3 and Shahmurov threshold balance.
P2 formal theorem contracts with all hypotheses expressed and no free 'proof complete' Boolean: open.
P3 same-object R236/R685/R690 or continuum A2 bridge: open.
P4 uniform scale-critical global regularity and kernel receipt: open.
An elementary local numeric verification of |Z|²=|omega|^(3/2) for nonzero values is **not** a paper theorem proof. No Lean/Agda kernel receipt or finished A/B claim.
