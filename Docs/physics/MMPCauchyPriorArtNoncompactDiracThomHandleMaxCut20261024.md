# MMP noncompact Cauchy / true magnetic return handle / Dirac Hadamard max-cut
**Date:** 2026-10-24. **Owner:** draft Agda PR #1248. **Sibling math:** dashi_lean4 PR #85 (finite Fock channel). No claim of new full four-dimensional Einstein–Maxwell–Dirac solution or Lean/Agda kernel certificate.

## Executive correction

The repository already has a considerable Cauchy stack. However, it includes *different mathematical meanings* of Cauchy. Our earlier roadmap mistakenly made the **compactness of the Cauchy slice in one useful 2025 propagator construction** look like a universal obstacle to global Dirac Hadamard states. Two ORIGINAL sources discharge that broad objection:

- **Capoferri–Murro (2025), Remark 3.8(2)**: a compactly supported Dirac Cauchy datum on a noncompact globally hyperbolic slice, over a **bounded time interval**, is handled by doubling a relatively compact neighbourhood of its full finite-time causal hull. Finite propagation and Cauchy uniqueness identify local solutions. This is a finite-time/local-data reduction, not a global compactification of the spacetime or its nonlocal Casimir state.
- **Christian Gérard–Théo Stoskopf (2022)**: a pure free Dirac Hadamard state can be constructed in their bounded-geometry regime; the same work gives two general constructions for **arbitrary globally hyperbolic spin spacetimes**. Thus free-state EXISTENCE can be imported at its true hypothesis/scope even for noncompact Cauchy surfaces. That does NOT select a charged, topologically nontrivial magnetic Wilson-loop state with the **negative** stress required by MMP. Extension to the specified charged twisted spin-c bundle and state remains a same-object proof task, not an assumed corollary.

**External theorem ownership:** Original source claims remain original authors' theorems. DASHI additions here are a proof-carrying conditional Agda interface and independently executed *restricted toy* calculations.

## Actual repository prior-art inventory

| In-repo owner | Native statement/status | What is legitimately reusable |
|---|---|---|
| `DASHI/Geometry/LCP/Cauchy.agda`, `Limit.agda`, `Banach.agda` | explicit constructive modulus `CauchyMod`, prefix-stream convergence and fixed-point theory | finite iteration/analytic Cauchy bookkeeping **only**, not Lorentzian hypersurfaces |
| `DASHI/Analysis/BishopFastCauchyCommonCompletionExact.agda`, `MarxFastCauchyCompletionCutset` | rational real completions / setoid/back-end and conditional representation bridges | convergence/analytic scalar model, not Dirac propagation |
| `DASHI/Physics/Gravity/PenroseGlobalCausalityAuthorityExact.agda` (merged Agda #898; follow-on #905) | Minguzzi (2019) Prop. 2.143, Thm 6.23/6.25 noncompact Cauchy, global causal horismos authority; explicitly no internal continuum causality reproof | **native Cauchy-hypersurface/source-attribution owner** |
| `DASHI/Physics/Gravity/PenroseGlobalHorismosContradictionExact.agda`, `Penrose1965NullGeodesicIncompletenessExact.agda` | same-object global causal/topological contradiction and correct Penrose 1965 theorem boundary | global-causality typed input; do not promote noncompact Cauchy into an actual constructed Lorentzian metric |
| `DASHI/Physics/QFT/AQFTCarrierAlgebraQuotientSurface.agda` | Cauchy evolution / algebra time-slice **target only** with explicitly missing domain-of-dependence, actual isomorphism and descent compatibility | precise receiving API for Dirac local well-posedness and future AQFT time-slice proof |
| `DASHI/Physics/Closure/CarrierSchwingerFunctionCauchyReceipt.agda` | finite carrier-norm Schwinger Cauchy receipt; exact numeric inequality and distribution/Gate3 lift explicitly unavailable | analogous field correlator convergence bookkeeping, **not** Wightman/Dirac microlocal spectrum |
| `DASHI/Physics/FiniteToContinuumGeometry.agda` | continuum geometry via explicitly PROVIDED metric/connection/refinement compatible bridge | source contracts only, **not** geometric manifold existence |
| Lean `QuantumMereologyFiniteSubsetMarginal`, `PartialTraceCoherence` (merged #61/#76) | finite selected density state / trace associativity | receiver/environment state comparison, not curved-spacetime Hadamard proof |

New Agda module `DASHI/Physics/QFT/MMPDiracCauchyNoncompactCompactDoubleBidiExact.agda` imports the **actual named Cauchy, Lorentzian and AQFT owners** and constructs a conditional finite-time double reduction. It explicitly proves that the same LOCAL observations agree when (i) compact support and finite causal hull are supplied, (ii) local data are matched across the collar, and (iii) hyperbolic Cauchy uniqueness on the actual operator is supplied. Those hypotheses are FIELDS, not anonymously asserted new theorems.

## Concrete *topological and causal background existence* cut

Consider the SAME-UNIVERSE spatial handle
```
Sigma = (S^1 × S^2) \ {point} = R^3 # (S^1 × S^2).
```

- One noncompact asymptotic end, with a nonseparating throat S², and `H_1(Sigma;Z)=Z`, `H_2(Sigma;Z)=Z`. Remove an interior point of the 3-cell from the standard CW model for S¹×S²; the punctured manifold retracts onto its 2-skeleton `S¹∨S²`. Its cellular chain boundaries in dimensions 1,2 vanish. This is standard cellular homology / Poincaré duality, not a novel DASHI theorem.
- Take the compact core `(S¹×S²)\open B³`, attach the unique asymptotically Euclidean exterior `R³\B³` through an S² collar. Choose an arbitrary smooth positive Riemannian metric on the core and interpolate to exactly Euclidean on the exterior. This is a complete Riemannian metric `h`. More generally, Katsumi Nomizu–Hideki Ozeki (1961) prove any connected second-countable smooth manifold admits some complete metric; their existence theorem does not itself guarantee the specific Einstein or Maxwell dynamics.
- Define `M=R_t×Sigma`, `g=-dt²+h`. By the standard **ultrastatic complete-slice theorem**, every `t=const` is a noncompact Cauchy hypersurface and the metric is globally hyperbolic. This supplies an actual *admissible kinematical background family*, **not** a solution of the Einstein equations. Cite Geroch/Bernal–Sánchez for general splitting; construction here runs the argument in the reverse direction.
- The orientable 3-manifold is spin, hence the ultrastatic product has a spin structure. `H²(Sigma;Z)=Z` admits charged U1 line bundles with first Chern class `q∈Z`. There is no global smooth vector potential 1-form if q is nonzero; choose gauge patches/connections.

**Explicit smooth magnetic-flux source on that topology (DASHI toy construction):**

Pick an embedded closed `S¹` core loop `gamma` representing the H1 generator and its product tubular neighbourhood `S¹_theta×D²_(x,y)`. In it put
```
F = c_q * phi(r) dx ∧ dy,
phi(r)=exp[-1/(1−r²)] for r<1, zero for r≥1,
c_q = q / integral_0^1 phi(r) r dr.
```
Extend F by zero outside the tube. This F is smooth and **closed** (`dF=0`). The relative/transverse flux is `∫D²F=2πq`. By the Thom/Poincaré-dual construction, a spanning S² dual to gamma satisfies `(1/2π)∫S²F=q`. In a local product metric `dtheta²+dx²+dy²`, the magnetic vector field `*F` is along `∂theta`, giving **actual closed magnetic field lines** in that tube through the handle. The magnetic U1 class is integral.

**Separate cohomology classes control return-loop quantum state.** On this same handle, spin structures form a torsor over `H¹(Sigma;Z₂)=Z₂`, so periodic/antiperiodic spin phases around the S¹ generator are selectable. Flat U1 connections form `H¹(Sigma;U1)=U1`; their Wilson phase `exp(2πi α_flat)` around the noncontractible S¹ can vary **even when the magnetic first Chern class q∈H²(Sigma;Z) is fixed**. The charged fermion's 1+1D circle parameter is the combined phase `α=α_spin+α_flat (mod 1)`; the established Bernoulli Casimir `B₂(α)=α²−α+1/6` has `B₂(1/2)=−1/12` (antiperiodic choice) but `B₂(1/6)=B₂(5/6)=+1/36` after ±1/3 *flat holonomy*. Thus q=12/24 does NOT select negative quantum energy on its own, nor does magnetic helicity imply a Wilson holonomy. A physical spin-c operator, gauge reference and quantum state must actually realize the selected α. The second numeric fixture now evaluates these independent parameters for q=2,12,24, with identical Bernoulli results at the same spin/holonomy values. The Casimir formula remains a **1+1D model**, not a 4D source-derived stress calculation.

This has a better physical distinction than merely stating that the two-ended `R×S²` has H₂=Z. It constructs a mathematically consistent ONE-exterior handle, nontrivial magnetic flux, and closed returning field lines on the SAME spatial topology.

**Nonpromotion:** `dF=0` (no magnetic monopoles) is *not* the other Maxwell equation `d *_{4D}F = J` (which may need real matter current to sustain the local Thom profile). The chosen ultrastatic product generally has `G_mu_nu ≠ 8πG(T_EM+<T_Dirac>)`; it may need exotic matter for a static traversable handle. The compact double from the PDE method is **not** this actual physical handle. External existence of SOME free Hadamard state does NOT give the specific magnetically twisted NS fermion state with negative Casimir energy, or its local-covariant stress-current on the same metric. No horizon/chronology/stability/renormalization claim is paid.

Executable `scripts/check_mmp_cauchy_handle_thom_flux_20261024.py` tests the 2-skeleton CW matrices, closed-form longitudinal `dF=0`, transverse smooth Thom-normalization integral and closed S¹ loops for `q={0,1,2,12,24,-3}`. Local Python PASS; q12 numerical Chern ≈11.99999999999994. This is a **test of the construction**, not a formal proof of three-manifold topology or four-dimensional Einstein theory.

## Independent finite-time Cauchy-doubling reproducibility check

`scripts/check_mmp_cauchy_compact_doubling_20261024.py` implements a **massless 1+1D chiral Dirac equation** on `R` and a doubled finite spatial interval (circle), initialized with a smooth compactly supported function. In the safe causal diamond with collar radius R=10, support radius a=1.6, observed radius b=2.4 and |t|≤5, `R-a-b-|t|≥1`. Exact analytic translations `f(x∓t)` and their periodic image sums coincide on the observed region; the same finite-mode two-point kernels are equal. The local executed source-equivalent script gives difference 0 to floating precision, and an adversarial observation after gluing shows mismatch ≈e^-1≈0.3678794412. This is a useful negative control preventing incorrect *global* equivalence promotion.

No full 4D twisted-spin-c propagation, microlocal wavefront-set test or CAR state/Hadamard proof is furnished by this 1+1 calculation; the finite-rank mode kernel is only a bounded covariance-like fixture. It has **no claim** to be a complete renormalized Hadamard two-point distribution.

## Correct source/scope attribution

Original literature roots to retain and not double-count:

1. C. W. **Misner** & J. A. **Wheeler**, *Classical Physics as Geometry*, *Annals of Physics* 2 (1957) 525–603, DOI 10.1016/0003-4916(57)90049-0: original 'charge without charge' field/topology motivation; not invented in this repo.
2. Katsumi **Nomizu** & Hideki **Ozeki**, *The Existence of Complete Riemannian Metrics*, Proc. AMS 12 (1961) 889–891, DOI 10.1090/S0002-9939-1961-0133785-8: complete metric existence.
3. R. **Geroch** (1970) globally hyperbolic/Cauchy equivalence; Antonio N. **Bernal** & Miguel **Sánchez** (2003/2004), DOI 10.1007/s00220-003-0982-6 and arXiv gr-qc/0401112: smooth Cauchy foliation/splitting. Eduardo **Minguzzi** (2019) *Lorentzian causality theory*, DOI 10.1007/s41114-019-0019-x: external theorem coordinates already recorded by in-repo Agda #898/#905.
4. Christian **Gérard** & Théo **Stoskopf**, *Hadamard States for Quantized Dirac Fields on Lorentzian Manifolds of Bounded Geometry*, *Rev. Math. Phys.* 34 (2022) 2250008, DOI 10.1142/S0129055X22500088: GENERAL free spin Dirac Hadamard existence, not actual MMP state or its charged twist.
5. Matteo **Capoferri** & Simone **Murro**, *Global and microlocal aspects of Dirac operators: Propagators and Hadamard states*, *Math. Nachr.* 298 (2025) 2942–2974, DOI 10.1002/mana.12032: Cauchy-compact oscillatory/Feynman propagators and **Remark 3.8(2) finite-time compact doubling** for noncompact compact-support Cauchy problems.
6. Nicoló **Drago**, Nicolas **Ginoux**, Simone **Murro**, *Møller operators and Hadamard states for Dirac fields with MIT boundary conditions*, *Documenta Math.* 27 (2022) 1693–1737, DOI 10.4171/DM/X16: boundary-corrected Cauchy/Møller source, only if an actual timelike physical boundary is introduced.
7. Jochen **Zahn** (2014), DOI 10.1142/S0129055X13300124: local-covariant charged Dirac renormalization, conserved current/stress, ambiguity.
8. Juan **Maldacena**, Alexey **Milekhin**, Fedor **Popov**, arXiv:1807.04726 (2018), CQG (2023), original *four-dimensional charged-fermion magnetically supported* wormhole. Do NOT transfer proofs from a different toy geometry into their physical state.

## Revised phase status: precise cut

| Phase | Actual result | Current unclosed primitive |
|---|---|---|
| P0 kinematical topology | **Existing external topology and ultrastatic theorems + new explicit smooth closed-loop magnetic 2-form.** Source-specific finite verification; no 4D Einstein solution. | Physical same-object gauge connection and spatial metric with real source/current, geometry constraints |
| P0 local Cauchy evolution | **Compact support finite-time double mechanism SOURCE-PAID by Capoferri–Murro** and local 1+1 exact translation fixture | 4D charged twisted operator and causal collar / locality with the actual handle background |
| P1a free spin Hadamard existence | **Externally established** under global hyperbolicity/spin premises by Gérard–Stoskopf; cannot represent as DASHI proof | Actual twisted spin-c bundle/connection applicability and explicit selected state/covariances |
| P1b selected MMP fermionic state | OPEN | A coherent global closed-return fermionic NS/Wilson state whose renormalized `<T_mu_nu>,<J_mu>` follows from one Hadamard two-point function, with finite counterterm scheme and correct Ward identities |
| P2 Einstein/Maxwell coupled source | OPEN | Solve `G=8πG(T_EM+<T>_ren)`, `dF=0`, `d*F=*J` simultaneously on same geometry; no arbitrary pressure-zero QFT shutoff |
| P3Q channel | Existing fixed-charge dual-rail/coherent info numerics only | actual 4D mode/wavepacket scattering and environmental loss + causal arrival from P1/P2 |
| P4 3 real plasma regions | separate smooth EM field surrogates only | physical Maxwell–MHD currents and reproducible effect on same fermion state and stress |

**Pareto next task:** adapt an actual **charged twisted spin-c Dirac Cauchy evolution** to the constructed *asymptotically flat one-end handle* and its compact double, provide one explicit quasifree covariance satisfying microlocal Hadamard conditions and the charged Ward identities, then integrate into Maxwell/Einstein. Do NOT spend a new cycle re-proving constructive stream Cauchy moduli or re-creating Lorentzian Cauchy ontology already present in the repo.

## Acceptance

```sh
python3 scripts/check_mmp_cauchy_compact_doubling_20261024.py
python3 scripts/check_mmp_cauchy_handle_thom_flux_20261024.py
# Source-written typed owner (Agda CLI/kernel availability to be assessed):
agda -i . -i ~/.agda/libraries/standard-library/src \
   DASHI/Physics/QFT/MMPDiracCauchyNoncompactCompactDoubleBidiExact.agda
```

The two locally equivalent numerical fixtures PASSED on 2026-10-24. Neither source-written exact GitHub-head Agda kernel/CI run nor any physical MMP wormhole solution is claimed.
