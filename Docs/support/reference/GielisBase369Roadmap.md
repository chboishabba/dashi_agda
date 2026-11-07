# Gielis × Base369 — exact phased max-cut roadmap

**Status:** active, PR [#1466](https://github.com/chboishabba/dashi_agda/pull/1466) (draft);
**source level:** G01/G02 finite source plus G06 refinement source written, not
Agda-kernel accepted here; Python exact arithmetic executable but committed
branch regression harness not run in this authoring environment. Never call
source-written/type-unchecked source a Golden proof.

**Primary formal record:** [GielisBase369Cut.md](GielisBase369Cut.md).
**Mathematical proof notebook:** [GielisBase369ProofTheorems.md](GielisBase369ProofTheorems.md) (E01–E35), with strictly separated native/empirical acceptance.
**Original author:** Johan Gielis, 2003, DOI 10.3732/ajb.90.3.333.
The selected exact *special case*, independent of its numerical experiments:

    r_m(theta)=2/sqrt(3+cos(m theta))
    r_m(theta)^(-2)=3/4+cos(m theta)/4.

Here m∈positive integers. eps≠1 in the spiral sweep is a *new controlled
deformation*, not a claim of a Gielis-law solution or a Tesla 369 law.

## Prior-art owners: USE THESE, DO NOT DUPLICATE

| Concept | Original canonical owner | Reuse obligation |
|---|---|---|
| C3, C6, C9, C18 refinements | `DASHI/Foundations/Base369CirclePhase.agda` | phase indexing, C18 source |
| C3→C9→C27 tower and 27/729 | `Base369TriadicPhaseTower.agda`, `Base369Ternary27HypervoxelFabricGeometryExact.agda` | retain difference C27 ≠ C3³ |
| Dihedral rotation/reflection | `DASHI/Biology/Physical/DNAHelixDihedralExact.agda`; `DASHI/ComputerScience/BalancedTernaryC2C3DihedralCodecBridgeExact.agda` | use existing srs=r⁻¹ |
| SO(3), Hodge, oriented torque | `DASHI/Physics/Foundations/TorqueTrialectic369Exact.agda`, `ContinuousSO3Torque369BridgeExact.agda`, `R3HodgeCrossExact.agda` | typed r×F, orientation not magnitude |
| Finite Fourier inversion | `DASHI/Physics/Closure/NSTriadKNLuoFiniteFourierInversionFromResolutionExact.agda`, `DASHI/Biology/Physical/C3CubeCyclotomicFourierExact.agda` | borrow existing resolution and cyclotomic carriers |
| Nyquist / resolution / aliasing | `DASHI/Cognition/PNF/SemanticSamplingLookupGeometry.agda`; `DASHI/Physics/Closure/Gate3PrunedUnionDensityReceipt.agda` | maintain distinction between sampling theorem and resolution analogy |
| Shannon information and codes | `DASHI/Biology/Levin/ShannonInformationEntropyBoundary.agda`, `PrefixFreeCodingBoundary.agda` | no Shannon optimality without probability/code witness |
| Kolmogorov/MDL | `DASHI/Foundations/Base369EngineeringMDL.agda`; `DASHI/Core/MultiscaleMDL.agda` | operational code-length/costs, not claimed true universal K |
| Exact SI dimensions and metrology | `DASHI/Physics/Units/SI.agda`; `SIMetrologyBridge.agda`; `MechanicalDimensionExact.agda`; `YangMillsSIScalingEndpointExact.agda` | typed W, N, N m, J, angular impulse; nominal roles and SI authority separate |
| Exact SI c carrier | `DASHI/Promotion/SIExactConstantParsedCarrierRequest.agda` | canonical c=299792458 m/s; no duplicate untyped numerical literal |
| Perron/finite nonnegative matrices | `DASHI/Physics/YangMills/BalabanFiniteInfluenceRowMassPowerExact.agda`, `BalabanFiniteWeightedInfluencePowerExact.agda`, `BalabanClayUniformPerronContractionExact.agda` | reuse finite row/power bounds, cone uniformity; E17 rational positive-vector spectral certificate remains specific |
| Collatz naming boundary | `DASHI/Core/FiniteTypedBranchingKernelExact.agda` plus Collatz/Syracuse dynamics owners | do not confuse Collatz iteration with Collatz–Wielandt; full generic spectral radius theorem not represented as verified here |
| Log-polar/exponential spiral | `DASHI/Cognition/AnalyticLogPolarSpiralCompilerExact.agda`, `DASHI/Analysis/ConstructiveRealSpine.agda` | reuse the actual log/exp construction |
| Concrete Bishop trig | `DASHI/Analysis/BishopConcreteTrigAnalyticTermDerivativeExact.agda` and Bishop sine/cosine sources | same-object native trig, no terminal singleton replacement |
| Geometric SOTA baseline | Gielis shape/PDE literature plus freeform optics | compare against non-369 m, splines, splines/ellipses/other reflectors |

**Kozyrev naming collision:** p-adic Kozyrev wavelets in the analysis/Clay
repository are not the ray-optics Kozyrev mirror simulator. The **legacy
optical mirror** is the earlier HTML SDF raymarcher/state machine, with
independent collision replay and torque logs. Its exact original repo/path
has now been located in original PR #1404 (head 337aabb, distinct open Git ref); its browser HTML event exports are NOT in this checkout. Require the exact original scene/interface,
not an invented identification. Prior audit reported first-hit
HTML-versus-independent intersection discrepancy ~1.349–1.832 mm and
a -195.58 micro-N m torque ranking **provisional**. This unresolved
geometry/collision-seam is an explicit blocker of same-apparatus claims.

## Phases, deliverables, exit criteria

| Phase | Deliverable | Explicit pass/fail exit | Status |
|---|---|---|---|
| P0 — Reuse and trust boundary | D0 owner map, provenance, fail-closed roadmap | No new duplicated Fourier/torque/spiral carriers; old versus new surfaces identified | source-written |
| P1 — Finite Golden | D1 kernel-accepted C18 Gram/dihedral and C36 aliasing | `scripts/check_gielis_base369_cut.sh`, `agda --safe` on ALL Golden roots, no holes | **OPEN: kernel check** |
| P2 — Same-object geometry | D2 continuous selected Gielis and Bishop/trig symmetry and area certificate | analytic identity, domain positivity/smoothness/area and 18/36 sample weld all native kernel-checked | **OPEN** |
| P3 — Finite/continuum spectral | D3 native exact Fourier projector and continuum spectral estimates | native algebra and complex Fourier; convergence/error proof or independently validated certified bounds | **OPEN** |
| P4 — Legacy-compatible optics | D4 normalized source+wall+ray+torque scene; D5 Pareto/null-control benchmark | first-hit parity tolerance quantified, original scene reproduced, non369 and freeform controls, impulse dimensions | **OPEN** |
| P5 — Real-world validation | D6 measurement report; D7 reusable inverse compiler and paper | controlled independent calibration, confidence intervals, replication; honest uncertainty | **OPEN** |

## Exact remaining lemmas / proof or acceptance leaves

States: **SOURCE** means text committed but no kernel receipt; **NUMERIC**
means computational test/design only; **OPEN** means original theorem unproved.

| ID | Exact target (proposed proof-owner name) | Requirement | Depends | State |
|---|---|---|---|---|
| G01 | `gielisFiniteKernelAccepted` | Native `--safe` on `GielisBase369FiniteExact`, `NyquistPhase36Exact`, `ExistingOwnersWeldExact`; no banned pragmas/holes | owners | SOURCE; kernel receipt OPEN |
| G02 | `sampledCosine369SameObject` | Prove for each 18-point index `2 cos(2π m j/18) = signal_m j` on *ordinary Bishop ℝ* for m=3,6,9 | G01, Bishop π/trig | E33 actual Bishop trig/complex value constructor and source-written reduction from ONE imaginary-axis complex exp multiplicativity; selected literal complex Cauchy series theorem OPEN |
| G03 | `gielisSpecialCaseIdentity` | Prove cos⁴x+sin⁴x=(3+cos4x)/4 on same ordinary real carrier; introduce sqrt and reciprocal | Bishop trig | E25/E29 E33 concrete Bishop Gielis quartic/quadruple-angle now reducible to shared Round11 Pythagorean + ONE imaginary exp additivity source; that complex analytic theorem and kernel OPEN |
| G04 | `gielisPositiveSmooth` | 1≤r≤√2; positive denominator, existence and continuous/differentiable radial graph, nondegenerate tangent | G03 | E33 source-native Bishop imaginary-axis multiplication reducer plus existing real expAdd; actual Bishop radial sqrt positivity and derivative/analytic source OPEN |
| G05 | `gielisCyclicDihedral` | Exact continuous rotation/reflection and compatibility with C18 maps; use existing dihedral owner | G02,G04 | Finite dihedral SOURCE and continuous paper theorem; Bishop same-object phase lift OPEN |
| G06 | `phaseGridAliasingBoundary` | At N=18 sin(9θ_j)=sin(27θ_j)=0; at N=36 sin9(θ_1)=+1, sin27(θ_1)=-1; no unjustified bandlimited theorem | G01 | Finite witness SOURCE; exact symbolic receipt; kernel OPEN |
| G07 | `finiteFourierProjector` | Native ℚ^18/finite-character linearity, idempotence, self-adjointness and `P_a P_b=P_lcm`; reuse finite Fourier inversion owner | G01 | E28 exact four-quarter m9 Fourier and E30 original-C3-derived six-phase CRT cyclotomic Fourier SOURCE; full 36-mode field/reconstruction OPEN |
| G08 | `gielisEqualArea` | Area=(1/2)∫₀²πr² dθ=√2π for all positive integer m; real periodic integration | G03,G04 | E03 exact area paper proof; Bishop polar integration, π and inverse/sqrt OPEN |
| G09 | `gielisNormalCurvature` | r,dr/dθ, outward unit normal, curvature and uniform nondegeneracy; prove smooth-curve equivalence | G04 | E04 normal/curvature paper proof; native Bishop derivative authority requires same-object weld |
| G10 | `complexFourierSameObject` | Complex characters, inversion/Parseval and oriented phase sector; account for m=9 Nyquist degeneracy | G06,G07 | E28 four-phase + E30 six-phase native Fourier roundtrips SOURCE, independently 625/729 exact vectors; original full C36 native field/DFT OPEN |
| G11 | `gielisDomainDirichlet` | Bounded Lipschitz/star-shaped Ω_m, Dirichlet self-adjoint -Δ, compact resolvent | G04,G09 | E35 exact area + Faber–Krahn all-m first continuum eigenvalue >224/55; E15 m3 upper <1273/264, E23 SI length scaling; full Bishop-native functional analysis still OPEN |
| G12 | `gielisDiscreteSpectrumConverges` | Consistent/boundary-correct finite difference or FE scheme, spectral nonpollution and quantitative error; 41/61 images insufficient | G11 | E31 exact rational unshrunken membership, E26 native finite graph algebra, E27 fixed-k continuum convergence on paper; E35 rigorous continuum lower >224/55; native Agda compactness/quantitative mesh error OPEN |
| G13 | `spiralBaselineSameObject` | Restore HTML SDF original scene/emitters/wall/aperture/forward ray intersection/absorber; exact collision replay comparison | actual legacy scene | PR #1404 ORIGINAL referee and RayLedger FOUND; epsilon=0 log centreline/normal-offset walls same-object E18; SHA-pinned cross-PR replay source COMMITTED; HTML SDF event parity OPEN |
| G14 | `polygonReflectionConverges` | For nongrazing hit/finite bounces establish polygon→smooth event/trajectory and torque convergence, with singular set handled | G09,G13 | Original PR #1404 first-forward geometry referee located, new-scene analytic hit convergence E16; SDF thickness and grazing/higher-hit acceptance OPEN |
| G15 | `physicalImpulseTorque` | Define optical momentum transfer, lever arm, time-power and units in SI; connect normalized impulse to existing SO(3) torque/Hodge | G13,G14 | E32 original signed ray r×(d_in−eta d_out) scalar lever algebra, right-hand rule, exact nominal SI torque magnitude SOURCE; original SI c reused; calibrated source inputs/hit geometry OPEN |
| G16 | `opticalParetoValidated` | Source-matched 369/non369/freeform controls; focus/impulse/energy objective directions, uncertainty/CI, calibration and replication | G13–G15 | E24 exact interval input uncertainty and E32 signed ray torque; model interval accepted, empirical independent uncertainty/measurement OPEN |
| G17 | `geometricInverseIdentifiability` | Parameter-to-boundary fitting with noise/MDL model class; equal-shape nonuniqueness or local full-rank identifiability | G04,G10 | E10 exact zero-modulation nonidentifiability; inverse estimation OPEN |
| G18 | `productSymmetry27Bridge` | Explicit product action for C3³ on 27 fibre states; distinguish C27 cyclic and prove projection/phase compatibility | tower+hyperfabric | E11 nonisomorphism C27 vs C3^3 proved; positive product bridge OPEN |
| G19 | `sampleRateShannonBoundary` | Selected spectral/bandlimited space, sample+reconstruction maps, threshold and aliasing/null counterexample; do not identify PNF query projection with a Shannon theorem | G06,G10 | E28 selected four-dimensional 9th-mode Fourier and E30 six-dimensional C6=C2×C3 exact transform SOURCE; full C36 36-character Agda scalar OPEN |
| G20 | `gielisMDLKolmogorovBoundary` | Reversible prefix-free Elias-gamma parameter codec; remaining residual, precision uncertainty, weighted physical cost, ordinary Kolmogorov/Shannon theorem boundaries | MDL+Shannon owners | E10 operational codec SOURCE; Kolmogorov/Shannon optimality OPEN |
| G21 | `gielisOpticalRunReceipt` | Direct run of **committed exact commit** script+test with provenance (toolchain/hash/seed/geometry), not the older standalone receipt | G13 optional for exploratory run, needed for sameness | E01–E35 mathematical ledger, thirteen native Agda Gielis roots registered in parallel checker; source written, Agda kernel receipt OPEN; CI/HTML out of scope |

## Critical dependencies / max-cut

- **Shortest formal cut:** G01 → G06 and G02 → G03 → G04 → G08.
- **Finite Fourier cut:** G01 + G06 → G07 → G10 → G19.
- **Engineering cut:** G13 → G14 → G15 → G16, with G21 as
  reproducibility gate. No need to block finite formal work on physical
  apparatus measurements.
- **High-alpha reuse:** G20 ← Shannon/MDL owners; G18 ← existing 27/729
  fabric. Neither can be 'proved' from mere matching cardinalities.

## Reproducibility protocol

    scripts/check_gielis_base369_cut.sh
    python -m pytest -q tests/test_gielis_base369_experiments.py
    python scripts/gielis_base369_experiments.py --pde --optics \
      --rays 720 --segments 1536 --bounces 8 --controls \
      --torque-objective min --output /tmp/gielis_369_new.json
    python scripts/gielis_base369_experiments.py --optics \
      --rays 720 --segments 1536 --bounces 8 --controls \
      --torque-objective max --output /tmp/gielis_369_torque_max.json

These are **commands to run**, not claims that checks have been run.
Normalised angular impulse has units metre × *unit momentum*, not
Newton metre torque. A low-cost/high-focus design and a high-impulse design
require different objective directions. The optical scene currently uses
an open 1.5-turn logarithmic spiral envelope and does not possess a global
C_m rotation symmetry despite its m-fold angular modulation.

## World-model/physical promotion criteria

- **PNF:** candidate, simulation receipt, observation, uncertainty, and
  measured physical mechanism must be distinct statement types.
- **SOTA:** report Gielis prior art, Fourier/dihedral classical theorems,
  same-area comparison, null controls m=4/5/7, non-Gielis freeforms.
- **No promotion:** 369 numerology; universal Tesla claim; p-adic Kozyrev
  wavelets = optical Kozyrev mirrors; singleton-real model = Bishop ℝ;
  finite Fourier → 4D Yang–Mills/NS/Monster physical claim; reflection
  proxy = measured torque; Python smoke test = Agda kernel acceptance.


## 2026-11-06 follow-up: Kolmogorov, Shannon and computational MDL

The Python optics sweep now carries a concrete `model_code_bits` field,
computed by `model_encode`/`model_decode`, not a guessed entropy:
one baseline bit for any eps=0 log spiral, otherwise one modulation tag
plus two Elias-gamma positive-integer codes for m and (1+1000*eps).
Only millistep eps in [0,0.45] is admitted. Roundtrip and sample
prefix-free regression are included. This is a description length for an
**explicit program language**, not universal Kolmogorov complexity K(x).
No Shannon source-distribution or rate-distortion optimum is asserted.

There is a second, distinct 'Kolmogorov' owner in turbulence:
`DASHI/Physics/Closure/NSCarrierKolmogorovSerrinReceipt.agda`.
Its cascade/length-scale semantics cannot be identified with algorithmic
information theory, and neither yields a measured optical performance
advantage without a field/source model. Do not mix these three meanings.

The 18→36 proof is specifically a discrete two-mode aliasing counterexample.
It does not prove continuous Nyquist-Shannon sampling/reconstruction or
selected MSE bounds. Those are independent G19 obligations.


## 2026-11-06 proof-round receipts and corrected physical sign

- Independent exact local SymPy check passed: special-case trig polynomial,
  ordinary-real radial derivatives/curvature, area = sqrt(2)*pi, and the
  algebraic ray-wall angular-impulse conservation relation. Its local artifact
  is a symbolic check, **not** an Agda proof acceptance receipt.
- `scripts/gielis_base369_symbolic_certificates.py` added for head-commit
  symbolic reproduction; pytest invokes it when SymPy is installed.
- Optical ray tracer now records `wall_unit_impulse = d_in - d_out` and
  `ray_angular_change = -(wall_unit_impulse)`. The earlier code used ray-side
  sign while calling the output 'torque'. The new measured wall torque
  conversion is **conditional**: for power P and equal-power rays,
  τ = (P/c) mean[summed r × (d_in-d_out)] in N m. It is not a physical
  calibration or an apparatus measurement.
- The paper-level mathematical results include a strict nonconvexity
  obstruction κ_m(0) = 1 - m²/8 for m ∈ {3,6,9}, strict Faber–Krahn lower
  bound j_{0,1}²/sqrt(2) < λ₁(Ω_m), and exact 36-grid DFT reconstruction
  for the selected 7-dimensional bandlimited space. No mesh error theorem
  or native formalisation is promoted.
- User request to 'complete all' cannot turn missing original optical
  scene/experiments, native Agda checks, or continuum numerical error bounds
  into proof terms. These remain listed above as OPEN acceptance leaves.


## 2026-11-06 exact-head source-enumeration audit

\`scripts/gielis_base369_source_audit.py\` now parses the **literal**
Agda tables and 18-case proof declarations, with no third-party
dependency. An independent connector-side computation on the committed
Agda source blobs (see GitHub file SHAs in repo) checked **648 finite
cases**, including 19 named theorem clause sets of 18 cases each,
literal 3/6/9 signature values, rotation/reflection invariance,
the full Gram diagonal, 18→36 aliasing and separation, and G01–G21
roadmap coverage. The executable source-audit script is wired into
\`scripts/check_gielis_base369_cut.sh\` and pytest.

**Interpretation:** source enumeration shows no missing listed cases.
It does not check that those Agda equations type-check, that the
imported proof owners are \`--safe\`, or that continuous Bishop-real
realization is constructed. **G01 remains OPEN until an actual
\`agda --safe\` kernel receipt at the exact head.**

\`Docs/support/reference/GielisBase369ProofTheorems.md\` records
paper-level E01–E11 proof details and the admissible conditional
theorems; ordinary-real Agda proof terms and physical observation
are separate acceptances.


## November 6 proof round: E12–E16, phase and deliverable advancement

Concrete mathematical and executable advances:

- E12: Native Bishop Real universal quartic polynomial normal form, source-written using the existing Bishop ring solver. Actual Bishop trigonometric Pythagorean and quadruple-angle and pi proof terms still OPEN; no claim of Agda kernel success.
- E13: Exact rational cyclotomic field Q(zeta36), 1296 Fourier-character orthogonality pairs and seven-mode 36-point reconstruction passed independent local execution. Native Agda complex Fourier instantiation OPEN.
- E14: Rigorous all-eigenvalue continuum sector-domain relative error inequality, eps=55*m/(49*N), (1+eps)^(-2) <= lambda_k(sector)/lambda_k(smooth) <= (1-eps)^(-2). Local rational m=9,N=2048 certificate gives max error 0.993875%; Cartesian finite-difference solver numerical error remains OPEN.
- E15: Explicit continuum Rayleigh–Ritz spectral first-eigenvalue upper bound lambda1(Omega3)<1273/264=4.82196969... by an H0^1 radial trial function; local SymPy exact integration passed.
- E16: Independent analytic-first-hit versus polygon-first-hit validation on the NEW open log-Gielis spiral. A local independent 80-ray run found maximum 384-segment discrepancy 0.00022293 m, versus 1536-segment discrepancy 0.00001249 m, factor 17.85. The original HTML Kozyrev SDF scene remains unavailable and same-object legacy G13 is OPEN.
- E16: Matched pseudo-random uniform ray source plus familywise Hoeffding intervals for focus and angular impulse, conditional on IID uniform source directions and bounded bounces. This cannot calibrate optical power or provide measured uncertainty for the older deterministic grid.

New source files:

    DASHI/Geometry/GielisBishopPolynomialExact.agda
    scripts/gielis_cyclotomic36_exact.py
    scripts/gielis_sector_spectral_certificate.py
    scripts/gielis_rayleigh_spectral_bound.py
    scripts/gielis_reflection_parity.py
    scripts/gielis_optical_statistics.py

**Phase/deliverable acceptance:** P2 ordinary mathematics advanced but Bishop Golden D2 OPEN; P3 exact Fourier and continuum sector spectral D3 subcertificates completed, full Cartesian finite-difference D3 OPEN; P4 new-scene collision and conditional statistics D4/D5 implemented, original-scene parity and physical calibration OPEN; P5 D6/D7 measurements/replication/publication OPEN. No P2–P5 blanket completion claim.

Verification commands (these are instructions, NOT exact-head test receipts):

    python scripts/gielis_cyclotomic36_exact.py
    python scripts/gielis_sector_spectral_certificate.py --m 9 --sectors 2048
    python scripts/gielis_rayleigh_spectral_bound.py
    python scripts/gielis_reflection_parity.py --m 3 --epsilon .12 --rays 48
    python scripts/gielis_optical_statistics.py --rays 720 --seed 369
    scripts/check_gielis_base369_cut.sh

Exact remaining native/empirical leaf list is the G01–G21 table above. Technical E01–E16 mathematical proofs and their nonpromotion conditions live in GielisBase369ProofTheorems.md.

### Crucial P2 existing owner: shared Round11 same-object trig weld

The source DASHI/Analysis/BishopRound11ClassicalTrigObjectWeldExact.agda already packages **one same-object identification** that, when furnished, transports BOTH classical DLMF sine/cosine Pythagorean and the Bishop analytic derivative source to the literal Round11 Bishop functions. The owner's canonical status explicitly has sameTrigObjectWeldClosed=false. Do not duplicate Pythagorean as an unattested Gielis-specific axiom. New GielisBishopPolynomialExact.agda now calls Shared.compileRound11Pythagorean using an actual shared weld witness W, and uses the real BishopP ring solver for the universal polynomial identity. G03 still needs the quadruple-angle producer and the same-object square-root/canonical pi phase. Conditional transport is not proof that W exists.

### Exact G13 original optical replay artifact identifiers

Historical independent first-forward audit records 132/132 intersecting rays, with median/max positional differences: Archimedean 1.414/1.499 mm, logarithmic 1.729/1.832 mm, segmented 1.349/1.431 mm. The HTML event solver used distance-to-stroked-wall geometry while the independent solver used normal-offset finite wall thickness. The original files were named spiral_raymarch_collision_export_forward.html, spiral_collision_events_forward.json and referee_spiral_events.py (and a kozyrev_first_forward_audit_bundle.zip artifact); their bytes are not present in the connected repo/Library sources available in this round. A first-hit convergence study on a DIFFERENT new analytic scene cannot close the original thickness-semantics mismatch. The 2026-10-28 log-spiral torque value -195.58 microN m remains provisional until that precise original replay is recovered and parity demonstrated.


## 2026-11-06 additional max-cut: original Kozyrev reuse + finite raster spectral proof

Original canonical sources now FOUND in [Kozyrev PR #1404](https://github.com/chboishabba/dashi_agda/pull/1404): `scripts/kozyrev_first_forward_intersection_referee.py`, `scripts/kozyrev_optical_event_ledger.py`, `scripts/kozyrev_matched_envelope_html.py`, `scripts/kozyrev_html_family_ternary_runner.py`, and `scripts/kozyrev_geometry_optimizer.py`. Do not describe the original PR as unidentified or duplicate its independent normal-offset physics owners. The browser HTML file and recorded actual event JSON are still absent from this branch.

| Extra subdeliverable | New acceptance | Current status |
|---|---|---|
| G12a original raster FD first eigenvalue | E17 exact-rational Perron–Frobenius/Collatz–Wielandt upper/lower bracket for the actual 4-minus-adjacency five-point matrix; check 3/6/9 on n41 and 3 on n61 | **MATHEMATICS CLOSED**, independent local rationals tested; committed-head replay pending |
| G12b FD-to-continuum | Prove Cartesian raster Dirichlet eigenvalue convergence including cut-cell boundary and numeric error | OPEN; the E14 angular-sector domain bound is distinct |
| G13a same logarithmic centreline | E18 prove Gielis epsilon-zero curve exactly equals the PR #1404 log family after matching inner=.75, outer=1.55, turns=1.5 and growth=log(1.55/.75)/(3pi) | MATHEMATICS CLOSED |
| G13b normal-offset wall referee | Source- and blob-hash-pinned PR #1404 original first-forward referee, with same finite thickness, sidecaps, and 3mm gate | ADAPTER SOURCE COMMITTED; exact-head cross-PR execution pending |
| G13c original HTML SDF parity | Recover actual browser HTML and JSON, reconcile stroked-SDF versus normal-offset wall geometry, verify 132/132 rays and higher bounces | OPEN |
| G15a physical angular-impulse convention | Import original PR #1404 RayLedger and compare identical event, power, reflectivity, momentum and torque | SOURCE-WRITTEN; original physical measurement not implied |
| G15b classical maximum radiation-pressure torque | E19 exact rational bound abs(tau) <= (P*R/c)(1+eta)*sum(eta^k,k=0..B-1) <= 2PRB/c | MATHEMATICS CLOSED and executable source; independent calibration OPEN |
| G16a paired random-angle model | Simultaneous Hoeffding focus/abs-impulse *paired differences* against baseline across m3/6/9 and m4/5/7 controls | CONDITIONAL MODEL PROOF, CODE SOURCE; experimental CI OPEN |

**Verification without Nix:** scripts/check_gielis_base369_cut.sh uses the repository's run_agda29_parallel_check.sh --safe. For source-pinned PR #1404 referee/ledger replay, export `KOZYREV_PR1404_DIR` pointing to a local checkout's `scripts` folder. The bridge rejects missing or mismatched original Git object blobs (SHA-1). This is optional on the general maths checker, but **mandatory** to claim G13b closed. Original HTML SDF parity is a separate G13c producer.

**Primary proof note**: [GielisBase369ProofTheorems.md](GielisBase369ProofTheorems.md), sections E01–E19. These are partial original acceptance closures, not a blanket discharge of P2/P3/P4/P5.


### Exact PR #1404 original-owner replay command

```bash
bash scripts/check_gielis_kozyrev_pr1404_original.sh --fetch
```

This uses Git objects from the **open original PR #1404**, verifies
the canonical Git blob hashes of both the original first-forward
referee and `RayLedger`, materializes them outside the working
tree, and runs the new baseline and finite-thickness normal-offset
geometry parity tests. It has no Nix/Chrome/terminal scraping
dependency. Network fetching is explicit only with `--fetch`.
The command is documented, **not claimed to have run in this
authoring environment**.

Once this command passes, mark **G13b reference-wall parity**
accepted. Do *not* promote G13c original HTML SDF or its
132-ray actual collision export without that separate evidence.


## Current narrow max-cut: already existing SI + Perron donors (2026-11-06)

**User scope change:** CI and historical HTML SDF replay are **DEFERRED
from this round's active work**, not deleted from the research record.
Work now prioritises direct native type transport and exact numerical
mathematics rather than new test infrastructure.

### Native owners consumed and concrete implementation

- `DASHI/Geometry/GielisSIPerronOwnerWeldExact.agda` (NEW)
  imports `SI`, `SIMetrologyBridge`, `MechanicalDimensionExact`,
  `YangMillsSIScalingEndpointExact`,
  `SIExactConstantParsedCarrierRequest`,
  `BalabanFiniteInfluenceRowMassPowerExact`, and the
  original R³ Hodge/SO3 torque owners.
- `speedOfLightIsExactSIInteger`: uses the existing canonical SI
  speed-of-light integer carrier, not another floating constant.
- `torqueFromPowerOverSpeedAndRadius` and
  `mechanicalOpticalTorqueIsSI`: exact mechanical dimension algebra
  \([P/c]R=M L^2T^{-2}\), derived on the existing M/L/T carrier and
  transported to the SI dimension vector.
- `RoleIndexedSIQuantity` and `OpticalMeasurement`: distinguish
  *torque N m* from *energy J* at the nominal-role level despite
  their equal SI dimensions, and retain the native uncertainty,
  source, version and decimal scale fields.
- `finiteInfluenceRowPowerBoundReuse`: direct application of
  the already existing theorem on the actual finite nonnegative
  matrix owner; no redundant finite-sum/distributive proof.
- `scripts/gielis_si_owner_adapter.py`: source-verified exact c and
  Power/Force/Energy exponent checks; both the existing Gielis
  ray model and rational torque envelope obtain the same value.
- All five Agda Gielis roots are now referenced by the existing
  parallel checker invocation. Source-written is **not** kernel
  acceptance.

### The correct Perron/Frobenius/Collatz division of labour

\[
 A_{m,n}=h^{-2}(4I-B),\quad
 \min_i\frac{4q_i-(Bq)_i}{h^2q_i}\le\lambda_1(A_{m,n})
 \le\max_i\frac{4q_i-(Bq)_i}{h^2q_i}.
\]

The lower/upper endpoints use the existing finite nonnegative-matrix
context and an exact *positive rational q*. They are already valid
via the classical Perron–Frobenius/Collatz–Wielandt theorem.
The *existing Agda sources found in the indexed repository* include
row-power and cone-contraction proofs, but do **not** expose a
kernel-accepted generic `CollatzWielandt` spectral-radius theorem.
The Collatz/Syracuse dynamics files refer to another mathematical
problem entirely. So this tranche **reuses** the real finite
row/power owners and keeps the generic spectral theorem distinct
from the exact-rational finite certificate; it neither invents
a new PF library nor promotes a statement-only interface.

### Exact remaining prioritized lemmas, excluding deferred CI/HTML

| Cut | Original source and target | Exact unfinished acceptance |
|---|---|---|
| SI1 | GielisSIPerronOwnerWeldExact on SI/Mechanical | Agda kernel acceptance of nominal role, exact c, and M/L/T→SI equations |
| SI2 | Native R³ Hodge and `RayLedger` | Same-source optical ray impulse × lever arm in selected typed magnitude and SI units, not merely dimension compatibility |
| PF1 | E17 rational FD and existing Balaban row/power owner | Native finite *specific* raster adjacency/positive-vector/row bounds if original Agda eigen proof is required |
| PF2 | Domain vs raster operators | Actual Cartesian FD-to-continuum error theorem; existing exact finite intervals do not prove convergence |
| BISHOP | G02–G05/G08–G09 | Round11 same-object sine/cosine/π/sqrt, analytic integration and kernel proofs |
| FOURIER | G07/G10/G19 | Native 36th-cyclotomic scalar and exact Fourier inversion with existing resolution owner |

**Explicitly deferred:** CI workflow and original HTML browser/132-ray
parity. The previously documented experimental calibration dependency
is unchanged: SI dimension proofs are not measured newton-metres.

**Proof details:** [E20–E21](GielisBase369ProofTheorems.md).


## 2026-11-06 latest exact SI/Bishop/spectral proof tranche E22–E26

**Six active golden-source dependencies now have concrete new producers:**

1. **SI dimension AND magnitude, E22:** Use the actual
   Mechanical.Quantity/multiplyQuantity to construct
   \(\tau=((P c^{-1})R)g\) and original mechanicalQuantityToSI
   to preserve its scalar value; \(g\) is a signed, dimensionless
   impact response, NOT inferred from SI. Distinct torque and
   energy roles remain intact.
2. **Physical spectral SI scaling, E23:** the new native
   GielisSpectralSIScaleExact source proves inverse-area units
   and typed rational magnitude scaling. The selected
   continuum m3 domain satisfies
   \(9/(4L_+^2)<\lambda_1(L\Omega_3)<
     1273/(264L_-^2)\;\mathrm{m}^{-2}\)
   for an assumed positive length interval. No wave speed,
   resonant frequency or measured physical device is invented.
3. **Optical input intervals, E24:** rational exact
   \(|\tau|\le(P_+R_+/c)(1+\eta_+)
   \sum_{k<B}\eta_+^k\), with valid \(\eta_+\le1\).
   Cancellation means the model's absolute lower bound is 0.
4. **Concrete Bishop configured trig, E25:** the actual
   GielisBishopPolynomialExact source derives
   \(4(\cos_B^4+\sin_B^4)\simeq3+\cos_B(4x)\)
   through the native ring solver, Pythagorean and
   quadruple-angle congruence. It is a **conditional theorem**
   on the same concrete Bishop functions. The true analytic
   Round11 quadruple-angle/same-object source and Agda kernel
   check remain OPEN.
5. **Finite raster positive-vector bound, E26:** derive
   the original lowest-eigenvalue enclosure directly from
   a symmetric-graph ground-state sum-of-squares identity,
   *without requiring a new PF or connectivity proof*.
   GielisFiniteGroundStateEdgeExact uses original ring,
   rational positivity and finite-sum owners for the general
   weighted-edge-list identity. The exact original raster
   calculator now checks additional rational vectors;
   120 independent exact rational graph/vector checks passed.
   Native full raster vertex assembly and FD-to-continuum remain OPEN.

**Actual source files this tranche:** GielisSpectralSIScaleExact.agda,
GielisFiniteGroundStateEdgeExact.agda, extensions to
GielisSIPerronOwnerWeldExact.agda and GielisBishopPolynomialExact.agda,
gielis_physical_spectral_si.py and gielis_si_optical_interval.py.
Existing canonical SI c, the MLT→SI bridge and original Balaban
Perron nonnegative-matrix owners are reused. Seven native
Gielis sources are now registered in the parallel checker.
No Agda kernel receipt is asserted.

**Remaining active MAX-CUT leaves (CI/HTML not in scope):**
G-BISHOP-A: original Round11 same-object sine/cosine and concrete
cosine doubling/quadrupling; G-BISHOP-B: canonical Bishop π,
sqrt reciprocal, differentiable radial star geometry and integral;
G-FOURIER: native \(C_{36}\) cyclotomic inversion on the original
Fourier-resolution operator; G-SPECTRAL: Agda specific raster
vertex/edge aggregation and Cartesian FD-to-continuum theorem;
G-SI-TRANSFER: original impact geometry \(r\times(d_{\rm in}-
\eta d_{\rm out})\) on the same typed SI magnitude and independently
calibrated inputs if a physical endpoint is asserted.


## Latest G12 producer: exact-target raster and qualitative spectral convergence (E27)

**Exact-target defect fixed:** The selected 5-point Dirichlet
finite-difference scripts previously used a FIXED normalized
radial inward tolerance 1e-12. As h→0 this selects a
different continuum domain, not literally the selected
unshrunken Gielis Ω_m. Both the actual PDE builder and its
exact rational eigenvalue referee now use

\[
 \delta(h)=\min(10^{-12},h^2),\qquad h=3/(n-1).
\]

For original n=41/n=61, this is exactly 1e-12, preserving
the original selected mask and earlier rational brackets.
For h→0 it tends to zero.

**Exact finite quadratic form identity**, including zero
extensions at EVERY exterior lattice site:

\[
 u^\top(4I-B_h)u =
 \sum_{i\in\mathbb Z^2}\sum_{j=1}^2
  (u_{i+e_j}-u_i)^2.
\]

The new scripts/gielis_fd_energy_mosco.py independently
checks this with integer/Fraction exact arithmetic for four
test vectors at each chosen original mask and verifies the
n41/n61 unchanged-mask property. E26 supplies the native
rational arbitrary finite-edge sum-of-squares donor.

**Paper mathematical theorem:** For every fixed k,
the idealized exact-radial-boundary Cartesian five-point
scheme with δ(h)→0 obeys
\(\lambda_k(A_h)\to\lambda_k(-\Delta_{D,\Omega_m})\).
E27 gives an explicit standard proof: smooth-test
recovery and Rayleigh limsup; finite-difference energy,
piecewise constant L2 reconstruction, bounded-support
Kolmogorov–Riesz compactness, H0¹ trace recovery,
and min-max liminf. This settles the qualitative
exact-boundary mathematical convergence cut.

**Still OPEN and not promoted:** Literal binary64 radial
evaluations have fixed machine error (no asymptotic
uniform guarantee); a validated numerical radial
predicate and quantitative n41/n61 continuum error
constant remain to be constructed, as does native
Agda compactness/raster-endpoint proof.
No fabricated result from the Yang–Mills Mosco
receipt modules, which themselves label recovery/liminf
as not constructed.

CI and historical HTML are deferred from the active cut.


## E28–E29 native exact Fourier/Bishop narrowing

**G07/G10/G19:** The existing Phase36 9th-mode Nyquist
witness has now been lifted into the nontrivial 4x4 rational
Fourier operator and its inverse on the actual chosen
quarter-wave samples, j=0,1,2,3.
GielisNineModeFourierExact.agda proves native
source-written coefficient and signal round trips
using coordinate extensionality and the original
rational ring solver. Original Q(zeta36) cyclotomic
arithmetic directly verifies the character rows
cos9=[1,0,-1,0], sin9=[0,1,0,-1], cos18=[1,-1,1,-1].
An independent exact Fraction cross-check enumerates
625 complete forward/inverse signal round trips.
The **selected m9 quarter-wave Fourier** is therefore
SOURCE-WRITTEN, not a blanket claim of a native
full 36-signal transform. Full C36 cyclotomic
native field and 36-character resolution remain
the exact unfinished G07/G10/G19 leaves.

**G03:** New BishopConcreteDoubleAngleInputs is
indexed by the identical original Bishop sine/cosine
dataset and angle. The reducer
bishopCosineQuadrupleFromTwoDoubleAngles transports
cos(2x), sin(2x) and cos(4x) doubling through native
Bishop congruence and the existing quartic solver.
bishopGielisFromPythagoreanAndTwoDoubleAngles
then proves the actual selected Gielis inverse-square
trigonometric numerator CONDITIONAL on those inputs.
The exact analytic remaining lemma is therefore the
Round11 selected source-native two-angle sine/cosine
addition/product-series identity (with 4x=2(2x)),
plus the pre-existing same-function classical/Bishop
identification, and kernel elaboration—not a
new standalone superformula trig axiom.

**Golden source implementation:** Eight Gielis Agda
roots are registered in scripts/check_gielis_base369_cut.sh
using the repository's parallel checker, alongside
the exact selected Q(zeta36) interoperability script.
The presence of source files does not constitute
an Agda kernel receipt.

**Still high-alpha:** Full original Bishop analytic
double-angle proof, actual C36 native scalar/DFT,
G12 original raster native compactness, and
calibrated optical SI magnitude transfer.
CI and historical HTML are out of current scope.


## E30 + E31 latest exact max-cut: native C6 and no more binary64 raster predicate

### E30 — Original C3 cyclotomic Fourier → actual C6 signal

GielisSixPhaseCyclotomicFourierExact.agda now
reuses the repository's fully proved
C3CubeCyclotomicFourierExact arithmetic and
native oneDimensionalFourierInversion /
oneDimensionalFourierForwardInverse theorems.
It constructs a two-point Fourier/Hadamard
transform and tensors it with the existing C3
DFT to give an exact selected C6=C2×C3
operator with both inverse directions.
The actual Phase18 six-point selection is
even=[0,4,2], odd=[3,1,5] and corresponding
original Q(zeta36) mode order [0,2,4,3,5,1].
The exact interoperability script tests
729 input signals against the direct original
cyclotomic six-point DFT and confirms all
transform/reconstruction equalities without float.
This closes source-level selected C6 Fourier
but not native FULL C36 representation.

### E31 — Exact rational m=3,6,9 raster geometry

**G12 numerical-boundary blocker RESOLVED**, not
merely reduced by the E27 h² cutoff.
An exact identity decides unshrunken Gielis
membership at every rational grid point using
the real part of (x+iy)^m and a strict
rational polynomial/sign comparison. For odd m
the single square root is eliminated by
case splitting on the sign of A and B before
squaring; equality is excluded exactly.
The source scripts/gielis_exact_rational_raster_geometry.py
has replaced the floating radial predicate in
the original Cartesian finite-difference solver,
the rational eigenvalue referee and the exact
zero-exterior discrete energy checker.
All four original fixtures (m3/6/9,n41 and
m3,n61) retained EXACTLY the legacy masks:
792,779,792,1788 interior sites and zero
disagreeing nodes. The old floating epsilon
is no longer a necessary algorithmic input,
and E27's vanishing-tolerance scheme is
superseded by exact *zero*-tolerance geometric
classification for positive integer m.
The selected rational Agda decision
functions and boundary/origin equations are
source-written in
GielisExactRationalGridPredicateExact.agda.
Native Agda correspondence with the Bishop-real
radial definition and kernel acceptance remain
separate G12/Bishop proof obligations.

### Current exact remaining high-alpha leaves

- G-BISHOP: actual Round11 same-source addition
  theorem/double-angle/π, reciprocal/sqrt and
  Bishop real radial integration, and Agda acceptance.
- G-FOURIER: FULL C36 Cyclotomic36 scalar
  \(\mathbb Q[x]/(x^{12}-x^6+1)\), 36 character
  orthogonality and generic inversion in native
  Agda; E28/E30 now CLOSE selected C4/C6
  subcarriers without implying the full result.
- G-SPECTRAL: existing exact-rational membership
  removes floating-boundary ambiguity;
  quantitative original finite-grid continuum
  error and native mathematical compactness/graph
  assembly remain.
- G-SI: exact typed optical signed-torque magnitude
  already implemented; original calibrated
  impact/momentum geometry and source receipt
  remain as the real-world validation leaf.
- Golden: all ten selected Gielis Agda modules now
  wired to parallel checker, exact-head source
  kernel acceptance not yet obtained.

Historical CI/HTML are deferred from the active
user-requested max-cut.


## E32 original signed-ray SI transfer and final narrowed mathematical cut

The new
DASHI/Geometry/GielisOpticalTorqueCrossSIExact.agda
computes the **actual** planar signed angular lever

\[
 \ell_z=x(i_y-\eta o_y)-y(i_x-\eta o_x),
 \qquad
 \tau_z=(P/c)\ell_z\;\mathrm{N\,m}.
\]

It builds the result by reusing the same native typed
Mechanical.Quantity and MechanicalSI.SIIndexedQuantity
as E22, not by assuming an arbitrary signed
dimensionless deflection factor. The source
proves the cross identity, anti-symmetry, reversal
under swapping in/out at full reflectivity,
zero from unchanged direction and invariance
under a 180-degree simultaneous rotation.
Existing R3HodgeCrossExact supplies the right-handed
Hodge/cross convention; the rational-to-axiomatic
real carrier bridge remains a separate exact
type identification. An independent Fraction
SI event fixture proves the ±18000/299792458 N m
signed cases and the zero-torque control.

### Exact current leaf list — do not reopen paid donors

| Active cut | Specific remaining producer | Already paid and reused |
|---|---|---|
| B-TRIG | Round11 **actual** complex/real exponential-to-sin/cos same-object identity and addition/doubling; consistent \(\pi\) | BishopExponentialCauchyProductExact.bishopExpAdd, BishopSineCosineSetoidCongruenceExact, E25/E29 ring and source reductions |
| B-GEOM | Actual Bishop reciprocal/sqrt branch, radial derivative, polar integral and positive nonzero radius | Native Bishop quartic, E02–E04 paper analysis |
| F-36 | Original \(\mathbb Q(\zeta_{36})\) 12-rational-coordinate native algebra, generic full 36-character orthogonality, DFT and reconstruction | Exact Python 1296 pairs, C3CubeCyclotomicFourierExact and NEW E28 C4 / E30 C6 native selected transforms |
| S-NATIVE | Same-carrier Bishop real analytic domain, native exact raster enumeration/energy compactness/Dirichlet eigenvalue limits | E17/E26 exact rational eigenvalues, E27 paper fixed-k convergence and E31 original literal exact rational mask |
| S-RATE | Quantified continuum **finite mesh** eigenvalue error, verified constants | Exact finite brackets, domain comparison and E27 qualitative convergence |
| SI-REAL | Measured source power, reflectivity, normal/impact locations, physical torque and uncertainty matching original optical event carrier | Canonical BIPM SI c, E20/E22 typed quantity transport, E24 intervals, E32 signed ray law |

**Deferred by user request:** CI and historical HTML
scene replay. No engineering/physical conclusion is
promoted beyond the available measurement evidence.

**Agda acceptance:** eleven source-written native
Gielis proof roots are now registered under the
repository's existing parallel checker. An Agda
kernel receipt has not been produced in this environment.


## E33 — reduce Gielis trig to ONE actual imaginary-axis Bishop exponential law

The original BishopExponentialCauchyProductExact
already contains bishopExpAdd and
bishopExpTimesNegativeIsOne for the REAL exponential.
The selected BishopSetoidComplexExact constructs
literal Cartesian Bishop complex values, while the
selected Round11 power series provide the *actual*
Bishop sine and cosine.

DASHI/Geometry/GielisBishopImaginaryExponentialReducerExact.agda
imports these original analytic donors and
defines E_B(ix)=(cos_B x,sin_B x) in the existing
Bishop complex carrier. Given **one** genuine
same-source equality

\[
 E_B(i2x)\simeq E_B(ix)\,E_B(ix)
\]

its real/imaginary setoid projections yield both
native cos(2x) and sin(2x) doubling formulae.
The repository's existing Bishop sine/cosine
setoid-congruence theorem transports the proven
Bishop ring identity 4x≈2(2x). The E29
consumer and E25 polynomial/quartic source then
prove the selected Gielis 4(cos⁴+sin⁴)=3+cos4x
identity on the literal selected Round11 object.

**Highest-alpha analytic leaf:** Construct this
imaginary-axis **COMPLEX** series Cauchy product
and prove it identifies with the existing Bishop
real sine/cosine power-series coefficients and
limits; the real bishopExpAdd theorem is a
donor, NOT a substitute. The previously
identified shared Round11 same-function
Pythagorean weld, Bishop pi/sqrt/radial
integration and strict Agda acceptance remain.

This reduces the G03 trig portion from
three independent 'double-angle inputs' to
one exact, falsifiable source-native analytic
theorem. The reducer source is written,
but the complex multiplication input itself
has **not** been constructed as a proof
and cannot be claimed closed.


## E34/E35 current exact analytic and continuum improvements

**Bishop E34:** New
GielisBishopComplexCauchyAlgebraExact.agda
proves source-level commutative and associative
Bishop complex multiplication and distribution,
on the existing BishopSetoidComplexExact
carrier, using the original Bishop real solver.
This pays the algebraic donor required for E33's
single complex imaginary-axis exponential
multiplication law. Remaining leaf:
**complex factorial coefficient Cauchy product
and absolute-limit identification** with the
original Round11 sin/cos functions. Do not
reprove real bishopExpAdd—it is already owned
by BishopExponentialCauchyProductExact.

**Continuum spectral E35:** The selected
Gielis family has area sqrt(2)*pi for ALL
positive integer m. Using the classical
Faber–Krahn inequality and a rational
alternating Bessel J0/J1 certificate:
- J0(12/5) > 608149/244140625 > 0;
- J1(x)>0 on (0,12/5], hence j_{0,1}>12/5;
- sqrt(2)<99/70 exactly;
- therefore lambda1(Omega_m)>224/55 (~4.0727).

The first Dirichlet eigenvalue for m=3 now
satisfies
\[
 \boxed{\frac{224}{55}<\lambda_1(\Omega_3)
  <\frac{1273}{264}.}
\]
For assumed physical scale L in [Llow,Lhigh],
the SI consumer now returns the stronger
strict lower 224/(55 Lhigh²) m^-2, without
claiming any wave-speed or empirical frequency.
The bound is **independent** of the original
finite-raster eigenvalue calculation.

The new Agda
GielisBesselFaberKrahnRationalExact.agda
contains the exact rational Bessel truncation,
strict positivity and eigenvalue arithmetic;
the standard Bessel/Faber–Krahn analytic
theorems and original Bishop-real embedding
remain explicit foreign mathematical donors.
The native Agda source has not been
kernel-checked in this environment.

**Active outstanding:** original Round11
complex exponential factorial-tail proof;
canonical Bishop pi/sqrt/area/curvature;
full Q(zeta36) cyclotomic native DFT;
native graph-to-continuum min–max/compactness;
quantitative finite-mesh spectral error;
measured original optical source/material
calibration. No CI or original HTML
replay is pursued under the current scope.
