# Gielis × Base369 — exact phased max-cut roadmap

**Status:** active, PR [#1466](https://github.com/chboishabba/dashi_agda/pull/1466) (draft);
**source level:** G01/G02 finite source plus G06 refinement source written, not
Agda-kernel accepted here; Python exact arithmetic executable but committed
branch regression harness not run in this authoring environment. Never call
source-written/type-unchecked source a Golden proof.

**Primary formal record:** [GielisBase369Cut.md](GielisBase369Cut.md).
**Mathematical proof notebook:** [GielisBase369ProofTheorems.md](GielisBase369ProofTheorems.md) (E01–E11), with strictly separated native/empirical acceptance.
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
| Log-polar/exponential spiral | `DASHI/Cognition/AnalyticLogPolarSpiralCompilerExact.agda`, `DASHI/Analysis/ConstructiveRealSpine.agda` | reuse the actual log/exp construction |
| Concrete Bishop trig | `DASHI/Analysis/BishopConcreteTrigAnalyticTermDerivativeExact.agda` and Bishop sine/cosine sources | same-object native trig, no terminal singleton replacement |
| Geometric SOTA baseline | Gielis shape/PDE literature plus freeform optics | compare against non-369 m, splines, splines/ellipses/other reflectors |

**Kozyrev naming collision:** p-adic Kozyrev wavelets in the analysis/Clay
repository are not the ray-optics Kozyrev mirror simulator. The **legacy
optical mirror** is the earlier HTML SDF raymarcher/state machine, with
independent collision replay and torque logs. Its exact original repo/path
is NOT located in this GitHub checkout; require its actual scene/interface,
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
| G02 | `sampledCosine369SameObject` | Prove for each 18-point index `2 cos(2π m j/18) = signal_m j` on *ordinary Bishop ℝ* for m=3,6,9 | G01, Bishop π/trig | Bishop π/sample values OPEN; E12 ring lemma SOURCE |
| G03 | `gielisSpecialCaseIdentity` | Prove cos⁴x+sin⁴x=(3+cos4x)/4 on same ordinary real carrier; introduce sqrt and reciprocal | Bishop trig | E01 paper proof; E12 native Bishop polynomial SOURCE; actual trig weld OPEN |
| G04 | `gielisPositiveSmooth` | 1≤r≤√2; positive denominator, existence and continuous/differentiable radial graph, nondegenerate tangent | G03 | E02 smoothness paper proof; Bishop derivative/sqrt OPEN |
| G05 | `gielisCyclicDihedral` | Exact continuous rotation/reflection and compatibility with C18 maps; use existing dihedral owner | G02,G04 | E02 cyclic/dihedral paper proof; native Bishop/Phase18 OPEN |
| G06 | `phaseGridAliasingBoundary` | At N=18 sin(9θ_j)=sin(27θ_j)=0; at N=36 sin9(θ_1)=+1, sin27(θ_1)=-1; no unjustified bandlimited theorem | G01 | Finite witness SOURCE; exact symbolic receipt; kernel OPEN |
| G07 | `finiteFourierProjector` | Native ℚ^18/finite-character linearity, idempotence, self-adjointness and `P_a P_b=P_lcm`; reuse finite Fourier inversion owner | G01 | E05 paper proof; E13 exact Q(zeta36) 1296-pair PASS; Agda OPEN |
| G08 | `gielisEqualArea` | Area=(1/2)∫₀²πr² dθ=√2π for all positive integer m; real periodic integration | G03,G04 | E03 exact area paper proof; Bishop integration OPEN |
| G09 | `gielisNormalCurvature` | r,dr/dθ, outward unit normal, curvature and uniform nondegeneracy; prove smooth-curve equivalence | G04 | E04 exact curvature paper proof; Bishop derivative OPEN |
| G10 | `complexFourierSameObject` | Complex characters, inversion/Parseval and oriented phase sector; account for m=9 Nyquist degeneracy | G06,G07 | E13 exact cyclotomic seven-mode roundtrip PASS; native Agda Fourier OPEN |
| G11 | `gielisDomainDirichlet` | Bounded Lipschitz/star-shaped Ω_m, Dirichlet self-adjoint -Δ, compact resolvent | G04,G09 | E07 operator/compact resolvent proof; E15 Rayleigh bound PASS; native Agda OPEN |
| G12 | `gielisDiscreteSpectrumConverges` | Consistent/boundary-correct finite difference or FE scheme, spectral nonpollution and quantitative error; 41/61 images insufficient | G11 | E14 sector-domain all-eigenvalue O(m/N) certified; Cartesian FD error OPEN |
| G13 | `spiralBaselineSameObject` | Restore HTML SDF original scene/emitters/wall/aperture/forward ray intersection/absorber; exact collision replay comparison | actual legacy scene | E16 independent new-scene root/segment source; original HTML SDF OPEN |
| G14 | `polygonReflectionConverges` | For nongrazing hit/finite bounces establish polygon→smooth event/trajectory and torque convergence, with singular set handled | G09,G13 | E09 nongrazing paper proof; local new-scene 17.85x convergence; legacy OPEN |
| G15 | `physicalImpulseTorque` | Define optical momentum transfer, lever arm, time-power and units in SI; connect normalized impulse to existing SO(3) torque/Hodge | G13,G14 | E08 sign and ideal P/c torque model SOURCE; physical calibration OPEN |
| G16 | `opticalParetoValidated` | Source-matched 369/non369/freeform controls; focus/impulse/energy objective directions, uncertainty/CI, calibration and replication | G13–G15 | E16 IID Hoeffding simultaneous uncertainty model SOURCE; measured CI OPEN |
| G17 | `geometricInverseIdentifiability` | Parameter-to-boundary fitting with noise/MDL model class; equal-shape nonuniqueness or local full-rank identifiability | G04,G10 | E10 exact zero-modulation nonidentifiability; inverse estimation OPEN |
| G18 | `productSymmetry27Bridge` | Explicit product action for C3³ on 27 fibre states; distinguish C27 cyclic and prove projection/phase compatibility | tower+hyperfabric | E11 nonisomorphism C27 vs C3^3 proved; positive product bridge OPEN |
| G19 | `sampleRateShannonBoundary` | Selected spectral/bandlimited space, sample+reconstruction maps, threshold and aliasing/null counterexample; do not identify PNF query projection with a Shannon theorem | G06,G10 | E06/E13 exact 7-mode Fourier theorem/pass; native sampling owner OPEN |
| G20 | `gielisMDLKolmogorovBoundary` | Reversible prefix-free Elias-gamma parameter codec; remaining residual, precision uncertainty, weighted physical cost, ordinary Kolmogorov/Shannon theorem boundaries | MDL+Shannon owners | E10 operational codec SOURCE; Kolmogorov/Shannon optimality OPEN |
| G21 | `gielisOpticalRunReceipt` | Direct run of **committed exact commit** script+test with provenance (toolchain/hash/seed/geometry), not the older standalone receipt | G13 optional for exploratory run, needed for sameness | Local E13–E15 checks pass; full exact-head Agda/Python/empirical receipt OPEN |

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
