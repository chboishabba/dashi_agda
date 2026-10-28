# Three Fourier modes × binary-in-ternary / ternary-in-binary × balanced/369 Navier–Stokes

**Date:** 2026-10-28. **PR:** [#1407](https://github.com/chboishabba/dashi_agda/pull/1407).
**Formal status:** new source-written Agda and authored Python tests; independently executed finite Python arithmetic; no Agda kernel run / exact-head CI run / physical NS or R2P2 validation. No ESD changes.

## 1. Reuse-first PR and owner genealogy

The user's specific question concerns the earlier Ma optical-lattice Fourier window `k=-1,0,+1`, the separate 369 binary/ternary codecs, and the existing signed/balanced Navier–Stokes constructions. The strongest common operator is **Fourier convolution/projection**, not coincident three-element cardinality.

Existing, fetched **default-master** owners:
- `DASHI.Algebra.Trit` — original balanced `neg/zer/pos` and involution.
- `DASHI.Codec.VerifiedFiniteTritCoder` — original two-bit trit table `neg=00, zer=01, pos=10, 11=invalid`, exact roundtrip; use as a machine *label* codec.
- `DASHI.Codec.BalancedTritBitFibre` — original **support bit + conditional sign** `zeroFibre | signedFibre sign`, exact invertibility and signed cost model. A single support bit is not a signed coefficient.
- `DASHI.ComputerScience.BinaryBalancedTernarySubcarrierExact` — source-owned strict binary image `false -> -1, true -> +1`, excluding centre 0. Does NOT equate binary and ternary carrier types.
- `DASHI.ComputerScience.BalancedTernaryQutritBasisBridgeExact` — original trit ↔ qutrit computational *basis labels*. Not a general quantum superposition or a Fourier amplitude.
- `DASHI.Core.IndexedRelationalHyperfabricSpineExact` + `DASHI.Core.IntersectionalNonFactorability` — source-owned collision ⇒ cannot factor/rechart and restore discarded information.
- `DASHI.Physics.Closure.NSIntegerFourierLattice` — original **unquotiented** `ℤ³` Fourier-mode vectors and exact additive triads.
- `DASHI.Physics.Closure.NSCross369OrientationBridgeExact` — original Complex3 vector cross product / Beltrami and Leray orientation witness; **Complex3 is not cyclic C3**.
- `DASHI.Physics.CFD.SparseTwistLESOperator` and `SparseTwistLESBridge` — original signed sparse-vorticity codec and conditional exact evolution; no generic model efficiency or Clay theorem.
- `DASHI.Physics.Closure.NSTriadKN369HighHighGramBridgeReceipt` — original fail-closed high-high Gram Rayleigh `λ_min(K_N(A)) ≥ c/N` frontier; 369 label does not pay that analytic estimate.
- `DASHI.Physics.Closure.R2P2OpticalLattice369HamiltonianCutExact` — PR #1407 source-written 2026 Ma S6 `±11,±18` supercell Fourier sideband non-representation in the *three-mode* window.

**Relevant latest PRs:** [#1386](https://github.com/chboishabba/dashi_agda/pull/1386) (open finite-27 bidirectional codec owner), [#1390](https://github.com/chboishabba/dashi_agda/pull/1390) (open current TOE codec max-cut), [#1279](https://github.com/chboishabba/dashi_agda/pull/1279) (open NS 369 original orientation+Gram reuse), [#1384](https://github.com/chboishabba/dashi_agda/pull/1384) (open native NS cross-gradient frontier), and [#1391](https://github.com/chboishabba/dashi_agda/pull/1391) (open NS R829 vector/non-promotion). All remain independently authored, and no sibling-only module has been imported here.

**Scientific roots:** original Orszag/Patterson pseudo-spectral Fourier aliasing/dealiasing theory, and **Clovis Lambert, Jason Reneuve, Pierre Augier**, *Aliasing and phase shifting in pseudo-spectral simulations of the incompressible Navier-Stokes equations* (2026), https://arxiv.org/abs/2603.08892. Ma, Stölzel, Christensen and collaborators, *An Aubry–André localized optical lattice clock*, [arXiv:2610.17499v2](https://arxiv.org/abs/2610.17499), remain the original optical-lattice experimental authors; their *plane-wave* S6 Hamiltonian is a different operator from nonlinear NS and the tiny finite proof here. Historical mathematical/scientific authors and all previous DASHI PR proof owners retain independent attribution. Ibrahim/Danforth/Dodds and Monster 3B authorship stays disjoint; there is no same-object identification.

## 2. Genuine exact finite algebra versus lossy three-grid folding

Let `M={-1,0,+1}` denote **integer Fourier mode indices**, not a physical balanced-trit-valued wave amplitude. There are 9 ordered pairs of input modes. Their **ordinary integer sums** occupy five modes `{-2,-1,0,+1,+2}`.

On a **three-point periodic DFT**, frequencies differing by multiples of 3 have identical sampled phases. The residue projection `ρ3(k)` is defined as the representative in `{-1,0,+1}`. Consequently,

```text
exact:        +1 + +1 = +2     (outside retained [-1,0,+1])
C3 residue:   +2 ≡ -1 (mod 3)
exact:        -1 + -1 = -2
C3 residue:   -2 ≡ +1 (mod 3)
```

The newly source-written `R2P2ThreeModeBinaryTernaryNSAliasingCutExact.agda` constructs all nine exact sums and an explicit 5→3 residue fold. It proves the two alias equalities by reduction. It proves an explicit information collision: the *genuine* integer `-1` and *unresolved* `+2` both fold to `-1`, while those five-mode labels are demonstrably different. The pre-existing generic nonfactorability theorem then yields a **no inverse decoder / no later rechart repair** result. This is a more meaningful finite Max Cut than constructing a new ternary carrier.

The binary/ternary codecs are **exactly invertible on a mode label**, but they necessarily preserve whatever folded index is supplied. Hence even a perfectly lossless encoder **cannot undo convolution aliasing**. There are two independent cuts: **(a)** support-only projection drops Fourier sign, and **(b)** periodic-grid folding drops the original unbounded wavevector. Their retained residuals differ. The original support+optional-sign fibre restores (a); retaining a five-mode integer Fourier support or comparable alias-free high-mode data restores (b) in this tiny finite example. One does not automatically repair the other.

This also distinguishes the original Ma S6 supercell sidebands `±11,±18`: they do not appear as nonzero off-diagonal terms in a three-plane-wave-mode window. That is a *linear Hamiltonian matrix truncation* issue; quadratic NS mode folding is a separate *nonlinear convolution* issue. The three-site **real-space** P3 adjacency is yet another independent operator, not a direct Fourier-sideband identity.

## 3. Exact executable 27-case sweep and five-mode correction

The new executable `scripts/r2p2_three_mode_codec_ns_aliasing_diagnostic.py` enumerates the `3^3=27` possible **balanced-integer amplitude** vectors `(a_-1,a_0,a_+1)∈{-1,0,1}^3`. It computes the exact quadratic product spectrum as integer convolution and compares retained modes after folding onto sample lengths N=3 and N=5.

In this precisely defined finite case:
- **24 of 27** input profiles create spurious retained-mode coefficients under N=3 pointwise multiplication.
- **0 of 27** create spurious retained-mode coefficients on N=5, because every quadratic output mode `-2..+2` is explicitly resolved.
- Example `u=e^{ix}` (amplitudes `0,0,1`): exact `P_{|k|≤1}(u²)=0`; 3-grid multiplication outputs a false `k=-1` unit coefficient; 5-grid multiplication/project-back outputs zero.

This comparison is exact integer arithmetic without floating FFT or numerical roundoff. It is **not** a proof of global 3/2 padding optimality or the standard 2/3 NS dealiasing theorem, because the specific N=5 resolution was selected to represent the full product `±2` and the simulation never models real NS pressure, projection, boundary conditions, helicity or time evolution. It is a finite counterexample and repair with an explicit type-level distinction between state/codec and operator/support.

**Execution attribution:** the finite 27-case enumeration and N=3/N=5 comparison were independently executed in local Python and returned `24/27, 0/27`. The **committed** diagnostic and full GitHub checkout unittest suite remain unexecuted on their exact PR head. The new Agda source has not been kernel-checked.

## 3b. Direct three-dimensional NS and 27-state codec comparison

The 1-D three-mode window extends **coordinatewise** to the concrete `3×3×3 = 27` index cube `C={-1,0,+1}^3`. This is the same finite index count as the repository's canonical triple balanced trit, but **not** the unbounded integer NS carrier `Z^3`. The new module directly imports `BinaryThreeBitTwoTritAntipodalCodecExact`, `BinaryThreeBitTrit27FibreLiftExact`, `BalancedTernaryAntipodalOrbitExact` and `Base369AddressSymmetryAndBranchGeometryExact` to reuse:

- The original **three binary bits → two balanced trits** injective payload codec. It uses 8 of 9 pair values, with centre (0,0) reserved.
- The **27-trit-triple framed lift**: two payload trits plus a zero framing trit. Its encoded three-bit image is **8 of the 27** possible trit triples. It is not a bijection from 8 states to 27 states.
- The original roundtrip `bit3LiftRoundTrip` and complement ↔ strict antipode equivalence; these are inherited, not newly proved here.
- The **full** three-axis signed mode label cube using the actual `Branch.triple` carrier, which includes all 27 labels (not just the binary payload image).

The new `periodicThreeAxisPositiveXSquareWrapsToNegativeX` is a genuine finite 3D example: two `(1,0,0)` Fourier modes have true sum `(2,0,0)` in the original NS integer lattice; modulo-three per-axis folding maps that to `(-1,0,0)`. A lossless three-bit/two-trit/framed-27 codec encodes whichever **post-fold** label it receives, but does not preserve the pre-fold integer vector unless the missing information is retained separately.

The executable now exhaustively enumerates **all 27²=729 ordered mode pairs** in that 3D cube. There are exactly `7³=343` pairs whose integer sum stays inside `{-1,0,1}³`, and **386** with at least one out-of-window component. A five-point frequency grid on each axis represents the full `{-2,-1,0,1,2}³` pairwise-sum range in this *particular* tiny finite setting, with zero index folding errors. These counts were independently executed in Python using 729 integer comparisons (not floating FFT). This is **not** a 27-vector physical NS Galerkin simulation; vector-valued complex amplitudes, Leray incompressibility, helical signs, Navier–Stokes time evolution and cutoff-uniform estimates are absent.

## 3c. Stronger NS steelman: nonzero Leray-projected interaction changes under C3 folding

A single transverse Fourier mode self-interacts trivially in the incompressible quadratic nonlinearity. Therefore the earlier `(+1)+(+1)` mode-index counterexample **by itself does not demonstrate a nonzero incompressible NS aliasing error**. To pay that objection, the exact-rational executable includes a nonparallel **two-input-mode** witness:

```text
p=(1,0,0),       a(p)=(0,1,0),    p·a=0
q=(1,1,0),       b(q)=(1,-1,0),   q·b=0
true output k=p+q=(2,1,0)
three-grid fold ρ3(k)=(-1,1,0)

symmetric convective coefficient up to common i:
S=(a·q)b+(b·p)a=(1,0,0)
P_k = I - kkᵀ/|k|²

P_(2,1,0) S    = (1/5,-2/5,0)
P_(-1,1,0) S   = (1/2, 1/2,0)
```

**These two results are nonzero and different.** Both input amplitudes satisfy their respective transversality constraints. The source-fixed orthogonal Leray projection is performed using **exact rational** arithmetic; the common complex Fourier factor `i` has been suppressed, which does not affect the discrepancy. The witness was independently executed in local Python and produced the exact fractions shown. A regression in `tests/test_r2p2_three_mode_codec_ns_aliasing.py` now calls the committed exact-rational routine.

This is closer to the real incompressible NS nonlinear Fourier normal form than a bare mode-number coincidence. But it remains **a selected pair at one instant**. It does not model the full field, symmetrised real-valued conjugate completion, pressure evolution, energy inequality, viscosity, finite-time solver, invariant blowup or global regularity. Neither `P_k` nor `P_ρ(k)` alone pays the actual R571/R736 high-high/low-mode uniform Gram/weighted convolution estimates. It is not an Agda-kernel theorem: the existing NS Galerkin/Leray theorem owner is cited, and this source-written adapter's finite layer still needs type checking.

## 4. Pareto / snowball / Ibrahim physical proof cutset

| Priority | Producer that actually pays the cut | Available? |
|---|---|---|
| P0 | Original binary↔ternary exact *label* encoders and nonzero sign subcarrier | On default master |
| P1 | Five exact integer mode sums and demonstrated C3 alias/no-rechart proof | Source written here; kernel pending |
| P2 | Selected quadratic NS convolution indexed on the original `ℤ³` Fourier triads, with a cutoff-consistent projection | Original NS owner exists; no new full consumer constructed |
| P3 | NS Complex3 Leray/helicity/Bony/Gram and physical weighted norm estimates through the canonical B/A/C/D owners | Source-specific open quantitative/analytic leaves unchanged |
| P4 | Actual sampled optical-lattice Hamiltonian eigenvectors, supercell S6 cutoff convergence, clock spectroscopy and calibration | Separate Ma experimental/theoretical source; not imported as a real device |
| P5 | Original R2P2 Yb bidirectional transfer/systematic covariances, ratio and geopotential with verified source hashes | External experimental data still required |

A three-mode toy **can reveal a discretisation bug or an information-loss boundary**. It cannot pay a uniform-in-frequency analytic NS bound, instantiate a continuum physically calibrated lattice clock, identify a quantum gravity correction or solve the Clay Navier–Stokes problem. The strongest steelman of the codec-NS connection is **operator-faithful representation with explicit alias/no-alias conditions**; a mere reversible digit codec is insufficient.

## 5. Deliverables and verification contract

- Exhaustive three-dimensional 27²=729 mode-pair enumeration and original eight-bit-payload-to-27-image distinction added to the same source.\n- New Agda owner: `DASHI/Physics/Closure/R2P2ThreeModeBinaryTernaryNSAliasingCutExact.agda`. Reuse-first imports and exact finite no-go.
- New executable: `scripts/r2p2_three_mode_codec_ns_aliasing_diagnostic.py`.
- Tests: `tests/test_r2p2_three_mode_codec_ns_aliasing.py`.
- Aggregate: `R2P2369AtomicQuantumDiamondArchitectureExact.agda` and all three TOE roots directly expose codec roundtrip, alias collision and no-NS-promotion.
- CI: `.github/workflows/r2p2-369-maxcut.yml` includes the new Python and focused Agda inputs.

Verification levels: **source written** ≠ **Python independently executed** ≠ **committed suite executed** ≠ **Agda kernel theorem** ≠ **real experimental or NS mathematical physics result**. This distinction and the original authors' priority must remain visible in all reports.


## 5b. 28 October reuse breakthrough: source-owned C3³ Fourier BIDI, exact 729 incidence and T⁶ carrier

**Important correction of earlier roadmap:** the original DASHI repository already contains a *full* (not merely symbolic) 27-point cyclotomic Fourier algebra:
- `DASHI.Biology.Physical.C3CubeCyclotomicFourierExact`: original `cubeFourierInversion`, `cubeFourierForwardInverse`, `cubeCharacterOrthogonality`; it builds a genuine 27-index DFT with `ℚ(ω)` amplitudes.
- `DASHI.Biology.Physical.C3CubeCyclotomicParsevalExact`: original `cubeParsevalNormalised`, `cubeParsevalUnnormalised`.
- `DASHI.Biology.Physical.C3CubeDirectGroupConvolutionExact`: original `c3CubeDirectConvolutionTheorem`, `directEqualsSpectralConvolution`. This is **cyclic** C3×C3×C3 group convolution, not Z³/Galerkin convolution.

These already-pay **F4.3–F4.6** as original cyclic-theory owners, once the new signed mode chart is kernel-checked. The new `R2P227729ExistingC3FourierConvolutionReuseExact` packs any function on the 27 signed integer **labels** into the original `CubeSignal`, proves unpack/pack pointwise and pack/unpack object roundtrips, and directly reuses inverse, Parseval, and direct-vs-spectral cyclic convolution. **The chart must order the Fourier group residues as [zero, plus, minus]**, matching C3 residue classes 0,1,2. Ordering them [-,0,+] would be a distinct permutation that need not intertwine the group operation.

The new `R2P227729FourierObserverIncidenceExact` now carries actual pair enumerations `cube27` (27) and `pair729` (729), exact `0..26` and `0..728` rank-list witnesses, and classified *input pairs* rather than naked number products: **343** satisfy coordinatewise `p+q∈[-1,1]³`, **386** do not. It also proves a typed mode/voxel BIDI, exhibits **sign(+2)=+ but centered-mod3(+2)=−**, and distinguishes original periodic C3³ wraparound from the original nonperiodic P3³ graph.

The new `R2P227729PairSixTritFibreBidiExact` gives explicit **mutual inverse** maps `ModeCube27 × ModeCube27 ↔ TernaryFiniteFunctionDeltaBasisExact.TritCube 6` and transport laws for *arbitrary* functions on these 729 addresses. This is a new carrier-shape equivalence to an **original** T⁶ source owner, not a construction of the selected GF729 field action, a Monster representation, or physical clock pairs.

The same finite convolution owner now instantiates the **existing general nonfactorability** theorem on the actual three-dimensional high-frequency modes `(2,0,0)` and `(-1,0,0)`. Both have the same `C3³` residue `(-1,0,0)`, but are distinct integer wavevectors. The module exports `threeAxisCyclicIndexCollision`, `noDecoderOfActualWideModeFromCyclic27`, and `cyclic27RechartCannotUndoWideFrequencyLoss`. Hence **no post-processing of the already-folded 27 Fourier-mode label** can reconstruct all true `[-2,2]³` outputs. The exact source-owned cyclic DFT remains valid on its own quotient; the collision shows precisely what it cannot infer. This theorem is source-written, not yet Agda-kernel checked.

The new `R2P227729FiniteQuadraticConvolutionExact` enumerates all pairs and provides an arbitrary-`Nat`-amplitude coefficient-wise theorem for all 125 integer wide-mode output labels. It recovers each exact `[-2,2]³` output after a **five-element index chart** and proves total pair-weight aggregation equality; a three-grid label-fold example remains genuinely lossy. Crucially, this is **NOT** `DFT5`/sampled-field multiplication equivalence and NOT an incompressible NS vector operator. The outstanding high-alpha finite work is now the **cross-operation intertwiner** (integer Galerkin convolution ↔ 5³-point physical-space product) and transverse vector/Leray structure. The original 27 C3 DFT is therefore reused, not duplicated.

**Execution proof grades at this revision:** source-written Agda modules and root imports; exact arithmetic independently run with Python for 27×27 pair incidence, rank ranges and five input-amplitude profiles on all 125 outputs; **no Agda kernel run**, no exact-checkout test suite receipt, no R2P2/NS physical measurement or global analytic result. User explicitly excluded CI from this continuation, so the branch workflow was left untouched in this tranche.

## 5c. 28 October deeper Pareto: 3³, 4³ and 5³ *cyclic group* operator cut

**Source root:** the exact pointwise/spectral dealiasing identities in Patterson–Orszag (1971) and later pseudo-spectral numerical analysis; Lambert, Reneuve and Augier, [arXiv:2603.08892](https://arxiv.org/abs/2603.08892) (2026), distinguish algebraically exact alias cancellation from approximate time-discretized computations. The current theorem application and finite labels are new DASHI code. Original cyclic `C3³` DFT/cyclotomic algebra remains separately owned by `DASHI.Biology.Physical.C3CubeCyclotomicFourierExact`.

For input integer-frequency support `S={-1,0,+1}³`, the quadratic sum support is `S+S={-2,-1,0,+1,+2}³`. The integer target `P_S(u*v)` retains only 27 output modes, whereas a *full* product stores 125 output modes. These lead to **different legitimate optimization objectives**:

| Periodic grid per axis | Points | Exact integer outputs retained | All 125 wide outputs distinguishable? | Finite result |
| --- | ---: | --- | --- | --- |
| `Z/3` (3×3×3) | **27** | **No**, `(+1)+(+1)=+2 ≡ -1`; false retained alias | No | Explicit failing finite witness |
| `Z/4` (4×4×4) | **64** | **Yes**, all 27 retained modes | **No**, `+2 ≡ -2` (mod 4) | New all-input coefficient theorem |
| `Z/5` (5×5×5) | **125** | **Yes** | **Yes**, all support outputs `[-2,2]³` | New all-input coefficient theorem |

For the retained-output objective, `4³=64` is **48.8% fewer points** than `5³=125`. That is a **grid-index capacity** comparison only, not measured runtime, memory bandwidth, numerical stability, approximation accuracy or physical clock performance. The 3³ grid's failure and 4³ grid's success are source-written *within this three-option family*, not a proof of global optimality across all discretisations, symmetry reductions or phase-shifting schemes. Both 4 and 5 are quadratic band-limit calculations, not claims about unbounded or full nonlinear NS.

**New source-written Agda mathematical owners**:
- `R2P227729FourGridRetainedQuadraticParetoExact`: explicit centered `Z/4` addition table; nine signed input-pair homomorphism cases; three-axis actual group sum and corresponding true `Z³` integer Fourier sum compatibility. `fourGridRetainedMembership` proves that no outer `±2` residue aliases into retained `{-1,0,1}`; therefore `fourGridMatchesExactRetainedForAllCoefficients` holds for every 27-mode **Nat** input. The explicit `fourGridFullOutputCollision` and generic original nonfactorability lemmas prove there is no decoder of all 125 frequencies from 64 residues, and no later relabelling can restore them.
- `R2P227729FiniteQuadraticConvolutionExact`: the existing full-index theorem is strengthened to use the **actual centered `Z/5` group addition** on encoded 27 input modes, not a trivial encoding of a precomputed true sum; all nine signed pair cases and three-axis group-sum compatibility are explicit. `all729PairsFiveIndexRecoveryIsExact` covers every output of the 125-wide support and all natural amplitudes.
- `R2P227729BilinearCyclotomicPadCutExact`: a polymorphic `CoefficientOps A` with user-supplied zero/add/multiply, two independent arbitrary 27-mode inputs `f,g`, generic summation-extensionality, and pointwise 729-term group-convolution incidence equality. The original `C3CubeCyclotomicFourierExact.Cyclotomic3 = ℚ(ω)` is instantiated *without duplicating its field algebra*. `cyclotomicFourGridRetainedBilinearExact` and `cyclotomicFiveGridFullBilinearExact` are general two-input signed/cyclotomic **finite sum** transport laws.
- `scripts/r2p2_27x27_four_grid_pareto_diagnostic.py` and its test module provide multiple signed rational coefficient inputs and exact `ℚ(ω)` multiplication inputs; group sums are computed from encoded inputs, not by relabelling precomputed integer sums. An independent local Python audit checked six rational profiles (including two distinct sparse frequencies), one two-input exact cyclotomic profile, all 27 retained modes, and all 125 full outputs. **The committed exact-checkout tests and Agda kernel have not run.** User instructed to disregard CI in this tranche; existing CI is left unchanged.

**Outstanding precise proof obligations (additional refinements to the 106 main ledger entries):**
1. **want:`C4FourierWithInverseAndConvolution`**: use original source Fourier components if possible; otherwise explicitly construct the true `64`-point `C4³` Fourier transform, root-of-unity normalization, inversion and group-convolution theorem for a field embedding that preserves actual complex coefficient identities. The previous `C3³` theorem is for order 3, not for order 4.
2. **want:`C4SampledProductEqualsRetainedIntegerGalerkin`**: use the source-written `Z/4` group-sum compatibility + actual DFT4 group convolution theorem to show the *sampled physical-space pointwise quadratic product* reproduces the retained `Z³` Galerkin coefficient for arbitrary complex-valued 27-mode inputs, including normalization and projection.
3. **want:`C5FourierWithInverseAndConvolution`**: likewise build or import the actual `125`-point `C5³` Fourier authority, with an adequate cyclotomic fifth-root field; the inherited `ℚ(ω)` 27-point group Fourier theorem **cannot** simply be renamed `C5`.
4. **want:`C5SampledProductEqualsFullIntegerConvolution`**: show the complete 125-output wide spectrum, not just projected retained outputs, matches a genuine `DFT5`/inverse sampled-field computation.
5. **want:`finiteRealDivergenceFreeComplex3LerayTransport`**: original complex-vector NS/Leray and conjugate reality must be preserved through the actual 64/125 sample-space operator; a generic scalar incidence law is not a physical NS regularity theorem.
6. **want:`kernelChecksAndSourceDataGates`**: no source-written `refl` witness is promoted to an Agda kernel theorem without executing the focused checked imports, all three TOE roots and relevant tests. Real Ma 87Sr, Triano R2P2 neutral Yb and original Ibrahim/Monster 3B sources remain separate.

This is an actual Pareto decision: target the **64-point retained-mode FFT theorem first**, because it pays the useful physical NS finite Galerkin projection with fewer samples; add the 125-point full-spectrum FFT only when the complete quadratic spectrum is an explicit consumer. The original 27-point `C3³` algebra is now an inherited DFT owner and a concrete alias counterexample, not a substitute for either C4 or C5.

## 6. Completion roadmap and exhaustive scoped lemma inventory (28 Oct 2026)

**Scope of “complete”**: This is the entire currently identifiable lemma cutset for (F) a fully kernel-checked exact three-mode/27×27 Fourier *finite* codec/NS-operator abstraction, (M) an actual Ma-source optical-lattice operator/spectral comparator, (R) the separate R2P2 experimental comparator, and (C) any attempt to pay the global NS analytic/Clay frontier. There cannot be a known finite, complete list of lemmas that proves an unsolved global mathematical claim merely by inspecting code. If F reaches a kernel-green finish, M/R/C remain independent targets. Names prefixed **want:** are specifications, **not** claims that those declarations exist.

**Tags:** [R] exact theorem already exists in inspected original default-master source; [S] source-written on PR #1407 but **not Agda kernel-checked**; [B] proof appears only in another **open branch**, so must be imported by a legal merge/rebase and rechecked; [N] new finite obligation; [A] genuinely open mathematical/analytic or empirical source-backed obligation. An independently executed Python integer check is not a kernel theorem. All original owners retain theorem attribution.

### Gate G0 — trustworthy lineage / Agda / execution (mandatory before claiming F complete)

- **G0.1** [N] \`noTrustEscapes\`: focused changed Agda files and transitive imports have no new postulates, holes, \`allow-unsolved-metas\`, \`TERMINATING\`, \`NO_POSITIVITY_CHECK\` or equivalent unexplained proof escape.
- **G0.2** [N] \`allSourceImportsResolve\`: each exact import, alias, data constructor and qualified constant resolves against the exact HEAD's pinned Agda 2.9 and stdlib versions.
- **G0.3** [N] \`focusedAgdaKernelGreen\`: type-check each new module in a dependency order (original source, wave, optical-lattice, binary/ternary Fourier, architecture), not only a string-search unittest.
- **G0.4** [N] \`allThreeTOERootsKernelGreen\`: independently check \`EverythingTOESymmetryResolved369\`, \`Unifier\` and \`Unified/Everything\`, avoiding aggregate import cycles and unmerged-only names.
- **G0.5** [N] \`pythonExactCheckoutGreen\`: run \`unittest discover -s tests -p 'test_r2p2_*.py'\` and both Python CLIs **from the same checked-out commit**, with stdout/exit codes, not from a retyped reference.
- **G0.6** [N] \`pythonVsKernelCaseCorrespondence\`: match every finite Python case's input/output types and constants with the Agda theorem statement; ensure tests do not only assert source strings.
- **G0.7** [N] \`primarySourceAndAttributionLedger\`: keep Ma v2, Triano APS 2026, Bothwell/Ye 2022, Orszag/Patterson, Lambert/Reneuve/Augier 2026, and original DASHI/PR contributors as separate owners.
- **G0.8** [N] \`noESDOrMonsterPromotion\`: assert changed-file ESD protection and that numerology, shared finite cardinality or sample data never becomes same-object Monster 3B or physical NS/GR evidence.
- **G0.9** [N] \`externalProofStatusGated\`: source-written ≠ executed Python ≠ kernel proof ≠ laboratory source-data validation, enforced in documentation and release status.

### Gate F1 — exact carriers and existing codecs (mostly reuse)

- **F1.1** [R] \`tritAfterThreeModeRoundTrip\` and \`threeModeAfterTritRoundTrip\` on PR #1407 [S]; original \`Trit\`/SSP carriers are on default master [R]. Verify both roundtrips in kernel.
- **F1.2** [R] \`VerifiedFiniteTritCoder.decode-encode\` and \`reserved-word-rejected\`: original \`neg=00, zer=01, pos=10, 11=invalid\`.
- **F1.3** [R] \`BalancedTritBitFibre.decode-encode\`, \`encode-decode\`, support/sign split and involution.
- **F1.4** [R] \`BinaryBalancedTernarySubcarrierExact.binaryTernaryRoundTrip\`, \`centreIsUnusedByBinaryEmbedding\`; binary uses only the two nonzero trits.
- **F1.5** [R] \`QutritBasisClassicalCodecFibreExact.qutritTwoBitRoundTrip\` and \`BalancedTernaryQutritBasisBridgeExact.qutritAfterTritRoundTrip\`; **basis labels only**.
- **F1.6** [R] \`BinaryThreeBitTwoTritAntipodalCodecExact.blockRoundTrip\`, \`centreUnused\`, \`complementAntipodeEquivariant\`.
- **F1.7** [R] \`BinaryThreeBitTrit27FibreLiftExact.bit3LiftRoundTrip\` and \`bitComplementBecomes27Antipode\`; its binary image has **8**, not 27, framed states.
- **F1.8** [R] \`Base369Ternary27HypervoxelFabricGeometryExact.hypervoxelStateCountIs27\` and exact \`Ternary27Point\`.
- **F1.9** [S] **want:\`threeModeCubeEquivBase369Point\`**: explicit bijection between three mode-label products and the existing canonical \`Ternary27Point\`, with both inverse proofs; use original constructors, not fresh incompatible C3 types.
- **F1.10** [S] **want:\`pair27EquivTrit6\`**: typed bijection between *ordered pairs* \`Cube27×Cube27\` and the existing \`TritCube 6\`; preserve roles, and prove projection/pair/rebuild in both directions. \`Base369TernaryDeltaBasisCrossPollinationExact.appraisalCountIsDecisionSquared\` proves cardinality, not this physical role identification.
- **F1.11** [N] **want:\`pair27IsNotPhysicalDoubleClockOrGF729\`**: guard that a pair of mode labels ≠ an optical two-clock measurement ≠ a selected GF(729) field element/Monster action without a separately named carrier-and-operator equivalence.

### Gate F2 — the **three distinct** 27-label observers (highest-alpha missing math)

- **F2.1** [R] \`NSTriadKNPeriodicIntegerTernary27SignChartRound529Exact.integerSign529\` and \`observePeriodicMode529\`: actual integer **sign** quotient, respecting reflection.
- **F2.2** [R] \`NSTriadKNPeriodicFourierTernaryTorusFibreBidiRound530Exact.periodicSignObservationSection530\`: existing section of sign observation.
- **F2.3** [R] \`NSTriadKNPeriodicTorusBase369NormalizationRound531Exact\`: exact sign-fibre/B369 carrier normalization and periodic torus adjacency, **not** a quotient of integer addition.
- **F2.4** [S] \`periodicThreePointFold\`, \`threeAxisPeriodicallyAliasedPlusXSquare\`: distinct **centered modulo-three** sampling residue.
- **F2.5** [S] **want:\`signVsCenteredModThreeDisagreeAtTwo\`**: at \`+2\` prove \`integerSign529(+2)=+\` and \`centeredMod3(+2)=-\`; their outputs differ even though both have three labels.
- **F2.6** [N] **want:\`signQuotientNotAdditive\`**: exhibit \`(+1)+(+1)\` as a concrete failure of signed-trit C3 group addition under the sign observer. The existing sign-section never claimed a group homomorphism.
- **F2.7** [N] **want:\`modThreeIsAdditive\`**: prove \`ρ_3(p+q)=ρ_3(ρ_3p+ρ_3q)\` for integer Fourier vectors, using a genuine mod-3 group structure (not signed sign classification).
- **F2.8** [S] **want:\`pathAdjacencyNotCyclicAdjacency\`**: preserve the original P3 cubical adjacency's lack of wraparound from \`Base369Ternary27PathCubeSpectralBandsExact\`; contrast with \`Base369PeriodicTernaryTorusPathRestrictionBidiExact\`.
- **F2.9** [R] \`Base369Ternary27CharacterAdjacencyEquivarianceExact\`: \`C3×C3×C3 ≠ Z/27Z\` guard, cubic tensor character and axis swap/rotation.
- **F2.10** [N] **want:\`observerInformationOrder\`**: identify which consumers factor through **sign**, **mod3**, **sign+exact residual**, and **mod3+integer quotient**. Neither bare 27-class observer can recover unbounded frequency or the correct output under every nonlinear operation.

### Gate F3 — pair incidence and correct integer Fourier convolution

- **F3.1** [R] \`NSIntegerFourierLattice.addMode\`, \`Resonance\`: original \`ℤ³\` exact resonance.
- **F3.2** [S] \`exactQuadraticModeSum\`, \`positivePositiveLeavesThreeModeWindow\` and \`periodicQuadraticModeSum\`: PR #1407 finite nine-case integer-versus-folded model.
- **F3.3** [S] **want:\`enumerateCube27CompleteNoDuplicates\`**: a canonical ordered \`Fin 27\` enumeration of all 27 signed mode labels, with a proof of completeness and uniqueness.
- **F3.4** [S] **want:\`enumeratePair729CompleteNoDuplicates\`**: equivalence between pairs of \`Fin 27\` and \`Fin 729\`, preserving ordered pair roles.
- **F3.5** [N] **want:\`integerTriadPairSumCommutesWithEmbedding\`**: all 729 source-indexed pairs use canonical \`NSIntegerFourierLattice.addMode\`, not arithmetic in C3³.
- **F3.6** [S] **want:\`oneAxisSevenInsidePairs\`**: seven of nine ordered pairs in \`{-1,0,1}²\` have sum inside \`{-1,0,1}\`.
- **F3.7** [S] **want:\`cube343InsidePairs\`**: coordinate product gives \`7³=343\` exact in-window ordered 3D pairs. The current Agda \`7*7*7=343\` arithmetic is not yet a proof that this is the actual classified set.
- **F3.8** [S] **want:\`cube386OutsidePairs\`**: partition the 729 actual pairs by decidable membership and prove \`729-343=386\`; no duplicate, omitted or unclassified input.
- **F3.9** [N] **want:\`modeSumNegationCovariant\`**: signed antipode / true wavevector negation commute with exact integer addition; respect conjugate-frequency roles.
- **F3.10** [N] **want:\`pairIncidenceByOutput\`**: partition 729 ordered interactions into output fibres by **integer** \`k=p+q\`, not output sign or 27-bin residue.
- **F3.11** [N] **want:\`outOfWindowDoesNotMeanNonzeroAmplitude\`**: incidence support alone supplies no physical coefficient; zero-valued and cancelling terms remain possible.

### Gate F4 — full finite function algebra, 27² matrix and true FFT/DFT

- **F4.1** [R] \`TernaryFiniteFunctionDeltaBasisExact.decomposeExact\` and \`Base369TernaryDeltaBasisCrossPollinationExact.decisionFunctionDecomposition\`: exact finite point-mass decomposition on \`TritCube 3\`.
- **F4.2** [R] \`Base369Ternary27CharacterAdjacencyEquivarianceExact.cubeCharacterValue\`: existing C3³ tensor character values.
- **F4.3** [R] **want:\`cubeCharactersOrthogonal\`**: exact finite orthogonality sum using a carrier with sufficient roots of unity and a correct normalization (\`ℂ\`, cyclotomic or rational complex).
- **F4.4** [R] **want:\`cubeDFTInverse\`**: construct a full 27-point transform and inverse; the original \`Base369Ternary27SpectralSymmetryIrrepBridgeExact\` explicitly does **not** claim this.
- **F4.5** [R] **want:\`cubeParseval\`**: correct normalization and squared-norm equality. The original symmetry/character labels do not themselves prove Parseval.
- **F4.6** [R] **want:\`mod3ConvolutionTheorem\`**: Fourier transform of **periodic folded** convolution is pointwise product, explicitly contrasted with the integer Galerkin convolution.
- **F4.7** [S] **want:\`fullPair729KernelToLinearMap\`**: a typed bilinear map \`Coefficient^27×Coefficient^27→Coefficient^27\` indexed by pair-incidence and output, with \`27²\` interaction entries; a 729-element index set alone does not supply physical coefficients.
- **F4.8** [N] **want:\`periodicVsPathSpectrumNotSilentlyIdentical\`**: original \`Base369Ternary27PathCubeSpectralBandsExact\` provides multiplicity combinatorics, not a diagonalization of periodic or real lattice operators by cyclic characters.
- **F4.9** [S] **want:\`codecPushForwardOfFullKernel\`**: transporting the *same fully retained* 27×27 kernel through an exact codec commutes with decoding, with no claim that a quotient also transports it.

### Gate F5 — alias-free projected quadratic operator and padded computation (finite endpoint)

- **F5.1** [S] \`exactRetainedModeProjection\`, \`correctQuadraticProjectionRemovesPlusTwo\` and \`incorrectQuadraticFoldCreatesMinusOne\`: correct truncation vs 3-point alias.
- **F5.2** [S] \`wideModeAliasCollision\`, \`foldedThreePointModeCannotRecoverExactFourierIndex\`, \`rechartingThreePointModeCannotFixAliasing\`: reuses generic nonfactorability. Kernel check pending.
- **F5.3** [S] **want:\`integerQuadraticConvolution27\`**: for arbitrary coefficients in an agreed ring/field, sum all integer-exact input pairs into output coefficients for \`k∈[-2,2]^3\`.
- **F5.4** [S] **want:\`projectionAfterConvolution\`**: define canonical integer Galerkin \`P_1(u*v)\` on \`[-1,1]^3\`, independent of sampled-grid aliasing.
- **F5.5** [N] **want:\`threeGridCounterexampleAtRetainedCoefficient\`**: formalize at least one genuinely nonzero erroneous retained quadratic coefficient, not merely a mode-label collision.
- **F5.6** [S] **want:\`fivePointGridInjectiveOnQuadraticSupport\`**: if all component sums lie in \`[-2,2]\`, reduction mod five is injective on that integer support.
- **F5.7** [N] **want:\`paddedFiveGridMatchesTrueProjectedProduct\`**: finite DFT orthogonality + previous injectivity yields \`P_1(FFT5⁻¹(FFT5(u)·FFT5(v)))=P_1(u*v)\` for **every** 27-coefficient input pair, not just 27 balanced-amplitude sample cases. Here `E` zero-embeds Fourier coefficients into the five-point grid on each axis; `DFT5` and `IDFT5` must have mutually consistent normalization. The right side `u*v` means exact integer-index Fourier convolution, not pointwise multiplication of coefficient arrays.
- **F5.8** [N] **want:\`threeGridHasNoUniversalExactness\`**: derive from F5.5 the impossibility of a universal equality for unpadded N=3.
- **F5.9** [N] **want:\`codecTransportPreservesPaddedProduct\`**: prove the exact codec diagram commutes with the *correct padded and projected* operator, with proper coefficient precision and sign data.
- **F5.10** [N] **want:\`finiteOperatorStatementDoesNotRequireLargeNSProof\`**: release an exact finite theorem without importing the open NS Clay/continuum assumptions.

### Gate F6 — divergence-free physical NS **finite** operator (stronger than a scalar alias witness)

- **F6.1** [R] original \`NSTriadKNComplex3ExactCarrier\`, \`NSCross369OrientationBridgeExact\`, and \`NSIntegerFourierLattice\`; do not identify a complex **3-vector** with cyclic group \`C3\`.
- **F6.2** [N] **want:\`transverseCoefficientBundle\`**: type \`û(k)∈ℂ³\` with \`k·û(k)=0\` for each integer \`k≠0\`, including a policy for zero frequency.
- **F6.3** [N] **want:\`conjugateRealityCondition\`**: if aiming at a real velocity field, pair \`û(-k)=conj(û(k))\`; the two-mode rational demo is not yet a complete real-valued NS field.
- **F6.4** [N] **want:\`lerayIdempotentAndTransverse\`**: for each nonzero integer k, prove \`P_k²=P_k\` and \`k·P_k v=0\` using the original scalar-field law package.
- **F6.5** [N] **want:\`nsQuadraticPairKernel\`**: exact Leray-projected vector convective term \`-i P_k Σ_{p+q=k}(û(p)·q)û(q)\` on the chosen finite Fourier support, with sign and factor conventions pinned.
- **F6.6** [N] **want:\`nsIntegerKernelRespectsTrueTriads\`**: proof that every kernel term uses *integer* \`p+q=k\`, not modulo-3 alias pairs.
- **F6.7** [N] **want:\`noncollinearTransverseAliasWitness\`**: translate executed rational example \`p=(1,0,0),q=(1,1,0)\`; \`a=(0,1,0), b=(1,-1,0)\`; show \`P_(2,1,0)(1,0,0)=(1/5,-2/5,0)\` but \`P_(-1,1,0)(1,0,0)=(1/2,1/2,0)\`. This is **not** presently an Agda kernel result.
- **F6.8** [N] **want:\`actualRealFieldAliasWitness\`**: optionally add conjugate modes and recompute the full vector nonlinearity so the witness is an admissible *real* divergence-free finite field rather than only a pair algebra receipt.
- **F6.9** [N] **want:\`NSProjectedPaddedGridBidi\`**: prove the exact finite incompressible NS Galerkin nonlinear operator is reproduced by an alias-free padded sampled-grid implementation, including the Leray projector at the **true** output k.
- **F6.10** [N] **want:\`finiteGalerkinEnergyCancellation\`**: derive the exact skew-symmetry/energy cancellation for the finite NS quadratic operator under the pinned periodic volume/inner-product normalization.
- **F6.11** [N] **want:\`finiteGalerkinLocalODE\`**: tie finite-dimensional Galerkin coefficients to a local ODE with standard regularity assumptions (polynomial RHS). This is routine mathematics but not paid by the current trit codec.
- **F6.12** [N] **want:\`finiteGalerkinUniformEnergyEstimate\`**: finite-cutoff energy identity/inequality with the correct viscosity/forcing assumptions; do not call this global cutoff-independent regularity.
- **F6.13** [N] **want:\`finiteDSpaceDoesNotProveContinuumClay\`**: no promotion from F6.9–F6.12 to any global NS regularity theorem.

### Gate M — real optical-lattice **different operator**, separate outcome

- **M1** [R] use Ma et al., arXiv:2610.17499v2, \`H=p²/(2m)-U497 sin²(k497 z+φ)-U813 sin²(k813 z)\` as source-owner, not P3 site adjacency.
- **M2** [S] Ma source-selected supercells \`18:11,85:52,139:85,175:107,265:162\`, exact **nominal-label** integer products, not measured-wavelength error.
- **M3** [S] S6 Fourier supercell offsets \`±11,±18\` absent in \`-1,0,+1\` truncated plane-wave basis; keep separate from NS quadratic aliasing.
- **M4** [A] **want:\`continuumHamiltonianFiniteCutoffSelfAdjoint\`** at supplied potential, boundary convention and actual calibrated wavelengths; cite Ma's original construction.
- **M5** [A] **want:\`sourceSupercellFourierMatrixCorrect\`**: derive full S6 basis matrix, kinetic normalization and sideband entries; a three-mode stencil cannot substitute for S6.
- **M6** [A] **want:\`supercellConvergenceErrorBound\`**: compare all 5 rational approximants and basis cutoffs in a source-appropriate norm, spectral/line-pulling observable and temperature. Nominal 497/813 integer mismatches are not the physical convergence error.
- **M7** [A] **want:\`WannierAAProjectionWithError\`**: justify the tight-binding reduction from the continuum Hamiltonian, with calibrated \`J,Δ,β,φ\`, tunnelling and finite-size errors.
- **M8** [A] **want:\`localizationSpectroscopyCorrespondence\`**: physical linewidth/Ramsey/line-pulling and systematics tied to Ma's actual source data and uncertainties. Do not infer R2P2 Yb trap parameters.

### Gate R — real R2P2 comparator (independent physical outcome)

- **R1** [A] **want:\`r2p2IsotopeAndTransitionSource\`**: source-verify actual neutral-Yb isotope and interrogation transition for **both** R2P2 clocks; 171Yb remains a model example until sourced.
- **R2** [R/S] existing \`R2P2MountainOpticalClockComparisonExact\` synthetic comb/primary abstract; \`R2P2369WaveOpticalCombInformationCutExact\` signed beat collision; kernel status unconfirmed.
- **R3** [A] **want:\`r2p2SignedCombObservableProducer\`**: mode number, \`f_rep\`, \`f_CEO\`, signed beat branch, trace timestamps, cycle slips, link/clock distinction.
- **R4** [A] **want:\`r2p2TwoWayTransferNonreciprocityBound\`**: 69 km atmospheric and 81 km fibre phase/time transfer, physically calibrated asymmetric path noise and uncertainty.
- **R5** [A] **want:\`r2p2CalibratedClockRatioAndCovariance\`**: same-epoch source-produced ratio with common-mode and differential systematics.
- **R6** [A] **want:\`r2p2GeopotentialAndRedshiftUncertainty\`**: independent surveyed geopotential and weak-field GR expectation with correlated uncertainties.
- **R7** [S/A] \`R2P2ClockBiasIdentifiabilityMaxCutExact\` synthetic two-lever-arm example shows ambiguous single lever arm; actual independent baselines required to identify bias and slope.
- **R8** [S/A] \`R2P2ThreeClockLoopClosure369Exact\` finite synthetic ratio product; real third clock/network has **not** been supplied by two-clock R2P2.
- **R9** [A] **want:\`r2p2PrespecifiedAlternativeModelDiscrimination\`**: full likelihood/covariance and apparatus bias controls before claims about departures from GR; no quantum gravity inference from a finite ternary grid.

### Gate C — global NS analytic/Clay frontier (NOT implied by finishing F)

The *existing* \`NSABCDConcentratedCompletionCutExact\` on master and distinct open PRs #1384 (cross-gradient), #1391 (instantaneous snapshot), #1279 (369 orientation/Gram) are the owners. These are **genuinely separate** mathematicians' research-level obligations; the list states their *interfaces*, not an assertion that they suffice to solve the unproved Clay problem:

- **C1** [A] **want:\`cutoffUniformConvolutionMajorant\`**: real whole-space low/high integrability with correct low-frequency compensation and high-frequency resolvent decay, as required by the canonical A lane.
- **C2** [A] **want:\`signedLebesgueAggregationSameObject\`**: actual R³ signed field, compensated integral and Fourier-domain identification; no discrete-sum ↔ continuum-integral promotion.
- **C3** [A] **want:\`crossGradientQuantitativePayment\`**: live periodic-B \`p·q\`/cross-gradient bound on correct physical slots and weights, not just mode-counting.
- **C4** [A] **want:\`highHighGramRayleighUniformBound\`**: quantitative \`λ_min(K_N(A))≥c/N\` (or chosen actually necessary replacement), uniform in the physical cutoff; generic 369 geometry/729 incidence does not pay it.
- **C5** [A] **want:\`BonyThreeClassUniformMajorants\`**: signed far-low/high-high/comparable estimates on original live class carrier, correctly separating homochiral/heterochiral channels.
- **C6** [A] **want:\`cutoffStableCompactnessAndLimit\`**: subsequence and weak/strong convergence strong enough to pass nonlinearities and claimed regularity, tied to actual norms.
- **C7** [A] **want:\`existingCDReleasedAuditSufficiency\`**: independent native Option C/D proof obligations under original Fefferman/Clay target hypotheses; no release proof imported by an optimistic flag.
- **C8** [A] **want:\`globalRegularityOrQualifyingCounterexample\`**: the actual Clay target, not a finite Galerkin theorem, a negative instantaneous rate, a simulated receipt or an analogy.
- **C9** [A] **want:\`sameObjectContinuumNSFinalCertificate\`**: after genuine mathematical achievement, pinned original theorem, exact assumptions and kernel-level or independently peer-reviewed evidence. None claimed at present.

### Gate I — Pareto/snowball/Ibrahim and 27/729 source identity firewalls

- **I1** [R] \`Base369TernaryDeltaBasisCrossPollinationExact\`: \`TritCube 6\` has 729 labels and exact finite point-mass decomposition. **Do not identify** 729 Fourier ordered pairs with its appraisal semantics automatically.
- **I2** [R] \`Base369Ternary27SpectralGeometryValidation\`: 27 voxel, 729 appraisal fibre, 19683 three-voxel fabric; periodic C3³ ≠ nonperiodic P3³, character labels ≠ proven physical eigenvectors.
- **I3** [B] #1105 selected \`GF(3^6)\` field action and #1250 pointed 720+9/3B source cuts: equal 729 **cardinality** does not transport multiplicative field, representation, projector or physical Fourier operators.
- **I4** [B] #1249 punctured-27/13 antipodal-pair geometry and #1386/#1390 Fin27 ABI: only rebase/import after explicit branch ownership, type agreement, head-check, and distinct same-object map. Original 3B/Albert/Ibrahim attribution survives.
- **I5** [R/N] \`BalabanIbrahimParetoSnowballTOEExact\` and original Ibrahim snowball/frontier sources: cross-source searches rank unresolved *evidence producers*, never replace theorem proofs or physical measurements.
- **I6** [N] **want:\`noEvidentialPromotionFromIncidenceCounts\`**: hard gate between 27²=729 combinatorics, 729 field points, Heisenberg 729, 720+9, C3³ voxel, code indices, and real Fourier/clock observations.
- **I7** [N] **want:\`claimSpecificTerminalGate\`**: independently judge F, M, R and C, never one global \`TOE complete\` Boolean.

### Minimal dependency graph / release gates

\`\`\`text
G0 kernel + executed tests + attribution  [MUST RUN FIRST]
  ├── F1 exact codecs/bijective modes
  │    ├── F2 sign != modulo != path adjacency
  │    ├── F3 typed 27x27 = 729 actual pair incidence
  │    └── F4 full 27 DFT/point-mass/function algebra
  │          └── F5 true convolution/projection vs alias, exact N=5 remedy
  │                └── F6 physical finite complex3/Leray/Galerkin operator
  │                      ├── FINITE release F (kernel+tests+clear semantics)
  │                      └── C1..C9 independent NS analytic/Clay frontier
  ├── M1..M8 Ma 87Sr supercell and calibrated spectroscopy (independent)
  ├── R1..R9 Triano R2P2 Yb transfer/redshift data (independent)
  └── I1..I7 same-object/attribution guards across every path
\`\`\`

**Pareto sequencing:** P0 **kernel/check-run and sign-vs-modulo distinction**; P1 typed 27↔Fin27 and 729 ordered-pair equivalence; P2 true 3D quadratic convolution + 3-grid alias + 5-grid exactness **for arbitrary coefficients**; P3 nonzero real-valued, transverse Leray/Galerkin witness and energy identity; P4 only then optional phase-shifting/2/3 dealiasing optimizations. M/R require original experimental producers and C requires genuine analytic theorems. Do not spend first on another 729 carrier name, synthetic receipt, Monster fingerprint or tertiary code wrapper.

**Exit F:** exact-head reproducible Agda kernel-green, complete 729-pair incidence proof, arbitrary-coefficient operator equality for N=5 and correct projection, explicit sign/modulo/path separation, original codec roundtrips, sufficiently typed NS finite algebra and no scientific overpromotion. **Exit M/R/C:** each has its own external physical/mathematical criteria; F success does not imply any of them.
