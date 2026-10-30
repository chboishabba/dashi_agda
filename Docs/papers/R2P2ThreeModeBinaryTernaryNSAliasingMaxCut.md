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

**Further inspected existing NS owner:** `DASHI.Physics.Closure.NSTriadKNFiniteConvolutionReconstruction` already provides an original source-owned finite-cutoff ordered-triad carrier, sound/complete/unique membership, pair-symmetrisation and `ExactFiniteFourierConvolutionAuthority`. These use the native original NS lattice, physical shell and exact scalar abstraction. The newly constructed 27×27 cyclic-index owner is a separate small finite test carrier. F6 must provide a **typed shape/weight map** into the existing physical ordered-triad owner and preserve its physical projection, rather than reimplementing a supposedly new NS Galerkin law. Original proof ownership remains in that module. Existing `NSTriadKNLuoFiniteFourierInversionFromResolutionExact` and `NSTriadKNLuoFiniteFourierParsevalFromInversionExact` are reusable *generic theorem interfaces* given character-resolution/inversion data; they do not furnish the specific missing C4/C5 character authority without a new instantiation.

**Ibrahim/snowball reuse boundary:** `DASHI.Wikimedia.IbrahimSnowballParetoFrontierExact` already has a source-native `ParetoFrontierLeaf` and ranks producer/source custody, attribution and evidence gaps. `DASHI.Unified.BalabanIbrahimParetoSnowballTOEExact` already bars turning search priority, source code, 729 numerology or route preference into a proof, runtime receipt or Monster recognition. We **reuse their policies without editing their historic record, changing their ranks or importing Monster action semantics**. Here the Fourier Pareto objectives are mathematically explicit sampled-grid capacity and *which frequency outputs are preserved*; those objectives are not Ibrahim's historical source-custody objectives. Attribution and same-object gates remain intact.

**Outstanding precise proof obligations (additional refinements to the 106 main ledger entries):**
1. **want:`C4FourierWithInverseAndConvolution`**: use original source Fourier components if possible; otherwise explicitly construct the true `64`-point `C4³` Fourier transform, root-of-unity normalization, inversion and group-convolution theorem for a field embedding that preserves actual complex coefficient identities. The previous `C3³` theorem is for order 3, not for order 4.
2. **want:`C4SampledProductEqualsRetainedIntegerGalerkin`**: use the source-written `Z/4` group-sum compatibility + actual DFT4 group convolution theorem to show the *sampled physical-space pointwise quadratic product* reproduces the retained `Z³` Galerkin coefficient for arbitrary complex-valued 27-mode inputs, including normalization and projection.
3. **want:`C5FourierWithInverseAndConvolution`**: likewise build or import the actual `125`-point `C5³` Fourier authority, with an adequate cyclotomic fifth-root field; the inherited `ℚ(ω)` 27-point group Fourier theorem **cannot** simply be renamed `C5`.
4. **want:`C5SampledProductEqualsFullIntegerConvolution`**: show the complete 125-output wide spectrum, not just projected retained outputs, matches a genuine `DFT5`/inverse sampled-field computation.
5. **want:`finiteRealDivergenceFreeComplex3LerayTransport`**: original complex-vector NS/Leray and conjugate reality must be preserved through the actual 64/125 sample-space operator; a generic scalar incidence law is not a physical NS regularity theorem.
6. **want:`kernelChecksAndSourceDataGates`**: no source-written `refl` witness is promoted to an Agda kernel theorem without executing the focused checked imports, all three TOE roots and relevant tests. Real Ma 87Sr, Triano R2P2 neutral Yb and original Ibrahim/Monster 3B sources remain separate.

This is an actual Pareto decision: target the **64-point retained-mode FFT theorem first**, because it pays the useful physical NS finite Galerkin projection with fewer samples; add the 125-point full-spectrum FFT only when the complete quadratic spectrum is an explicit consumer. The original 27-point `C3³` algebra is now an inherited DFT owner and a concrete alias counterexample, not a substitute for either C4 or C5.

## 5d. Source-native 13-in-27 and five-in-nine antipodal Fourier symmetry

**Reused original mathematical/proof owners**: `DASHI.Foundations.BalancedTernaryAntipodalOrbitExact`, `BalancedTernaryAntipodal369OrbitHierarchyExact`, and `BalancedTernaryHypercubeAntipodalOrbitCountExact` already construct a global *C2 sign involution* and its quotients. **Jean-Pierre Serre**, *Linear Representations of Finite Groups* (1977), remains the original group-action/representation root. `TernaryNineAntipodalD4SeparationExact` originally proves the strict 5-in-9 classes are NOT automatically the five D4 irreducible species; the D4 geometric nine-cell orbit quotient has only three orbits (centre, edges, corners). The source-owned `C3CubeCyclotomicFourierExact` supplies exact Q(ω) conjugation, including `conjugationInvolutive`. Related open prior owners [#1249](https://github.com/chboishabba/dashi_agda/pull/1249) (punctured 27 / 13 pairs), [#1250](https://github.com/chboishabba/dashi_agda/pull/1250) (Monster 3B action), [#1386](https://github.com/chboishabba/dashi_agda/pull/1386) and [#1390](https://github.com/chboishabba/dashi_agda/pull/1390) (ternary codec) retain their independent branch authorship. No open-only imported theorem was treated as merged.

### The correct numerical interpretation

| Finite carrier | Fixed zero | Nonzero C2 antipodal pairs | Orbit classes | Hermitian Fourier scalar storage |
| --- | ---: | ---: | ---: | --- |
| T², 9 signed mode labels | 1 | **4** | **5** | 1 real centre + 4 conjugate-complex values = 9 real scalar components |
| T³, 27 signed mode labels | 1 | **13** | **14** | 1 real centre + 13 conjugate-complex values = 27 real scalar components |
| T⁶, 729 ordered input pairs | 1 | **364** | **365** | Pair-address action only; does not imply amplitude reduction or symmetric NS kernel without a proof |
| T³ on wide `[-2,2]³`, 125 output labels | 1 | **62** | **63** | If conjugation symmetry of the output convolution is established |

**13-in-27 refers to 13 *pairs*, not 13 total classes**; **five-in-nine refers to five *classes*, not five nonzero pairs**. Neither property changes the real degrees of freedom of an unconstrained real Fourier field. Most importantly, no cardinality argument constructs a Monster 3B/GF729 representation or a D4 representation-theoretic equivalence.

### Source-written Agda cross-pollination

- `R2P227729AntipodalThirteenFiveOrbitFourierCutExact.agda` imports **the actual existing orbit classifiers**, not new quotient carriers. It constructs a three-axis signed Fourier antipode and a commutative embedding of the five plane orbit classes into the 14 cube orbit classes; inherits `27=1+13·2`, `9=1+4·2`, and the existing 5/14-class counts. It proves the original D4 distinctness flag, `negateCube` involution, and **true integer quadratic sum negation covariance** `sum(-p,-q)=-sum(p,q)` on the original 729 pair inputs and 125 wide outputs.
- The essential **negative result** is `noIntegerPairOutputFromOnlyOrbitLabels`: the pair `(+x,+x)` and `(-x,+x)` have **identical ordered pairs of antipodal input classes** but true integer outputs `(+2,0,0)` and `(0,0,0)`. The original `IntersectionalNonFactorability` witness proves that no function of the antipodal input labels alone can determine every true quadratic Fourier output; later recoding/recharting cannot recover the discarded sign. Hence an orbit quotient is NOT, without phase/sign residuals, a homomorphism of the Fourier convolution operator.
- `R2P227729HermitianThirteenPairFourierCodecExact.agda` constructs genuinely **lossless real-signal codecs**: one exact ℚ centre plus **9+3+1=13** `Q(ω)` values from the existing positive-first, positive-second, and positive-third orbit constructors, and an independent **1 real + 4 Q(ω)** compact plane codec. Crucial preconditions: input `f(-k)=conj f(k)` at each frequency and real zero-mode. The `decodeAfterEncodeHermitian27` and `decodeAfterEncodeHermitian9` roundtrips are source-written proof terms **not yet kernel-certified**. They do not claim arbitrary complex 27-mode compression.
- Original C3 cube Fourier has a full exact DFT and conjugation operation, **not** a theorem that bare orbit labels reproduce the original nonlinear NS/clock Fourier kernel. With conjugate-aware storage, the decompressed signed field can be passed into the existing exact 27/729 integer-frequency operator; an actual 13-orbit reduced convolution formula with orientation and conjugate weights is a **new remaining lemma**, not automatically a consequence of the paired counts.
- `scripts/r2p2_13in27_5in9_hermitian_symmetry.py` and `tests/test_r2p2_13in27_5in9_hermitian_symmetry.py` implement independent exact-fraction Q(ω) storage, 9/27 unpacks and 729-pair convolution; the separate local Python audit (not an exact checkout run) checked 14/5 orbit classes, 13/4 nonzero pairs, 365 ordered-pair orbits and 63 wide-output orbits. It confirmed all 27 and 9 Hermitian coefficients recover exactly, and the **125-output product of two independent Hermitian fields remains conjugate symmetric**. This latter computation is not yet an Agda proof of a permutation of all 729 indexed sum terms.

### Operator transport completed at the signed-index level (source-written, kernel pending)

The new `R2P227729HermitianConvolutionTransportExact` now defines the **actual consumer** of the compact centre+13-pair data: decode each pair's full signed Q(ω) coefficients, then evaluate the already-owned full 729-term true integer convolution. `compact13PairTransportPreservesAll125IntegerOutputs` proves pointwise equality with the original full bilinear operator for every pair of independently supplied `Hermitian27` inputs and every wide frequency. `compact13PairsPreserveFourGridRetainedQuadratic` and `compact13PairsPreserveFiveGridFullQuadratic` compose that theorem with the earlier 64-retained/125-full cyclic-index Pareto results. **There is no new faster 13-only FFT or NS solver**: this theorem pays semantic compatibility of the compression, not a complexity speedup.

The new `R2P281PlaneHermitianFiveOrbitConvolutionExact` builds an independent literal nine-mode plane enumeration, **9²=81 ordered input pairs**, and **5²=25 wide output-frequency labels**, again using the original Q(ω) multiplication. `fiveOrbitPlaneCodecPreservesAll25QuadraticOutputs` proves a pairwise-sum extensionality theorem: the centre + four conjugate orbit amplitudes, when decoded, yield the same full 81-term plane integer convolution at every output. The 9-plane orbit-to-27-cube embedding remains a separate source-written bridge, not a D4 character identity.

The separately executed local exact-fraction audit now checks **two actually distinct** Hermitian input arrays, their fully signed 729-pair product and the conjugate-reality property at all 125 outputs, plus two distinct nine-plane arrays and 81-pair products at all 25 outputs. In both dimensions, actual convolution outputs computed from the compact packed representation match the original full signed coefficient arrays. This is a computational result, *not* a committed-checkout test receipt and *not* an Agda kernel certificate.

### Even-grid Nyquist exception: the original 13/27 code does not blindly become a 64-grid code

A further reuse-first finite index module, `R2P2C4C5NyquistAntipodalFixedPointExact`, applies the same global-negation question to the **actual cyclic Z/4 and Z/5 output indices** used by the Fourier Pareto result. The original C3 count/hierarchy is *odd-grid* and has a unique fixed zero frequency. At even grid size N=4, **Nyquist 2 ≡ −2 (mod 4)** is also fixed under negation on every axis, so every frequency whose three coordinates are each zero or Nyquist is self-negative.

| Grid | Frequency bins | Self-negative indices | Nonfixed inversion pairs | Total C2 orbits |
| --- | ---: | ---: | ---: | ---: |
| Original C3³, signed 27 cube | 27 | **1** | 13 | 14 |
| Pareto C4³, retained-output grid | 64 | **8** | 28 | **36** |
| Full C5³ output grid | 125 | **1** | 62 | **63** |

The new Agda module includes the explicit cyclic negation tables, involution, signed-frequency compatibility, all 64/125 grid enumeration, eight/one fixed-point counts, and `64=8+28·2` and `125=1+62·2` equalities. It leaves original C3/27 antipodal and D4/Monster authorship unchanged.

The updated pure-Python exact Q(ω) diagnostic takes **two distinct conjugate-symmetric source fields**, computes all 729 integer-frequency products, and folds their resulting 125 coefficients onto both cyclic grids. The resulting 64 coefficients obey the cyclic Hermitian involution; the **eight Nyquist-corner coefficients are real**. All 125 output coefficients likewise obey Hermitian symmetry on the five-grid, whose only fixed centre is real. These are independently executed exact-fraction checks, **not Agda kernel theorems or a physical-space C4/C5 DFT implementation**.

**New high-alpha FFT proof obligation:** any actual real-signal C4³ packed sampled-frequency carrier must store **eight independent real fixed-corner values and 28 conjugate pairs**, not one real centre plus 13 pairs. Actual C5³ packed output uses **one real centre and 62 conjugate pairs**. Neither packing is an inherited literal 13/27 codec. Further requirements are C4/C5-specific transform roots, inversion/Parseval/convolution theorems, and a typed link from the real packed FFT to the original Q(ω) integer coefficient consumer.

### Pareto effect and actual next interfaces

The strongest immediate application is **Hermitian half-spectrum storage** for a real scalar finite Fourier field. This can reduce complex storage and duplicated conjugate computations, but **not** the number of physical real degrees of freedom, the actual integer convolution support, or automatically the number of complex-vector NS operations.

Outstanding **want** contracts, on top of existing F1–F6:
1. `paired729ConvolutionHermitianByReindexing`: prove, under the existing exact `Q(ω)` multiplicative-conjugation law and pair-index involution, that `output(-k)=conj(output(k))` for ALL arbitrary Hermitian left/right input fields. The source already has pair-sum negation covariance. The missing part is a **finite-list permutation/reindexing theorem**, preferably reuse `NSTriadKNFiniteConvolutionReconstruction` original permutation/symmetrisation machinery.
2. `compact13OrbitBilinearConvolutionBidi`: **codec-to-existing-729-operator semantic transport now source-written** as `compact13PairTransportPreservesAll125IntegerOutputs`. Remaining optimisation: derive a genuinely lower-work orbit-aggregated implementation *without* decoding all 729 terms, with correct signed, conjugated and multiplicity-weighted channels. Never infer it from a quotient group law (one is disproved).
3. `compactFivePlaneConvolutionBidi`: **nine-plane 81-pair/25-output semantic transport now source-written** as `fiveOrbitPlaneCodecPreservesAll25QuadraticOutputs`. Remaining: prove plane-support injection into full 27-mode bilinear convolution and construct a genuine four-orbit weighted fast evaluator.
4. `realFieldLerayComplex3Conjugacy`: tie scalar Hermitian symmetry to original `Complex3` transverse velocity, physically correct `P_{-k}=P_k`, signed Fourier derivative and pressure projection; no global regularity inference.
5. `fft4/fft5HermitianPaddedOperatorBidi`: existing 64 retained vs125 full cyclic-index Pareto survives the codec, but the actual **C4/C5 sampled-space FFT with normalization** still must be proved.
6. `provenanceSameObjectAndKernelGate`: ensure D4 orbit geometry/irrep species, GF729, Monster 3B character fingerprints, laboratory Yb/Sr observations and analytic NS estimates remain separate from this elementary C2 orbit storage theorem.

**Verification**: new Agda files, roots and docs are source-written on PR #1407. Exact arithmetic independently checked in local Python. Agda kernel not run (no Agda executable installed locally); exact-branch committed unittest suite not executed; user asked to ignore CI. All authorship, original primary roots and the source-written/executed/kernel distinction remain visible.

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

### 5e. Pair-orbit 365 canonicalization (29 October 2026)

The existing source-owned 13-in-27/five-in-nine Antipodal/Hermitian PR lane already contains the necessary sign, conjugation, Nyquist and 729 pair inversion laws. Rather than duplicate those, `R2P227729PairOrbit365CanonicalSymmetryExact.agda` now reuses their actual `simultaneouslyNegateOrderedPair` involution and existing full `pair729` enumeration. It defines a lexicographic `positivePair` decision by the first nonzero coordinate of the first input, then of the second input if the first is zero; `canonicalPair` chooses the pair or its simultaneous antipode. The source-written reductions `oneActualCentralPair` and `actualPositivePairRepresentatives` target exact counts **1** and **365**, respectively; the already-owned output covariance is imported by its exact theorem name. Independent local Python enumeration on all 729 distinct pair inputs returned **365** canonical distinct class representatives, **365** positive-side pairs and **one** inversion-fixed centre. There is still no Agda kernel receipt, no orbit-weighted 365-term accelerated bilinear NS convolution theorem and no demonstration that separately quotienting each input preserves the output (it does not). Original mathematical and repository owners retain attribution, and no Monster/Heisenberg/clock same-object recognition is inferred. Existing protected ESD files and CI were not edited.


## 5e. 29 October 2026: 365-orbit Q(omega) event compiler and Q(i) C4 sampled product

**Head continuation:** source-authored in PR #1407; no Agda kernel run or exact-branch regression execution. The local standalone Python arithmetic was executed, but is not a pinned checkout execution receipt.

### Highest-alpha A: 365 actual multiplication events, not merely 365 labels

Original authority is unchanged: `BalancedTernaryAntipodalOrbitExact` owns 13-in-27/5-in-9 C2 classifications; `R2P227729PairOrbit365CanonicalSymmetryExact` owns the actual positive-side classification and count of 365 representatives; `C3CubeCyclotomicFourierExact` owns Q(omega) and multiplicative conjugation; `R2P227729BilinearCyclotomicPadCutExact` owns the ordered 729-pair convolution.

New module `R2P227729OrbitWeighted365ConvolutionExact.agda` constructs the actual filtered 365-element list and computes **one Q(omega) multiplication per canonical pair**. For a representative (p,q), it emits (p+q,f(p)g(q)); if (p,q) is not the unique (0,0) fixed point it also emits (-p-q,conj(f(p)g(q))) *without a second multiplication*. Its `reflectedEventIsConjugate` statement uses the inherited Hermitian input constraints, integer-sum negation law and exact multiplicativity of conjugation, for two distinct input coefficient fields. The 365 representatives emit 729 weighted events. The updated independently executed Python check also constructed the entire reflected pair-address list and compared it as a multiset with all 729 original addresses. It passed exact no-duplicate/exhaustive coverage. The analogous 41 -> 81 address permutation was checked independently in the same run.

This differs from mere 13-pair packed-input storage: it avoids 364 of the 729 coefficient multiplications of a naïve pair loop. It does not claim the overall runtime is 2x faster. There are still 729 event updates, conjugations, aggregation and indexing costs.

**Proof status:** the per-pair reflected identity and count are source-written Agda; full-list permutation / sum equality of the 729 emitted events with the original lexicographic 729 ordered events remains an *explicit kernel obligation*. No such theorem is silently assumed. Standalone local Python `r2p2_orbit365_check.py` independently ran 12 different exact Q(omega) Hermitian pairs of fields and matched all 125 output coefficients. The corresponding committed reproducible script is `scripts/r2p2_27x27_orbit365_weighted_convolution.py` with test `tests/test_r2p2_27x27_orbit365_weighted_convolution.py`. Its presence is not a claim that the committed exact-head test itself ran.

The exact 2D nine-mode analog is 81 = 1 + 40×2 ordered input pairs and is **now source-written in the same Agda module** as a 41-multiplication event compiler. It directly reuses `R2P281PlaneHermitianFiveOrbitConvolutionExact` for true 25-label plane outputs and the original `Hermitian9` source. The new `reflectedPlaneEventIsConjugate` proves the per-pair mirror identity, and the explicit canonical 41-list emits 81 events. Three TOE roots also project the count and the reflected event law. Local standalone exact Q(omega) comparison passed twelve pairs of independently generated plane fields across all 25 true integer outputs. The corresponding repository script was updated. **Agda kernel checking and the complete 81-event list-permutation/sum theorem remain open.** No five-class D4 irrep interpretation is inferred.

### Highest-alpha B: a genuine sampled-field C4³ finite theorem, at paper level

Let K={-1,0,1}³. Let `Q(i)` be the Gaussian rational field, and let `chi_k(x) = i^(k·x)` for x∈(Z/4Z)³. Use the **unscaled** inverse synthesis `U(x)=sum_{p∈K}u_p chi_p(x)` and the **1/64-normalized** forward Fourier coefficient `F4(h)(k)=(1/64) sum_x h(x) chi_{-k}(x)`.

For arbitrary u,v : K→Q(i), direct finite distribution gives

```text
F4(U·V)(k)
  = sum_{p,q in K} u[p]v[q] (1/64) sum_{x in C4³} i^((p+q-k)·x)
  = sum_{p,q in K; p+q ≡ k (mod 4)} u[p]v[q].
```

The second equality is finite character orthogonality. Each coordinate of p+q is in [-2,2], whereas the retained k coordinate is in [-1,1]. Thus p+q-k lies in [-3,3]; its only multiple of 4 is zero. Therefore for **every retained k**, `p+q ≡ k (mod 4)` iff `p+q = k` as *integer* vectors. This establishes at the mathematical (non-kernel) level:

```text
for all u,v : K -> Q(i), and k in K,
  F4[ (F4^-1 E u) pointwise (F4^-1 E v) ](k)
    = sum_{p+q=k, p,q in K} u[p]v[q].
```

This 4³-grid theorem is **only projected-output equality**: modulo four merges +2 and -2 (Nyquist) at the unretained full-product indices. Five samples per axis are needed to preserve all 125 signed output frequencies without collision. An arbitrary Q(omega) C3 carrier cannot supply an honest fourth root of unity; Q(i) is used here and the existing C3 transform is not mislabelled C4.

**Reproducibility:** standalone local exact rational Python executed 64 finite C4³ orthogonality checks and eight independently populated, distinct complex two-field coefficient profiles. All 27 projected outputs matched exact integer convolution. Committed `scripts/r2p2_c4_3d_exact_sampled_quadratic_dft.py` and `tests/test_r2p2_c4_3d_exact_sampled_quadratic_dft.py` hold the implementation and check. Their exact-branch checkout execution is still pending. No Agda kernel formalisation of the Q(i) three-dimensional DFT, inverse, orthogonality, and projected multiplication has been completed.

### Pareto/max-cut and snowball ledger after this tranche

| Obligation | Evidence grade | Status |
| --- | --- | --- |
| 27 input labels, 729 signed pairs, 365 simultaneous antipodal orbits | Existing owner + source-written Agda + independent counts | Established finite computational evidence; kernel pending |
| 365 representative single-product event compiler and per-event conjugation | New source-written Agda, local exact Q(omega) tests | Implemented; global reindex/permutation proof open |
| 4³ sampled multiplication equals all retained true integer convolution coefficients | Algebraic character proof in this document + local Q(i) exact checks | Mathematical proof supplied; Agda formalisation open |
| Full 5³ sampled product and all 125 frequency coefficients | Source-written index theorem, not sampled ζ5 Fourier | Open |
| Complex3 transverse vectors, Leray, Hermitian reality, finite Galerkin energy | Reuse original `NSTriadKNFiniteConvolutionReconstruction` and NS physical sources | Open same-object integration |
| Cutoff-uniform NS high-high bounds and continuum Clay conclusion | Original analytic NS owners | Open; nothing here proves them |
| Ma Sr optical lattice and R2P2 Yb clock/calibrated residual | External original scientific measurement owners | Open and empirical |
| Ibrahim / Monster 3B; GF(729), 720+9 | Distinct original repository proof ownership | No new same-object evidence, no promotion |
| All three TOE roots | Direct imports and projection theorems | Source-written, kernel pending |
| CI and ESD | Left untouched | User scope respected |

### C4 source-written formal Fourier character checkpoint

A further new owner, `DASHI/Physics/Closure/R2P2C4GaussianFourierCharacterExact.agda`, has been added and connected to all three TOE roots. It implements exact Gaussian rational arithmetic, four actual roots `1,i,-1,-i`, a 16-case `Z/4Z` scalar multiplication table distinct from group addition, 16 source-written cases for `root4(a+b)=root4(a)*root4(b)`, and 16 source-written exact character orthogonality cases `sum_x χ_k(x) conjugate(χ_l(x))=4 δ(k,l)`. It tensors those one-axis laws into a source-written `C4³` orthogonality statement and a self-norm-64 witness. This uses the original `FourGridRetainedQuadraticParetoExact.fourGroupAdd` rather than introducing a parallel C4 group. **Agda kernel not run.** Its complete normalized 64-point forward/inverse transform and sampled bilinear multiplication identity remain separate source formalisation tasks, even though the corresponding mathematical identity is proved above and checked independently in local Python.

The four-grid module retains the explicit eight Nyquist self-inverse frequency corners. They must remain special in any future Hermitian real-field C4 DFT implementation. The C4 Fourier root is not the previously established C3 `Q(omega)` root.

**Next kernel obligations in exact dependency order:** (1) type-check the new event owner and three root projections; (2) prove `canonicalOrderedPairs` plus their simultaneous negatives are a *no-duplicate, exhaustive permutation* of the real `pair729` list, then commute finite Q(omega) addition over that permutation to establish 365-event/729-pair equality for arbitrary Hermitian inputs, and independently establish the analogous 41-event/81-pair plane identity; (3) kernel-check the newly source-written Q(i) C4 group-root, 1D and C4³ orthogonality source terms and implement the missing normalized inverse/forward Fourier transforms, then prove the sample-pointwise identity in Agda; (4) attach the theorem to the original Complex3/Leray finite NS object and prove reality and energy cancellation; (5) treat cutoff-uniform continuum estimates, five-point full spectrum and calibrated experimental data as independent exits. Do not use sibling PR monodromy #1414, Pareto scheduler #1416/#1417, or their numerology as replacement evidence.

**Attribution:** original historic finite Fourier group theory, Orszag/Patterson numerical dealiasing, Lambert–Reneuve–Augier (2026, [arXiv:2603.08892](https://arxiv.org/abs/2603.08892)) are background scientific authors; repository source proofs and their actual PR authorship remain distinct. Exact standalone computation does not become kernel type checking. The previous Ibrahim Monster 3B and other source-owner statements remain unchanged. No ESD edits and no physical or same-object Monster claim.


## 5f. 29 October 2026 — real 64-point C4 transform, operator adapter and universal C4/C5 basis certificate

**Provenance:** This extension continues the source-owned section 5e, with original mathematics by Fourier/finite-character authors and pseudo-spectral dealiasing by Patterson/Orszag. Lambert–Reneuve–Augier (2026, [arXiv:2603.08892](https://arxiv.org/abs/2603.08892)) is a contemporary comparison, not the original theorem or a source of NS regularity. Original in-repository `C3CubeCyclotomicFourierExact`, `R2P227729FourGridRetainedQuadraticParetoExact`, `R2P227729BilinearCyclotomicPadCutExact` and `NSTriadKNFiniteConvolutionReconstruction` retain their proof authorship. No ESD or Ibrahim Monster 3B owner was modified.

### Source-written 64-point Fourier forward/inverse (new)

`DASHI/Physics/Closure/R2P2C4GaussianSampledFourierBidiExact.agda` implements the actual fourth-root Fourier matrix on a `Quad` of Gaussian rationals, both normalized inverse and unnormalized forward, then transports the method of the original three-axis `C3CubeCyclotomicFourierExact` through `Quad (Quad (Quad Gaussian4))`. It includes explicit four-by-four transpose, axis roundtrips, both 64-sample inversion directions, and an actual pointwise sampled product. Agda source-written only; no kernel execution.

The matrix convention is
```text
F4  : a[x] -> sum_(x=0..3) a[x] i^(-k x)                [unnormalized]
I4  : a[k] -> 1/4 sum_(k=0..3) a[k] i^(+k x)           [normalized]
F64 = F4 tensor F4 tensor F4
I64 = I4 tensor I4 tensor I4 = 1/64 sum_k ...
```
There is no implicit substitution of the source cubic cyclotomic field Q(omega) for the fourth-root field Q(i). The original C3 DFT remains separately owned and valid for its carrier.

### Actual 27->64 sampled-field bilinear operator

`DASHI/Physics/Closure/R2P2C4RetainedSampledOperatorExact.agda` now defines:

1. `axisFromFour` and `axisToFour`, excluding the Nyquist residue 2 from the **input** signed frequencies, with an exact section.
2. `quadFromFunction` in the cyclic order 0,+1,2,-1 (not the display order -1,0,+1,2).
3. `pad27To64` as a genuine 64-cell zero-padding map, with `paddingRetainsAll27` for every signed integer input.
4. `synthesiseUnscaled = 64 * inverseFourier64` and `analyseNormalized = (1/64) * fourier64`, removing the hidden scaling ambiguity.
5. `retainedSampledBilinear`: pad f,g; synthesize both at 64 physical grid points; multiply the 64 samples; apply normalized Fourier analysis; read the 27 signed retained outputs.
6. `gaussianCoefficientOps`: instantiates the original **coefficient-polymorphic** true 729-pair convolution and four-grid index theorem at the **same** Q(i) scalar carrier. The imported original theorem yields `fourGridGaussianIndexIsTrueIntegerConvolution` for two entirely arbitrary Q(i) 27-mode input fields, with no conversion between incompatible scalars.

The remaining exact kernel equation is now between two explicitly defined functions on the **same type**:
```text
∀ f g : ModeCube27 -> Gaussian4, k : ModeCube27:
    retainedSampledBilinear f g k
      ≡ fourGridGaussianIndexConvolutionAt f g k.
```
This is not proved in Agda yet; do **not** add it as a postulate. A proof must distribute the actual 64 sampled product over two 27-term Fourier syntheses, apply C4³ character orthogonality and normalization, and reindex the finite sum via the existing 729 ordered-pair collector. Once it exists, composing with the inherited indexed theorem will establish the exact finite sampled-to-integer operator bridge.

### Universal finite basis checks — stronger than random coefficient fixtures

New committed `scripts/r2p2_c4_c5_universal_basis_certificate.py` and pytest wrapper check:

| Basis identity | Exact cases tested | Interpretation |
|---|---:|---|
| C4³ 64x64 Fourier/inverse matrix | 4,096 | All matrix elements of the character-orthogonality identity |
| C4³ 27x27 input pairs, 27 retained outputs | 19,683 | Every symbolic coefficient of `u[p]v[q]` agrees with the true integer-frequency retained convolution |
| C5³ 27x27 input pairs, 125 full outputs | 91,125 | Every symbolic coefficient agrees with the full integer-frequency convolution using the exact formal fifth-root relation `1+ζ+ζ²+ζ³+ζ⁴=0` |
| C4 full-field tensor sample identity | Three separately populated 64-sample arrays | Exact Q(i) forward/inverse equality and direct-character evaluation |
| Nyquist condition | Eight | Exactly eight C4³ inversion-fixed grid frequencies |

These **are universal coefficient/basis checks**, not merely eight or twelve random profiles: bilinearity then implies the corresponding mathematical finite identity for arbitrary coefficient fields over the relevant cyclotomic coefficient rings. The C5 audit uses four-coordinate exact representation of cyclotomic fifth roots in its character sums; it is not a completed Agda `Q(ζ5)` sampled-transform implementation. This is independent executed Python in the local runtime; **not an exact-repository-checkout test receipt**, and not Agda kernel certification.

The C4 case is exact for retained outputs only. Full outputs +2 and -2 collide modulo four. The C5 case is exact for all 125 outputs. C4 has eight self-antipodal Nyquist frequencies; any real-field inverse transform must treat their Fourier coefficients as self-conjugate (real).

### Prior art, highest-alpha and Pareto ownership decision

1. **Reuse first:** the original `NSTriadKNFiniteConvolutionReconstruction` has a proof of bag equality, list permutation, and preservation of finite ordered convolution sums under a canonical input-swap orbit reindexing. Its *method* is the right donor for the 365 simultaneous-negation orbit case. Its specific input-swap theorem must **not** be applied directly to a different action.
2. **Complete the one critical missing finite equality:** show `retainedSampledBilinear = fourGridGaussianIndexConvolutionAt` by an actual C4³ character proof over the 27/729 input/output supports.
3. **Then the orbit wall:** reuse the source proof strategy for a typed no-duplicate/exhaustive permutation from 365 canonical input pairs plus reflected mates to 729 ordered input pairs. Transport Q(omega) finite sums under that permutation. The executable address certificate is not a substitute for the kernel permutation proof.
4. **Then NS:** attach the already-proved finite operator to the **original** Complex3/Leray/triad carriers, with Hermitian conjugation, real divergence-free fields, energy cancellation and actual finite Galerkin theorem. Do not build an incompatible duplicate NS object.
5. **Separately:** cutoff-uniform high-high Gram estimates and Clay regularity are original analytic research obligations; physical Ma 87Sr and R2P2 neutral Yb calibration need real source data, covariance and systematics; C5 sampled DFT/ζ5 Agda source is not yet constructed.
6. **Ibrahim firewall:** cite original Ibrahim snowball/Pareto and Monster 3B ownership. No mere match of 27, 729, 365, 19683 or C5 character indices is a group representation, same-object Monster weld, metrological proof or independent physical observation.

Adjacent PR #1414 covers independent polynomial monodromy/S3-C3, and #1416/#1417 cover abstract Pareto worker scheduling. They were inspected for reuse priorities, not merged, copied or turned into physics authority.

### Execution and trust boundary

**Actually executed locally:** standalone exact Python 365/729 Hermitian and 41/81 plane comparisons, 4-grid sampled-product profiles, complete C4/C5 universal coefficient certificate, and the exact forward/inverse Q(i) 64-cell checks.

**Only source-written:** new Agda C4 `Quad`, `CubeSignal64` inversion, 27->64 padding/roundtrip, sampled operator, inherited 729-pair Gaussian instantiation, and their projections in the three TOE roots. No checkout-pinned pytest execution, Agda type-check, or CI receipt was obtained. No changed ESD file, no new postulate, no allow-unsolved-metas, no termination/positivity bypass.

**Remaining wall:** kernel certify the current new modules, then prove the one real sampled-versus-index Q(i) equality and canonical-pair permutation/sum law. Finite mathematical correctness, source-written terms, executed Python checks, certified Agda theorems, scientific source provenance, and calibrated physical observations remain separate verification grades.


## 5g. 29 October 2026 — source-owned generic permutation closes all but the concrete 365 address lemma

New reuse discovery: `DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact` already owns `uniqueMembershipEquivalenceToPermutation` for arbitrary finite lists. Its own lineage credits the original physical NS list-permutation closure, including `NSTriadKNPhysicalOutputFiberPermutationRound35Exact`. Reusing that owner, rather than duplicating permutation theory, is the Pareto/max-cut route.

New source-written adapter `R2P227729Orbit365PermutationReductionExact.agda` defines `expandedCanonicalPairs` by expanding each of the 365 canonical ordered pairs into itself and its simultaneous-negative mate, except the unique fixed zero/zero pair. It contains:
- The 729-entry length computation and generic list-map/concat fusion.
- Pointwise `emitPairEqualsMapExpanded` from the **already inherited** reflected-event conjugation theorem; therefore the actual 365-product event stream equals the source-event mapping of the expanded 729 addresses.
- Exact Q(omega) additive commutativity, associativity and zero identity, plus proof-relevant fold invariance under the original standard list-permutation relation.
- The fully quantified **conditional** theorem `fullPairSumEqualsOrbitSumGivenPermutation`: if `pair729 ↭ expandedCanonicalPairs`, the original 729-product Hermitian output equals the 365-product/reused-conjugates output at **every** integer-frequency target for **every** pair of admissible Hermitian coefficient fields.
- `specific365PermutationFromUniqueMembership`, which delegates the permutation to the source-owned generic theorem and makes its four premises explicit (original uniqueness, expanded uniqueness, both membership directions). These premises have **not** been promoted to unconditional Agda theorems.

This splits the remaining finite work into narrow concrete proof obligations:
```text
(1) Unique.Unique pair729
(2) Unique.Unique expandedCanonicalPairs
(3) ∀ p, p ∈ pair729 → p ∈ expandedCanonicalPairs
(4) ∀ p, p ∈ expandedCanonicalPairs → p ∈ pair729
----------------------------------------------------------------------
     pair729 ↭ expandedCanonicalPairs       [SOURCE GENERIC REUSE]
     original Hermitian 729-fold ≡ orbit-365-fold  [NEW CONDITIONAL]
```
The independent exact Python enumeration confirms (1)–(4) as finite computational facts and shows the actual 729-address multisets agree; that is **not** an Agda kernel proof of those four propositions. Type-check the new module before treating its source-written conditional proofs as established. All three TOE roots now project its explicit conditional theorem, without falsely recording the missing input permutation as discharged.

**The strongest next max-cut**, after kernel readback, is to use the already available dense 0..728 pair rank and generic finite list unique/membership lemmas to prove (1)–(4), then close the conditional proposition without introducing any postulate, meta escape or alternate 729 ontology. Independently, close `retainedSampledBilinear = fourGridGaussianIndexConvolutionAt` by distributivity and C4 tensor character orthogonality. Neither conclusion implies the original continuum NS analytic theorem, R2P2 calibration or any Monster/Ibrahim same-object representation.


## 5h. 29 October 2026 — unconditional source-written orbit proofs, Q(zeta5) full 125-sample implementation

**Current live PR inspiration:** #1433 normalizes the actual Agda NS A/B/C/D and BM2/R829 frontiers without claiming any new PDE result; #1428 records R440 noncore/core diagnostics and explicitly leaves B4, B1–B3 and periodic physical continuation open. These PRs are distinct donor/authority lanes. The Fourier branch does **not** silently import their unmerged changes, claim to pay R440/R736, or promote a finite Galerkin identity to a Clay conclusion. Retain all original NS proof owners, external collaborators and Ibrahim Monster 3B author attribution.

### 5h.1 Three-dimensional 365/729 orbit permutation at the original dense ranks

The original `R2P227729FourierObserverIncidenceExact` already has an ordered 27-mode enumeration and the exact dense address rank `orderedPairRank : ModePair729 -> Nat`. The original `NSTriadKNLiteralCriticalProductionRadialOrderExact` uses a source-written **constructive insertion sort plus proof-relevant permutation**. New `R2P227729Orbit365RankSortPermutationExact.agda` reuses that strategy, generalized to an arbitrary carrier and rank function.

- `sortByRankPermutation` proves, constructively and without uniqueness assumptions, that sorting is a permutation of the original list.
- `rankSorted365ExpandedIsOriginal729 = refl` is an intentional **closed 729-element normalization certificate** comparing the actual expanded 365 canonical pairs against original `pair729` in rank order. It is not merely a cardinality comparison.
- `actualOriginal729PermutesToExpanded365` composes the two permutation facts, supplying the formerly missing hypothesis to the preexisting `fullPairSumEqualsOrbitSumGivenPermutation`.
- `orbit365FullHermitianConvolutionEquals729` now has no address-permutation hypothesis in its *source-written type*. It identifies the original and orbit-weighted 125-output finite Q(omega) Hermitian convolution for any two admissible input fields.
- **Critical status**: this is newly authored Agda source, *not yet kernel-checked*. If rank-sort normalization proves too expensive in the pinned Agda kernel, replace the direct `refl` computation with rank-index uniqueness/membership proofs while keeping the inherited permutation and fold identities. Do not call source text a verified theorem.

The independent exact Python comparison confirmed the sorted 729 addresses exactly match original pair order; this only independently validates the finite combinatorics.

### 5h.2 Reusing the generic sorter for the five-in-nine plane (41/81)

New `R2P281PlaneOrbit41RankSortConvolutionExact.agda` reuses the *same generic* `sortByRank`/permutation proof, not a copied two-dimensional sorting system. `planeOrderedPairRank` is the original 9x9 dense lexicographic pair rank; its expanded 41-orbit list sorts back to the original 81 addresses, by a source-written closed `refl` normal form.

It then builds the source-weighted plane events, reuses the generic Q(omega) permutation-invariant fold from `R2P227729Orbit365PermutationReductionExact`, and matches the **original** `R2P281PlaneHermitianFiveOrbitConvolutionExact.truePlaneBilinearAt` (including the zero-contribution branches). The new `sourceFiveInNineTrueConvolutionEqualsOrbit41` is an unconditional source-written proof type for arbitrary two Hermitian plane fields and all 25 actual integer output frequencies. Agda kernel validation remains pending. No 5-class D4 irrep, Monster group action or physical 2D NS claim.

### 5h.3 Source-written C4 one-axis sampled multiplication

New `R2P2C4GaussianSampledFourierBidiExact.oneAxisSampledConvolutionIsCyclic` states that four times the unnormalized forward DFT of the pointwise product of two individually normalized inverse DFTs equals the correct four-residue cyclic convolution of arbitrary Gaussian-rational coefficient fields. It is written using the original Q(i) operations and the ring solver, not a postulate. Independent exact-rational Python checks passed 64 separately populated coefficient-field pairs, all four output frequencies. Agda typechecking of the ring-solver proof is pending.

### 5h.4 Q(zeta_5) is the correct FULL five-grid scalar; C5 sampled construction added

The existing `R2P227729FiniteQuadraticConvolutionExact` owns the actual C5 group operation and the 125 integer-frequency output labels. Search of existing repository default-branch code found no suitable already-owned `Q(zeta5)` full sampled Fourier scalar/DFT; unrelated zeta/Monster names are NOT substitutes.

New `R2P2C5CyclotomicFullFourierCharacterExact.agda` constructs exact four-coordinate rational cyclotomic scalars modulo `Phi_5=1+z+z²+z³+z⁴`, with 16 exact convolution products combined into coefficients, conjugation, root of order five, 25 source-written C5 character orthogonality cases, and a C5³ tensor product character law over the original `GridCube125`.

New `R2P2C5FullSampledFourierBidiExact.agda` adds five-point forward/inverse transforms on `Quint Cyclotomic5`, source-written arbitrary-coefficient inversion terms, and their full three-dimensional 125-sample tensorized forward/inverse pair plus actual pointwise sampled multiplication. This is a separate coefficient field from the prior C4/Q(i) and C3/Q(omega) Fourier owners.

New `R2P2C5FullSampledIntegerOperatorExact.agda` adds:
- exactly zero-padded 27 input Fourier coefficients in a 125-entry C5³ array;
- signed input-mode roundtrips;
- the physically conventional unscaled synthesis `125 * inverseFourier125`;
- normalized Fourier analysis `(1/125) * fourier125`;
- the actual *full-output* 125-sample pointwise-product operator `fullSampledBilinear125`;
- an instantiation of the original coefficient-polymorphic 729-pair indexed convolution on the **same** Q(zeta5) carrier, with the original `fiveGridBilinearRecoversAllFullCoefficients` theorem.

The **only missing Agda sampled-to-index finite equation** at this level is:
```text
∀ f g : ModeCube27 -> Cyclotomic5, k : WideCube125:
  fullSampledBilinear125 f g k
    ≡ indexedFiveGridBilinearAt f g k
```
This equation is **not asserted** in Agda until proved. For C4, the analogous sampled-to-index equality is also still missing, despite the completed 1D source statement and exact sampled code.

**Independent exact Python checks actually executed in this session:** Q(zeta5) root powers `zeta^5=1`; all 25 scalar character inner products; 8 arbitrary 5-mode transform/inverse pairs; full 125-sample Q(zeta5) inverse and forward tensor roundtrip; two independent densely populated 27-coefficient Q(zeta5) field pairs passed exact sampled-vs-integer convolution at **all 125 full outputs**. The first three profiles are encoded in `scripts/r2p2_c5_exact_sampled_125_full_bilinear.py` and its pytest wrapper, which were committed but not executed on an exact GitHub checkout. The earlier 91,125 **universal fifth-root bilinear coefficient** checks remain an independent mathematical basis audit.

### 5h.5 Updated proof status, max-cut and attribution gate

| Producer / obligation | Current evidence | Remains open |
| --- | --- | --- |
| 365/729 and 41/81 address + Hermitian convolution | Source-written unconditional Agda proof types, actual ranked sorts; independent exact arithmetic | Agda kernel exact-head typecheck / potentially optimize normalization |
| C4/Q(i) actual sampled 64-grid | Source-written 1D product theorem, 3D FFT forward/inverse, 27-padding, indexed Gaussian exact integer theorem; independent all-basis arithmetic | 3D sampled-to-index kernel equality |
| C5/Q(zeta5) actual full sampled 125-grid | Source-written fifth-root/DFT/pad/pointwise/indexed theorem; independent full sampled 125-output checks + 91,125 basis coefficients | 3D sampled-to-index kernel equality |
| Physical NS finite Galerkin | Original Complex3/Leray/triad authority remains golden | Same-object vector-Leray projection, physical energy, original R440/R736 and real-ODE analytic leaves |
| Continuum NS, optical clocks, Ibrahim/Monster 3B | Original separate research owners | Analytic/empirical/same-object evidence not supplied here |

All new owners are imported with explicit theorem projections by `EverythingTOESymmetryResolved369`, `Unifier` and `Unified/Everything`. No modifications to digital ESD or CI, no `postulate`, no unsolved-meta or termination/positivity escape, and no claim of kernel verification. Continue highest-alpha on the two *sampled-to-index* tensor distribution proofs; avoid numerology-only welds and keep source-produced, independently computed, kernel-checked, and physically calibrated evidence grades separate.


## 5i. 29 October 2026 — direct repository-source audit, Lean donor check, and C5 one-axis sampled bridge

This continuation **read concrete Agda source files on the live PR head and master, and concrete Lean sources on the main branch of `chboishabba/dashi_lean4`**. A PR description alone is not evidence of a theorem, a mathematical same-object relation, a branch-available implementation, or a successful kernel replay. These source checks intentionally preceded further edits.

### Source owners read directly (not inferred from PR bodies)

- `R2P227729FourierObserverIncidenceExact.agda`: `allMode3 = [-1,0,+1]`; `modeRank(-1,0,+1)=(0,1,2)`; `cubeRank(x,y,z)=9*rank(x)+3*rank(y)+rank(z)`; `orderedPairRank(p,q)=27*cubeRank(p)+cubeRank(q)`. The source contains `cube27RanksAreExactlyZeroThrough26` and `orderedPairRanksAreExactlyZeroThrough728`, which are literal source-written `refl` statements, not assumed bijections.
- `R2P227729PairOrbit365CanonicalSymmetryExact.agda`: the **actual** `positivePair` selects `Herm.positiveSide q` when `p=0`, otherwise `Herm.positiveSide p`. The centre is the single fixed pair. This matches the new `canonicalOrderedPairs` filter and the 365 orbit compiler, not a different product action.
- `R2P281PlaneHermitianFiveOrbitConvolutionExact.agda`: `plane9` explicitly enumerates the same [-1,0,+1]^2 lexicographic order; `planePairs81` is the Cartesian 9x9 enumeration. `HermitianThirteenPairFourierCodecExact.planePositiveSide` gives the matching zero/positive-side case split. The new rank 9*planeRank(p)+planeRank(q) is therefore the *source* enumeration rank.
- `R2P227729FiniteQuadraticConvolutionExact.agda`: the original `fiveGroupAdd` is the complete five-residue addition table, while `fiveGridGroupSumMatchesIntegerPair` is the source's integer-frequency pair bridge. `R2P227729BilinearCyclotomicPadCutExact.agda` already contains `fourGridBilinearRecoversAllRetainedCoefficients` and `fiveGridBilinearRecoversAllFullCoefficients` for arbitrary coefficient operations. Reuse, not reconstruction.
- `NSTriadKNFiniteConvolutionReconstruction.agda`: genuine finite-list permutation/commutative-sum transport, with physical triad ownership still separate. `Mathematics.NumberTheory.FiniteWeightedReindexExact.agda`: the generic duplicate-free membership→permutation and finite-fold bridge already exists. The current rank-sort path is not another unrelated quotient construction.
- `NSTriadKNLuoFiniteFourierInversionFromResolutionExact.agda` and `NSTriadKNLuoFiniteFourierParsevalFromInversionExact.agda`: existing finite character-resolution, sum swap and rational Parseval arguments credited to **Loukas Grafakos**, *Classical Fourier Analysis*, DOI 10.1007/978-1-4939-1194-3. They are a proof-method donor. Their current carriers are **rational ℚ**, not `Q(i)` or `Q(zeta5)`, so they cannot be imported as a ready same-type proof of the C4/C5 complex-valued sampled product without a scalar-algebra transport.

**Concrete Lean main-source audit:** `dashi_lean4/ExternalClayNS/AgdaContract.lean` explicitly transports time-first Agda histories into the actual Lean `ClaySpec` spacetime functions; it is semantic interop, **not** a native 27/729 finite FFT implementation. `dashi_lean4/NSUnforcedAnalyticCuts.lean` directly states the periodic-B R440 full-output-fibre signed-centering defect can grow under *zero-amplitude cutoff padding*, even for a smooth unforced shear solution. Its available finite Young/covariance envelope cannot be promoted to the cutoff-uniform B4 payment. The retained physically meaningful route is the original source's unpadded amplitude and separate B estimates. Latest Agda #1433 and #1428 PRs retain these independent NS A/B/C/D/R440/R736 boundaries; nothing in this finite C4/C5 construction overrides them.

**Web prior-art check:** [OpenAI NavierStokesAndEuler](https://github.com/openai/NavierStokesAndEuler) attributes its formalized finite-time forced NS breakdown and unforced Euler results to OpenAI; the [FormalConjectures NS file](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Millennium/NavierStokes.lean) still distinguishes open unforced A/B from forced C/D, and the actual published external Lean proof is a separately owned result. No external result is represented here as a native Agda FFT theorem. Fourier/Patterson–Orszag/Grafakos classical results and the newer Lambert–Reneuve–Augier numerical analysis retain their independent authorship.

### Direct max-cut code extension

Existing owner **`R2P2C5FullSampledFourierBidiExact.agda`** was extended in place: `cyclicConvolutionAt` uses **the original** `Full.fiveGroupAdd` and **the original** `R2P2C4C5NyquistAntipodalFixedPointExact.fiveGroupAntipode`, not another hand-copied 25-entry group law. `sampledConvolution5` uses the already authored inverse and forward transforms with the **required factor 5** to compensate for two normalized inverse transforms. New `oneAxisSampledConvolutionIsCyclic` is a source-written exact rational-cyclotomic ring equation for two independent five-point coefficient arrays.

This is the C5 analogue of the already source-written C4 one-axis sampled-convolution law. Both are connected to `EverythingTOESymmetryResolved369`, `Unifier` and `Unified/Everything`; both remain **source-written, unverified by Agda kernel**. Neither closes the 3D 27-mode sampled-index theorem without tensor distribution and the original ordered-pair reindexing.

**Independently executed here:** a local exact-`Fraction` Q(zeta5) implementation checked the entire 25-pair monomial basis (all five outputs per pair, therefore all 125 symbolic bilinear basis coefficients), plus 12 distinct densely populated Q(zeta5) input-array pairs, against the source group-cyclic index formula. The existing `scripts/r2p2_c5_exact_sampled_125_full_bilinear.py` was **extended**, not forked, with `check_one_axis_sampled_convolution` and its 25-basis/12-field assertions, under the existing pytest wrapper. Its committed code has not been executed from an exact checked-out GitHub blob. Independent full C5 91,125 universal basis coefficients and full 125-sample profile comparisons remain the previous computational receipts.

### Exact address verification strengthened against the actual source ranks

`scripts/r2p2_27x27_orbit365_weighted_convolution.py` was extended with **the original dense ranking formulas**. It now asserts the rank-sorted actual 365→729 address expansion is **literally the original 729-address Cartesian list**, and the 41→81 expansion is **literally the original 81-address Cartesian list**, with rank lists `0..728` and `0..80`. These exact checks were independently executed locally for both dimensions (729/365 and 81/41 passed). Prior bag-`Counter` equality alone would not specifically verify the new Agda rank-normalization proof.

### Verified status/next Pareto cut

- **Actually checked:** original source definitions, actual Lean semantic and R440 physical warnings, independent exact local arithmetic, GitHub committed readback, three TOE projections. No ESD/CI edits.
- **Source-written only:** C4 and C5 one-axis sampled multiplication equations, 3D and 2D rank-sorted full Hermitian convolution theorems, C4/C5 tensor inverses and sampled products. **No local Agda/Lean executable or native repository checkout** is available; neither kernel was run here. Avoid `machineChecked` claims.
- **Highest-alpha remaining:** exploit the now identical 1D C4/C5 sampled/cyclic identities by transporting finite pointwise multiplication through the 3-axis tensor products to prove actual `Sampled64=Indexed4` on all 27 retained outputs and `Sampled125=Indexed5` on all 125 outputs. The original source coefficients and signed integer labels are already defined. Then attach a separately checked same-object scalar-to-Complex3/Leray finite NS bridge. Neither source-written `refl` nor a synthetic numerical receipt substitutes for kernel verification, analytically uniform B4, real evolution, or actual clock measurements.

**Attribution/non-promotion:** `IbrahimSnowballParetoFrontierExact`, `SnowballAttributionProvenanceInvariantExact` and the original Ibrahim/Monster 3B mathematical and repository owners remain independent; an exact Q(zeta5) scalar or 729 Fourier pair labels is not the existing Monster representation. Separate source authorship, original repository proof ownership, independent arithmetic executions, and kernel certification. No ESD edits.

### 5i addendum — C4 cross-check and explicit rational scale repair

To keep C4 and C5 equally audited, `scripts/r2p2_c4_3d_exact_sampled_quadratic_dft.py` now also checks all 16 four-point monomial basis pairs (all four outputs) and 12 arbitrary dense Q(i) coefficient-field pairs against the original cyclic four-group indexing. The independent local exact-`Fraction` computation passed all cases. This checks the same arbitrary-input 1D identity as the earlier source-written `oneAxisSampledConvolutionIsCyclic`, but does not certify its Agda term.

Static source review also found a portability/implicit-instance hazard in the new operator modules: the unscaled Fourier normalization constants had been written as polymorphic bare numerals `64` and `125` of type `ℚ`. These were changed **in place** to the standard library's explicit rational constructors `normalize 64 1` and `normalize 125 1`. The complementary inverse scales remain `normalize 1 64` and `normalize 1 125`. This is a syntactic/type-directed hardening, not a claim of a verified algebraic theorem. The Agda standard-library `Data.Rational.Base.normalize` signature was checked against its actual source; it accepts nonzero-denominator natural arguments.

The direct Agda and Lean source-inspection evidence, exact local Python checks, and new source commits are separate grades. No exact-branch Agda/Lean kernel, pinned checkout regression execution, or CI was run.


## 5j. 30 October 2026 — direct current-head Agda/Lean audit and source-identical 729-product Fubini bridge

### Verified donor discovery before writing code

**Agda branch source read directly:** `FourierObserverIncidenceExact` owns `cube27`, `pair729`, 0..26/0..728 dense ranks; `FiniteQuadraticConvolutionExact` owns the original `fiveGroupAdd`; `FourGridRetainedQuadraticParetoExact` owns original `fourGroupAdd`; `BilinearCyclotomicPadCutExact` owns arbitrary-coefficient indexed 729-term exact convolution; `Orbit365PermutationReductionExact`, `Orbit365RankSortPermutationExact`, and `PlaneOrbit41RankSortConvolutionExact` own the earlier antipodal source candidate. Reused all, did not invent a second input-pair ABI.

**Most important negative source finding:** `Biology/Physical/C3CubeCyclotomicFourierExact.agda` has `spectralConvolutionDiagonalises`, but its `FourierAuthorityBoundary` *explicitly records* `spectralConvolutionAlreadyProvesGroupSumFormulaIsFalse`. That theorem is based on `cubeFourierForwardInverse`, **not** the missing spatial pointwise-product-to-group-convolution formula. It cannot be invoked as the missing C4/C5 729-term bridge. The existing `NSTriadKNLuoFiniteFourierParsevalFromInversionExact` and `YangMills/BalabanFiniteSumFubiniExact` already prove rational-valued Fubini/sum-swap/distribution. These are **method donors** only: their target `ℚ` is not automatically `Q(i)` or `Q(ζ5)`.

**Actual Lean main-source read:** `dashi_lean4/ExternalClayNS/AgdaContract.lean` transports space/time histories; `NSUnforcedAnalyticCuts.lean` contains the signed R440 physical zero-padding adversary. No unproved finite C4/C5 Fourier scalar equivalence was imported from Lean. **Latest PRs checked:** #1438 trialectic weighted directed graph with exact non-geometric opposition and no C3 invariance; #1437 separate combinatorial Max Cut/Pareto scheduling with explicit no-physics-promotion; #1433 actual A/B/C/D and BM2/R829; #1428 periodic-B R440 frontier. Their specific **Agda code** was read, not only their PR bodies. Their source ownership remains independent of the 27×729 sampled Fourier proof.

### Exact coefficient algebra now source-written, without a parallel ontology

Extended **existing** `R2P2C4GaussianFourierCharacterExact.agda` and `R2P2C5CyclotomicFullFourierCharacterExact.agda` with 12 exact scalar laws each: addition associativity, commutativity, zero identities, multiplication associativity, commutativity, one/zero identities and both distributivity directions. They are source-written rational ring-solver proof terms, not kernel receipts. They are the missing concrete field laws needed to use finite Fubini with Q(i) and Q(ζ5).

Extended original **`R2P227729BilinearCyclotomicPadCutExact.agda`** with a **single** coefficient-polymorphic `FiniteSumAlgebra` law record and finite fold lemmas `sumAllCong`, `sumAllZero`, `sumShuffle4`, `sumAllAdd`, `sumAllSwap`, `sumAllScaleLeft/Right`, `sumAllAppend`, `sumAllMap`, `sumAllConcatMap`, `sumAllPair729AsDouble`, and `sumAllDoubleProduct`. The chief theorem is **`source729ProductExpansion`**:

```text
∀ f,g : original ModeCube27 -> A,
     (Σ[p∈original cube27] f[p]) * (Σ[q∈original cube27] g[q])
   = Σ[(p,q)∈original pair729] (f[p] * g[q])
```

It is a proof over exactly the existing **729 original ordered addresses** and an arbitrary `CoefficientOps A` equipped with explicitly supplied finite-sum algebra laws, not merely `27 × 27 = 729` counts. This reuses the source rational finite-sum Fubini proof pattern over the correct scalar carriers, and introduces no unproved scalar coercion. Instantiated as `gaussianActual729InputProductExpansion` in the existing C4 operator and `cyclotomicFiveActual729InputProductExpansion` in the existing C5 operator. Both are now named and projected into all three golden TOE roots.

Added explicit finite **character-addition** in the **same existing C4/C5 character files**: `scalarIndexDistributivity` (64/125 original-index cases by the actual original group addition) and `characterAdditionLaw` (character of sum equals product). This is the exact group-representation law needed to turn each spatial Fourier product's 729 expanded terms into a frequency-indexed sum. It is **not** an identification with any Monster 3B representation.

### Independent executed evidence versus claimed Agda authority

A source-derived JavaScript checker parsed the actual C4/C5 Agda `scalarProduct4/5` and `fourGroupAdd/fiveGroupAdd` tables, including the source's generalized zero-identity cases, and evaluated **64/64 C4** and **125/125 C5** scalar-index distributivity clauses: **zero mismatches**. This tests the exact definitions entering `characterAdditionLaw`, not a separately invented group table.

A separate local exact Python `Fraction` arithmetic test checked **all 8 Q(i) and 64 Q(ζ5) basis triples** for multiplication associativity and both distributivity directions; it then checked **five independent arbitrary dense 27-mode field pairs for each scalar** against the full **729** original ordered-product expansion. All passed. The two preexisting C4/C5 Python scripts were extended with basis-triple / 729-sum regression checks **in place**, not forked. This is independently executed arithmetic, **not** a committed-checkout regression run, nor the Agda kernel checking these terms.

**Verification state:** The new Agda ring law proofs, generic finite-sum lemmas, 729-product expansion and C4/C5 character-addition terms are *source-written only*. An exact-head kernel check is necessary before calling them proved in Agda. No postulates, holes, termination/positivity/unsolved-meta bypasses were intentionally added; scan/readback must still not be confused with compiler verification.

### Highest-alpha remaining cut (precise equation)

The product-distribution step to literal `pair729` is now sourced. The remaining proof obligation is to transport the **actual Q(i)/Q(ζ5) tensor Fourier sample operators** into these algebraic sums, collapse the `64/125` normalized spatial character sums by the exact character orthogonality laws, and use the **original** output membership/aliasing maps, obtaining the two equations without any unverified intermediate postulate:

```text
∀ f,g : ModeCube27 -> Gaussian4, k : ModeCube27,
  retainedSampledBilinear f g k
   ≡ fourGridGaussianIndexConvolutionAt f g k

∀ f,g : ModeCube27 -> Cyclotomic5, k : WideCube125,
  fullSampledBilinear125 f g k
   ≡ indexedFiveGridBilinearAt f g k
```

Then a separately verified native `ExactNSFourierInteractionStructure` / Complex3 / Leray transport is required, keeping original R440/R736/B4 analytic cut and physical real ODE separate. **OpenAI NavierStokesAndEuler 2026** formally proves the *forced* C/D breakdown and unforced Euler blowup, not this branch's unforced periodic-B estimate; original authors and Lean source priority are preserved ([original released code](https://github.com/openai/NavierStokesAndEuler), [released formalization manifest](https://github.com/openai/NavierStokesAndEuler/blob/main/formalization.yaml)). Weinan Wang's 2026 Lean result on 2D Galerkin constructions ([arXiv:2609.33033](https://arxiv.org/abs/2609.33033)) is independent prior art, not this exact 3D C4/C5 scalar transport.

**Ibrahim/source-custody rule:** `IbrahimSnowballParetoFrontierExact`, prior source-produced first-link provenance, original Monster 3B authors, other repository proofs and kernel-verified certificates retain separate ownership and authority. No 27/729 spectral coincidence, matched character table, synthetic clock receipt, or generalized Pareto/Max Cut lane promotes same-object Monster, calibrated R2P2, or unforced NS closure. ESD untouched, CI untouched.
