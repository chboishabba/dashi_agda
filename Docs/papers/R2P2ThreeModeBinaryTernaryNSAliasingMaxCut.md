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
