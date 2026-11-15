# Crystallography × 369 Hyperfabric: consolidated max-cut roadmap
Date: 2026-10-26
Owner: PR #1261, consuming pre-existing repository artefacts and PR donor branches.

## Original question and the genuine mathematical expansion
The initiating visual demonstrated tetragonal 4/mmm (D4h), of order 16:
r^4=s^2=h^2=1, srs=r^-1, and h central. The ensuing work
identified an exact signed-coordinate Weyl embedding,
D4h ≅ W(B2)×W(A1) ↪ W(B3) ↪ W(B4),
and a need for shared crystallographic definitions. This is
classical crystallography, not an original experimental claim.

Adjacent, *distinct* pre-existing lanes include:
- T4/T9/T18 trialectic local descent and C3 cyclic transport;
- a 9-site D4 grid with centre/edge/corner orbit data;
- a native balanced 3³ path-graph cube and signed antipode;
- the punctured-nine plane and colour-wheel/pants adapters;
- 369 atomic index, electronic shells, fermionic antisymmetry,
  molecular/industrial hyperfibre and physical-validation receipts;
- Z³ Fourier mode lattice, 4D Balaban finite periodic blocking,
  B4 Weyl action and hyperfabric restrictions;
- diamond NV four-axis/spin/MCG/ODMR/optical/TSFV models and
  magnetic Seitz/Bloch donors from distinct PRs.

## What the finite core actually says

X=T³ has 27 *spatial sites*, not the cyclic additive group C27.
In the native nonperiodic path-graph lattice, remove only 0.
There are 26 nonzero sites and 13 antipodal pairs.
The projective strata by nonzero coordinate count are
3 coordinate axes, 6 face diagonals, 4 body diagonals.
B3 signed permutations preserve strata and act faithfully on
all 13 unoriented axes, while its 4-body-diagonal action has
kernel ±I and quotient S4.

Slice X* by z: 9 lower, 8 central, 9 upper = 26.
Only the central plane is punctured. Antipodal gluing pairs
outer sheet points across the two outer sheets, and the
central slice within itself. Replacing this with three
punctured nines would yield 24 and erase essential residuals.

The base-three string 111 has ordinary value 13. If ordinary
digits 111 index a centred ternary cube via digit -> digit-1,
the addressed cube site is (0,0,0). As a balanced signed
coordinate string +++, its weighted amplitude is 13 and its
spatial site is the [111] corner. The 13 projective axes
are a third object. Keep codec/observer tags.

The nonperiodic path cube, periodic additive C3³ torus,
modular nine-sheet map, exceptional Jordan 27-space and
physical diamond lattice are different objects despite
shared finite cardinalities. In particular PR #1239
documents a modular bijection that is not a graph
automorphism of the native nearest-neighbour cube.

## Phase and deliverable gates

### P0. Provenance and executable receipts (partially complete)
Deliverables: source-root ledger, code owner inventory, exact PR
donor imports vs copied adapters, local check records.
Completed: multiple source-scoped audits; no physical
specimen identification was attempted.
Gate: explicit Agda typecheck and mathematical regression
checks for current #1261 branch. CI is not required.

### P1. Finite crystallographic group actions (implemented, kernel open)
Deliverables: D4h normal form; exact 3x3 matrices; eight-site
actions; D4 nine-cell transport; signed B4 inclusion and
four cubic NV axes. Completed: source-level implementation
and finite Python diagnostic receipts.
Open: Agda kernel receipts, abstraction of large exhaustive
case splits, exact B4 donor-to-D4h representation morphism.

### P2. Twenty-seven puncture and thirteen projective axes
Deliverables: native X* cube ↔ 8+9+9 sheet chart;
origin exclusion; antipodal 13 quotient; strata 3+6+4;
B3 equivariance with ±I projective kernel and faithful oriented action; diamond four-axis
restriction and kernel ±I.
Now: chart forward map, partial inverse and chart
round-trip submitted, reusing PuncturedNineSheet; PR #1249
owns native antipodal involution and adjacency proof.
Open: import PR #1249 when available, typed dependent
nonorigin inverse, quotient normal forms, Agda faithfulness.

### P3. Hyperfabric pants seam and XOR residual
Deliverables: real z-sheet incidence/restriction maps;
GlobalSection and InterfaceMatch with phase/capacity
proofs; binary orientation residual, XOR 1-cochain,
cycle holonomy obstruction theorem and gluing BIDI.
Prior art: TypedHyperfabricCore,
TypedHyperfabricPantsGluingBridgeExact,
JInvariantColourWheelNineSheetPantsGluingExact and
NSTriadSignedXORGaugeabilityBoundary.
Open: same-object instantiation and proof of seam
compatibility, not just descriptive analogy.

### P4. Crystallographic lattice and 3D classifications
Deliverables: 7 systems / 14 Bravais / 32 point-group
catalogue; actual lattice basis/metric, 32 matrix
representations and lattice preservation; Seitz affine
multiplication; 230 space-group type data crosscheck.
Current: metadata catalogues and D4h signed-coordinate
definitions; existing B4 and Fourier lattice donors.
Open: matrix, metric and Seitz proofs, authoritative
versioned IUCr/spglib comparison. Numerical catalogue is
not a 230-classification proof.

### P5. Species-decorated crystals, diamond and Bloch
Deliverables: native atomic 369 AtomicIndex decorations
and species/occupancy-preserving action, diamond fcc
two-sublattice basis and Fd-3m (#227), NV ordered-defect
site stabilisers, separate quantum spin-one action,
Bloch Hamiltonian covariance and spectroscopy bridges.
Current: typed atomic metadata and preservation contract,
NV four-axis adapter; donor PRs #1238/#1262, CoTaSe2
magnetic Seitz/Bloch PRs #1076/#1115.
Open: concrete Seitz operations, physical site orbits,
faithful magnetic/quantum representations and calibrated
experiment receipts.

### P6. Experiments and independent discrimination
Deliverables: operational tests distinguishing actual
crystal symmetry, antiferromagnetic/magnetic groups,
defect-orientation fractions, band degeneracies, NV
zero-field/Zeeman response and scattering selection rules.
No structural cardinality or ternary codec is an empirical
observation or quantum advantage theorem.

## Steelman and falsifiers

Strongest steelman: the same *functorial finite action/gluing
machinery* may organise ternary finite hyperfabric data,
crystallographic projections and symmetry-resolved atom/quantum
observables while preserving residuals. This is useful even
if it discovers no novel force, element rule or sensor effect.

Distinguish this from stronger speculative claims:
- Signed ternary structural similarity does NOT entail
  a physical diamond lattice or C3 Hamiltonian symmetry.
- A spatial C3 stabiliser of the [111] defect axis is
  distinct from cyclic permutation of m_s={+1,0,-1};
  PR #1262 already gives an Sz² obstruction.
- XOR orientation gluing is Z2 and cannot silently be
  identified with ternary C3 addition.
- Same cardinality of 27 geometry, Jordan or modular
  algebra does not supply an isomorphism preserving their
  respective products or adjacency.

Falsification / proof-search criteria:
(i) explicit failure of equivariance on a site/action pair;
(ii) nonmatching reflection fixed-point counts for
alternative eight-site D4 carriers;
(iii) failure of source hyperfabric InterfaceMatch;
(iv) nonzero XOR holonomy along a cycle;
(v) absence of a lattice-preserving integral Seitz action;
(vi) spectra/selection rules diverging from measured
physical data under stated instrument conventions.
Negative findings remain durable structural results.

## Attribution
Established Weyl/Coxeter groups, IUCr classes, Bloch/Seitz,
quantum spin and crystallography remain external prior art.
Existing DASHI native module/PR authors retain dated code
and claim provenance. The contributions in #1261 are new
typed adapters, separation theorems/obligations, explicit
finite proof terms and independent computational audits.
Source existence, attributed statements, model definitions,
local checks, kernel proofs and external-world physical
identification are separate promotion stages. Do not
infer material proof merely from imported theorem names.

## Updated Pareto cut (2026-10-26, web and latest PR refresh)

The earlier list in this roadmap has been superseded by substantial
new PR #1261 construction and native donor PR #1249. Do not
rebuild the 13-axis orientation quotient: #1249 owns its actual
same-carrier 26 ↔ 13×Bool chart, antipodal graph and holonomy.

### P1: Concrete primitive tetragonal (4/mmm; P4/mmm No.123)
- 16 D4h normal forms, integer direct/reciprocal Z³ Fourier modes,
  weighted tetragonal pairing, Seitz integer translations and
  atomic 369 species-labelled consumer are source-implemented.
- Independent exact group/metric/Seitz finite diagnostics passed.
- Source-level Agda proofs need genuine compiler elaboration.
  CI is not a gate; kernel proof status is one.

### P2: Diamond-cubic Fd-3m (No.227)
- New #1261 native modules construct FCC primitive lattice,
  its two displaced diamond sublattices, nontrivial glide square,
  native 369 species-labelled nitrogen-vacancy bond and local C3v.
- Independent exact computations validate 48 signed cubic matrices,
  all 192 affine representatives, their 36,864 products, eight
  occupied conventional-cell sites, 24-versus-6 stabilisers.
- New fcc/bcc forward integer winding proof, plus an exact
  64-residue **bidirectional** fcc reciprocal/parity criterion;
  the unrestricted Z-integer converse is not yet an Agda theorem.
- New Gaussian-integer eight-atom structure-factor model:
  exact factorisation and 64 intensity proof cases: 52 zero,
  8 relative intensity 32, 4 intensity 64. All are reciprocal
  index residue classes, not measured peak intensities.
- Explicit distinction: 222 is permitted by F centring but
  cancels for the ideal equal-atom diamond motif; uniform A/B
  scattering contrast restores its intensity and breaks the
  sublattice-exchanging glide. An isolated NV centre cannot be
  modelled by uniform removal of the B sublattice.
- Next: full Agda 48/192 group-operation quotient and Wyckoff
  multiplicity, independent IUCr table settings/origin crosswalk,
  reciprocal lattice units and actual nuclear/spin Hamiltonians.

### P3: Physical NV and multicore spectroscopy
- Agda PR #1262 establishes non-invariance of cyclic spin-one
  Sz² label permutation: spatial [111] C3v is not a basis-level
  spin/qutrit C3 identity.
- PR #1269 now owns SI-dimensional calibration, same-device
  electron/nuclear register bridges, readout and finite photon
  inference. Reuse; do not duplicate or invent calibration.
- PR #1270 and primary original paper arXiv:2609.13022v2
  (Gemsheim et al., revised 2026-09-18) provide the separate
  paper-specific nuclear-spin register and ambient Grover
  experimental evidence. Manufacturer core-count claims are not
  evidence of one coherent full-width quantum register.
- Next same-object obligation: explicit defect-site → calibrated
  spin/orbital Hamiltonian → pulse/channel → optical response →
  SI quantities → photon statistics; include source-native
  actual device IDs, parameter uncertainties and negative tests.
- Diffraction source here is a geometric observable; it does
  not measure room-temperature qubit gate fidelity.

### P4: General crystalline classification and experiments
- Catalogue labels for seven systems / 14 Bravais / 32 point
  groups exist; actual 230 space-group operation tables,
  settings, origin choices and Wyckoff actions are not proved.
- Discriminators: correct diffraction absences, reciprocal
  phase, site/bond little-group, magnetic/strain splitting,
  ODMR frequencies, photons and SI-calibrated errors.
- T4/T9/T18, signed-zero, punctured-nine/punctured-27,
  hyperfabric pants and XOR remain optional finite
  cross-validation carriers, NOT the research centre.

### Provenance and acceptance
- Classical external roots: IUCr International Tables Vol A,
  Fd-3m (227) and P4/mmm (123), IUCr Online Dictionary
  *Reflection conditions* (general versus special/Wyckoff),
  standard diamond two-site structure factors.
  https://onlinelibrary.wiley.com/iucr/itc/A1b/ch2o3v0001/sgtable2o3o227/
  https://dictionary.iucr.org/Reflection_conditions
- Recent experimental authority: Gemsheim et al.,
  *Grover Search with Semiconductor Spin Qubits at Ambient
  Conditions*, arXiv:2609.13022v2.
  https://arxiv.org/abs/2609.13022
- Actual added work: native bridge/source Agda, Python exact
  regression and roadmap. Never credit these formalisation
  products to original experimental authors.
- Verified finite Python arithmetic, source-written Agda,
  Agda-kernel proof and measured external-world evidence
  are distinct statuses. No CI dependency is imposed.



## 2026-10-26 latest: same FCC lattice → first finite Bloch matrix

The previously open ideal spinless two-sublattice nearest-neighbour
Bloch consumer is now source-implemented in
`DiamondNearestNeighbourBlochExact.agda`,
`DiamondBlochCubicCovarianceExact.agda` and
`DiamondBlochSpectralEvidenceBoundaryExact.agda`.

- Four actual tetrahedral nearest B neighbours of an FCC A
  site, not a replacement site set or 27-space analogy.
- Hermitian 2×2 `H(k)`, Gaussian phase Γ(k), `H²=|Γ|²I`,
  64 finite fourth-root momentum phase samples.
- All 48 signed-cubic maps preserve squared energies and
  have stronger matrix covariance: odd sign parity conjugates Γ,
  represented by exchanging A/B basis entries.
- Nontrivial exact samples: `|Γ|²=0` on 48 of 64 residues;
  `|Γ|²=16` on 16. Toy hopping sample values, NOT the actual
  diamond or NV electronic/spin bandgap.
- Scalar-spectral non-entailment: a mass-squared spectral curve
  can retain cubic symmetry while A/B atomic scattering contrast
  breaks the nonsymmorphic glide. Bare scalar gap² also loses
  complex Bloch phase. Thus a scalar spectrum does not
  certify the actual material's full space-group action.
- PR #1272 Fourier-pixel bidirectional work supplies a distinct
  phase/intensity observer methodology; it is NOT a diamond
  hardware experiment and does not measure this Bloch Γ(k).

Updated Pareto proof sequence:
1. Agda kernel typecheck/fix (CI not required).
2. Full 192-operation Fd-3m Seitz/Bloch phase action, lattice
   origin and Wyckoff settings, true reciprocal units.
3. Source-specified multi-orbital/spin-orbit/strain/Zeeman
   material Hamiltonian, ordered NV-bond C3v representations,
   and preservation of the PR #1262 spin-one label no-go.
4. Same-device SI-calibrated NV control, optical readout,
   electron/nuclear register maps (#1269), original nuclear
   Grover experiment and vendor claims distinguished (#1270).
5. Complete 7/14/32/230 operation catalogues with original
   source authority and operational experimental diagnostics.

Attribution and acceptance apply at every arrow: established
Fu–Kane–Mele/IUCr science, original DASHI owners, new PR #1261
formalisation, uncompiled Agda source, independent exact finite
arithmetic, and experimental observations are NOT one status.
