# Changelog

This changelog is append-only. Older mentions of `false` are historical wave
records unless the entry explicitly states it is describing the current live
monitor surface.

## 2026-07-19 — Wetsuit seam optimisation boundary

- Added `DASHI.Geometry.WetsuitSeamOptimisationBoundary`, a fail-closed typed
  carrier for body-zone design priors, material/panel budgets,
  manufacturability evidence, weighted seam cost, admissibility, relative
  optimality, validation gates, and split advice.
- Added `DASHI.Geometry.WetsuitSeamOptimisationRegression` with canonical
  underarm/inner-leg preference and shoulder/spine avoidance prior receipts,
  while keeping continuum optimality and manufacturing authority explicitly
  unpromoted.
- Added the compact aggregate `DASHI.Geometry.WetsuitSeamOptimisation`.
- The module formalises the optimisation and obligation surface only; it does
  not claim universal biomechanics, continuum-mechanics closure, or certified
  manufacture. `DASHI.Everything` was not run in this connector-backed pass.

## 2026-07-13 — P06 duplicate-free valid-walk enumeration

- Added and focused-checked `P06GeneratedWalkUniqueness.agda`.  Under the
  canonical neighbour adapter it proves extension-block `NoDuplicates`,
  recursive block disjointness, and
  `generatedWalkVertexListsNoDuplicates` without postulates or proof-heavy
  `WalkObject` equality.
- Added `GeneratedWalkVertexListSemantics`, packaging generated valid-walk
  lists, extensional completeness, duplicate-freedom, and the single
  `countWalks ≡ length` bridge.
- Added focused-checked additive `P06ConcreteEnumerationEndpoint.agda` and
  `P06SkeletonEnumerationSurface.agda`.  The former makes DFS membership an
  explicit field of a membership-indexed map; neither module touches the
  legacy total-index API.
- Added focused-checked `P06ConcreteSkeletonWitness.agda`, which proves all
  individual-candidate chooseN facts and packages the remaining skeleton list
  obligations (`complete`, vertex-list uniqueness, and count agreement)
  without pretending they are derivable from an arbitrary list.
- Added focused-checked `P06DFSValidWalkSurface.agda`.  It packages the
  minimal per-skeleton `WalkObject` plus equality to `dfsWalkRange`, derives
  generated-list membership and soundness, and adapts map witnesses to the
  membership-indexed endpoint.  It deliberately does not infer path validity
  from `DFSCover` coverage alone.
- `Everything.agda` was not run.  The remaining P06 mathematical blocker is
  now the genuine DFS-valid-walk membership witness; the legacy total-index
  record remains compatibility-only.

## 2026-07-13 — Corrected P06 walk status

- Corrected the P06 record: recursive walk completeness has landed through
  `walkObjectsCompleteByVertices`, and successor-membership inversion has
  landed through `walkObjectsSucMemberByVertices` and
  `walkObjectExtendMemberByVertices` in
  `DASHI/Physics/YangMills/GraphCombinatorics.agda`.


## 2026-10-30 — PR #1407 source-identical finite Fourier 729-product Fubini (kernel pending)

- Directly audited actual `dashi_agda` C3/C4/C5 Fourier, 27/729 pair/orbit, original coefficient-polymorphic convolution, Yang–Mills Fubini and NS rank/permutation code; directly read `dashi_lean4` NS semantic contract and zero-padding adversary. Checked new PR #1437/#1438 Agda owner files and #1433 NS boundary.
- Added **source-written** C4/Q(i) and C5/Q(ζ5) ring algebra laws plus finite source-group character-addition lemmas; original C3 Fourier source correctly flags that diagonalization is **not** already the group-convolution theorem.
- Added `FiniteSumAlgebra` and generic finite-sum add, scale, swap, append, map, concat-map and 27×27→729 pair-product expansion to **existing** `R2P227729BilinearCyclotomicPadCutExact.agda` instead of duplicating the original indexed operator. Instantiated over both scalar carriers and exposed named theorem candidates in all three TOE roots.
- Independently checked the original Agda C4/C5 scalar-group tables (64 and 125 cases, zero mismatch); local exact `Fraction` verified 8 Gaussian and 64 fifth-cyclotomic ring basis triples and five distinct dense 729-pair inputs per carrier. Extended existing Python diagnostics in place, without claiming an exact-checkout run.
- Updated `.planning/ROADMAP.md`, `TODO.md` and paper §5j. **Agda kernel was not run and CI was neither changed nor run**; source-written proofs are not certified. Remaining C4/C5 3D sampled↔indexed identities, NS physical R440/R736/B4, original external forced C/D attribution, R2P2 calibration and Ibrahim Monster 3B same-object evidence remain strictly separate.


### 2026-10-30 — PR #1407 sampled Fourier phase-sum intermediate proof (kernel pending)
- Extended original coefficient-polymorphic Fubini algebra with `productShuffle4/productShuffleSix` and concrete scalar multiplication-associativity/commutativity laws. Added actual Q(i) C4 and Q(ζ5) C5 character-weighted `Original27UnscaledSynthesisAt`/ `Original729PhaseContribution` and `SourceSampledProductExpands729` in existing operator owners, with typed projections into all three TOE roots.
- Independently executed exact arithmetic checks on full 64/125 sample sets, each involving the original 729 input-pair phases, and extended existing regression scripts. Pinned repository checkout/Agda/Lean kernels and CI not run.
- Remains open: actual padded tensor FFT-to-source character identification, normalized forward orthogonality collapse, sampled/index equality, native physical NS/analytic B4, R2P2 data and separate Ibrahim Monster 3B same-object evidence. No ESD or CI modifications in this tranche.


### 2026-10-30 — PR #1407 exact C4/C5 normalized resolution extraction boundary (kernel pending)
- Reused the ORIGINAL `R2P227729BilinearCyclotomicPadCutExact` with generic `finiteFourierExtractionFromOriginal729GivenResolution`. Its sole premise is the explicitly required normalized character-resolution identity; proof terms use inherited finite sum swap, scale, membership case split, not hidden postulates.
- Extended existing C4/C5 operators with actual normalized character phase, original 64/125 Nyquist sample lists, source selected-pair kernels, and resolution-hypothesis-bearing `SourceSampledEqualsIndexedGivenResolution`. Projected these correctly conditional theorems in TOE, Unifier, Unified.Everything.
- Independently checked full actual source-order finite characters: C4 4096 group comparisons/19683 original pair-targets and C5 15625 group comparisons/91125 original pair-targets, pure exact arithmetic. A preliminary 1D-vs-3D N/N³ diagnostic was fixed before complete passing run. Added source-order checks to existing universal Python certificate. Exact checkout Python suite and Agda/Lean kernels NOT run.
- Remaining independent golden kernel obligations: actual normalized 3D character resolution, sample-array FFT/source character equivalence, final C4/C5 sampled→indexed, physical NS R440/R736/B4/real time, clock calibration, original Ibrahim Monster 3B; no ESD/CI modifications.


### 2026-10-30 — exact spectral primary sources and `--safe` admission boundary
- Verified historical Orszag (1971 J. Atmos. Sci.), Patterson/Orszag (1971 Phys. Fluids) and Orszag (1971 Galerkin spectral) primary-source authorship; kept finite method inheritance, branch-owned Agda proof terms and executed exact checks separate.
- Source-audited original `Core.Prelude`, observer incidence and new C4/C5/bilinear modules: `{-# OPTIONS --safe #-}` is not declared in these files. Static hole/postulate scans do not certify safe mode. Recorded transitive `--safe` import closure and exact-head Agda checking as mandatory before golden certification; no ESD change and no CI run.
- Made C4 four-point source rational normalization explicit with `normalize 4 1`.
