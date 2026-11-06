## 6 November 2026 — priority physical-cube max-cut, stronger than bare-link Dobrushin

**New rigorous quantitative strategy / source implementation:** [YMClayPhysicalCubeDobrushinCMP116Transport20261106.md](../physics/YMClayPhysicalCubeDobrushinCMP116Transport20261106.md). It audits the actual original Dobrushin, CMP116, Wilson/Haar/Gibbs, Perron/Doob, physical RG/UV and OS owners, and retains distinct 2D/3D/4D/5D semantics. The 2D/3D/5D donor does NOT independently prove 4D.

**Source-written:** `DASHI/Physics/YangMills/YMClayPhysicalCubeDobrushinFromGibbsExact.agda` reuses original `BalabanFiniteBoundaryConditionedDobrushinExact` and `BalabanP33RationalQuaternionNormSquaredExact`; explicit `physicalCubeCellLength (cubeSideInCells a) (latticeSpacing a) ≡ physicalCubeSide`, one `0≤q<1` across all UV cutoffs/volumes, same original normalized Gibbs conditional fibre, `originalConditionalRowsUniformlyContract`, `originalConditionalObservableUniformlyContract`. **These are SOURCE/CONDITIONAL, Agda kernel pending**; actual uniform influence estimates remain to be produced. No bare `Set` field for physical cube calibration.

**Reference:** `scripts/check_ym_physical_cube_perron_certificate.py` implements exact rational weighted Perron `Cw≤q w`, positivity, exact fixed-physical-cube calibration, 12+ power checks and negative controls. It **refuses physical proof admission even if metadata is supplied**, because authentic physical source claims cannot be verified by strings. Independently checked the 4×4 illustrative matrix with exact fractions through 101 powers, max weighted row `5/12`, `q=1/2`, 5 refinements; not evidence of any actual Wilson measure.

| Physical-cube ID | Exact missing theorem/source producer | Definition of done |
|---|---|---|
| PCUBE.P01 | Construct selected `B_{a,ell *}μ_{a,L}^{Wilson}` conditional kernels from original continuous Haar/Gibbs and exact R445 same-object maps | Kernel proof and Borel conditional integration with same action/decoder |
| PCUBE.P02 | Fixed `ell` across physical lattice spacings `a→0`, `b(a)a=ell` or certified ceil interval | Original lattice geometry/units, not fixed block in lattice units |
| PCUBE.P03 | Selected all-scale physical reflection-halfspace compatibility for actual blocking | Reflective transfer and OS-positive-time sigma-algebra mapping |
| PCUBE.P04 | Actual cutoff/volume independent weighted influence `C^{a,L}w≤q w`, `0≤q<1` | **Core new nonperturbative estimate**, actual SU(N) conditionals; either direct relative, averaged Dobrushin–Shlosman, or CMP116 rooted-polymer route |
| PCUBE.P05 | Selected direct R467 `literalSelectedCMP116Localization` and envelope `≤ C_F q^{t/ell}` on actual source/continuum family | One original same-J witness and common physical source norm, no unproved field |
| PCUBE.P06 | Same limiting OS H, strong semigroup and dense local modes, gap `m≥-log(q)/ell` | Physical units, no spectral pollution or invisible subgap states |
| PCUBE.P07 | Nontrivial continuum and all prescribed compact simple groups | Actual physical OS/Wightman theory and full Clay interpretation |
| PCUBE.F01–F03 | `physicalCubeCellLength`, `originalConditionalRowsUniformlyContract`, `originalConditionalObservableUniformlyContract` | Source written; require Agda exact-head/typecheck and actual PCUBE.P01/P04 inputs |
| PCUBE.F04 | Weighted Perron checker | Python exact rational algebra and negative controls only, no physical promotion |

**Max-cut order:** prefer original CMP116 rooted-shell estimate if source-native, otherwise selected **weighted** physical-block Dobrushin matrix, rather than bare-link `18 tanh(12 beta)`. If pointwise raw-weight influence fails, the weaker averaged block criterion remains admissible. This does **not** duplicate existing published 4D CMP122 RG theorem. Any strict `q` at fixed physical `ell` gives `m=-log(q)/ell>0` for the same OS Hamiltonian IF all selected physical continuum/OS/spectral premises are actually proved. `q<1` for fixed LATTICE step with changing `a` is not the same theorem.

---


### Phase-1 constructive decision procedure — 6 November

**New original source:** `YMClayNativeOriginalSortDeciderExact.agda` adds `decideNativeMember`, `decideAllSelectable`, `isYes`, `proofFromYes`, `originalC3SelectableBooleanGoal`, `originalC3CanonicalFromBoolean`, `originalPairSelectableBooleanGoal`, and `originalPairCanonicalFromBoolean`. A successful *closed* computed Boolean membership trace now implies the existing exact native C3 or pair canonical-label equality without assuming an entire 1,024-vector equality. The two Boolean equalities and the pair-length equality **still require closed Agda proof terms and kernel acceptance**; `decideAllSelectable` is not a physical or analytic theorem. This source is imported by `DASHI/Unified/BalabanRGTOERegression.agda` and targeted by `.github/workflows/ym-native-maxcut-exact-agda.yml`, which uses the repository's existing Nix Agda shell. New workflow creation is not a green CI receipt. 

# Yang–Mills #1444 — execution phases, concrete deliverables and exact lemma acceptance queue
**Snapshot:** 6 November 2026. **Owner:** independent 4D Yang–Mills PR #1444. **Unification #1460 is NOT a prerequisite.**

## Purpose: stop repeating the six-gate inventory

This file is the **executable completion plan**. The canonical [exact lemma ledger](YMClayCurrentExactLemmaLedger20261103.md) supplies historical IDs, and [ClayYMProofRoadmap](ClayYMProofRoadmap.md) retains full historical context. Do not add another generic Wilson plaquette, Fubini theorem, trivial parametric record, or cosmetic compiler while an existing exact source theorem covers the statement. Each change MUST provide (1) selected original owner, (2) exact goal type or analytic proposition, (3) produced term/bound, (4) kernel or independent receipt, (5) transitive assumptions, and (6) status change if any.

**Immutable facts:** 219 original submission field *names* are all bare `Set` types, not 219 proved statements. The Round78 five-input compiler and its 15 carriers, 34 predicates and 13 fields are conditional on physical interpretation. Neither a machine-declared `ClayYangMillsSolution` with trivial vocabulary nor a finite-grid spectrum is an external Clay proof. Do not backfill statuses from search hints.

## Phase 0 — exact-head proof harness (TRUST.K01–K03)

| ID | Deliverable | Acceptance | Status |
|---|---|---|---|
| V00 | Pin Git SHA, Agda/compiler/stdlib and `DASHI/Unified/BalabanRGTOERegression.agda` root | Repeatable exact-head clean typecheck, no open metas, no fake `--safe` claims | OPEN: this run has GitHub readback and Python, but no local Agda binary or checkout |
| V01 | Trust/axiom DAG | Report every imported `postulate` including `RealAnalysisAxioms`, any unsafe flags and exact mathematical external authorities | OPEN |
| V02 | Regress original physical owners | Run native six-plane, signed-Wilson, finite Fubini, selected C3, blocking, full 219-field drift audit; record exact receipts | REFERENCE / kernel OPEN |

## Phase 1 — three finite exact equalities (R443.F07; R445.F16/F21)

| ID | Exact source-native term | Reused owner | Next proof step | State |
|---|---|---|---|---|
| F1.0 | `originalSortToTargetCorrect` with explicit valid-target/permutation membership | `YMClayNativeC3AdjacentSortProgramExact.originalSortToTarget`, `YMClayFiniteProductHaarPermutationExact.permuteLinks` | Prove bubble-head lemma, residual-subset/permutation invariant, induct on vector length; **not** quadratic closed reduction | OPEN |
| F1.1 | `constructedNativeC3CanonicalLabelGoal` | `YMClayNativeC3SingleVectorPermutationCertificateExact`, original C3 bond inverse | Instantiate F1.0 with original canonical label bijection | OPEN; 1024 labels / 46,592 swaps pass independent exact reference |
| F1.2 | `originalPairSpectatorLengthGoal` | `YMClayNativeSideFourPairDistinctCertificateExact` original 64 coarse, 128 distinct fine and 896 complement | Prove disjoint partition/length on original enumerated bonds, not arbitrary 1024 distinct placeholders | OPEN; exact reference passes |
| F1.3 | `originalPairSpectatorCanonicalLabelGoal` | `YMClayNativeSideFourPairSpectatorSortProgramExact` | Instantiate F1.0 from original partition; preserve pair orientation | OPEN; 41,792 swaps pass reference |
| F1.4 | All-value vector transport, original matrix links and product Haar permutation | `singleVectorC3ImpliesAllVectors`, `productHaarPermutationInvariant` | Apply only after F1.1, F1.3 and true one-link measure | CONDITIONAL existing |

**Phase-1 exit:** all three exact closed equalities typecheck against the same source head; originals retain exact canonical vector and no substitute carrier. A Python hash alone does not pass.

## Phase 2 — finite selected continuous-SU(N) Wilson/Gibbs integration (R443/R445)

| ID | Decisive producer | Already existing reusable donor | Acceptance | State |
|---|---|---|---|---|
| W2.0 | Native 6-plane spatial C3 action and density on original same SU(N) links | `YMClaySUNMatrixNativeSixPlaneC3FromInverseTraceExact` + `YMClaySUNMatrixSpatialC3RealFubiniExact` + `YMClaySUNNativeSixPlaneFullC3FromInverseTraceExact` | Original `Variable.periodicSUNGibbsDensity` decoder equality; **distinguish full CMP119 E/R/B/V terms** | SOURCE/KERNEL PENDING; CMP119 full OPEN |
| W2.1 | Actual compact complex/real SU(N) matrix group and normalized Borel Haar on explicit integrable algebra | `SUNMatrixCarrier`, `YMClaySUNVariablePeriodicProductHaarExact` | Construct measure + positivity/Fubini/translation on the original observable class; no assumption disguised as proof | OPEN |
| W2.2 | Selected actual 1024-link weighted effective-density identity | `YMClaySUNWeightedHaarPairFibreDisintegrationExact`, `YMClaySUNWeightedDisjointPairFibreReparamExact`, `YMClayNativeSideFourTwoLinkPairSameObjectExact` | Prove original `Codec.decodeOriginalBonds 4` link permutation, spectator disintegration, equality for arbitrary selected coarse cylinder F **on the original fine `e^{-S}`** | CONDITIONAL on F1/W2.1 |
| W2.3 | Coarse action honesty | `YMClayFiniteRGPushforwardNonBareWitnessSafeExact` | Distinguish `S_eff=-log ρ_eff` from pure bare Wilson; prove counterterm identity if needed, never assume it | OPEN physical |

**Phase-2 exit:** physically instantiated continuous compact SU(N) Haar and exactly same original finite Wilson source, normalized physical Gibbs pushforward and source-native action, with any remaining CMP119 terms named separately.

## Phase 3 — analytically uniform R445/R320 producers

| ID | Exact mathematical target | What a receipt must show | Status |
|---|---|---|---|
| A3.0 | Same physical selected `a_n, L_n, β(a_n)`, all-scale blocked gauge/reflection mapping | Original Wilson–Gibbs `μ_{a,L}`, compatible reflection/time slices and selected RG map; no fixed side-4 masquerading as continuum | OPEN |
| A3.1 | Uniform physical moments / tightness and continuum/thermodynamic subsequential extraction | Constants, units, original insertion/test class, dependence on `a,L`, existence and local nontriviality | OPEN |
| A3.2 | Genuine mixed-J differentiated `log Z_{a,L}(J)` on original CMP116 marked observables | Common source domain, differentiation and exact covariance identity; bounded plaquette result alone handles only restricted marks | OPEN full; finite bounded-mark mathematical sublemma documented separately |
| A3.3 | Uniform rooted-shell exponential decay `|D_FD_G log Z_{a,L}(0)| ≤ C_{F,G}e^{-m d_phys(F,G)}` | Physically appropriate positive `m`, uniform `C`, no hidden cutoff/volume dependence, same original source | OPEN — core analytic discovery |
| A3.4 | Continuum marked-correlator transport | Same state, same limit, O(4)/Euclidean time, reflection-compatible transfer to reconstructed OS test class | OPEN |

**Phase-3 exit:** proofs of original physical uniform estimates and selected limits, not just finite covariance identities or numerical fits.

## Phase 4 — R333 same-Hamiltonian physical spectral gap

| ID | Exact target | Acceptance | Status |
|---|---|---|---|
| S4.0 | Original Wilson-Gibbs reflection positivity and preservation through actual R445 blocking/limit | Nonnegative full reflected Gram matrices for original observable class; positive scalar density alone insufficient | OPEN |
| S4.1 | Physical OS null quotient, Hilbert completion, strong semigroup and `H_OS` | Same selected limiting physical measure, domains and physical time units | OPEN |
| S4.2 | Wilson transfer / spectral operator identification | Same operator for correlators, transfer matrix, OS semigroup; no independent fake gap carrier | OPEN |
| S4.3 | `H_OS|_{Ω^⊥} ≥ Δ I` with `Δ>0` | Strict physical-unit, volume/cutoff-uniform gap, full relevant Hilbert subspace, exclusion of undetected sectors | OPEN |
| S4.4 | Limit survival and nontrivial excitation | Both limits + vacuum uniqueness + local non-Gaussian or other nontrivial witness | OPEN |

## Phase 5 — external Clay scope and semantics

| ID | Target | Condition | Status |
|---|---|---|---|
| C5.0 | 219 original-field proof-relevance crosswalk | For each used field, selected physical type + theorem witness + same-object/trust graph; explicit redundancy for omitted fields | OPEN |
| C5.1 | 15 carriers, 34 predicates, 8/9/11 Clay requirement meaning | Real `R⁴`, accepted OS/Wightman QFT, O(4)/Poincaré, gauge-invariant local fields, positivity and nontriviality; prevent trivial-model endpoint | OPEN |
| C5.2 | `LiteralClayStructuralBase`, `UVToContinuumYM`, `SameHamiltonianPhysicalMassGap`, `SameFamilyLocalFieldsOPEStressWard`, `StandardSameHGaussianNontrivialityConsequence` | Physically selected witnesses fed to existing T78 compiler; not just record parameter fields | OPEN |
| C5.3 | Prescribed compact simple group scope and independently checked Clay statement | Actual all-G transport or independent per-G construction, not SU(N)-only or empty domain | OPEN |

## Mandatory receipt per change

`{head_sha, producer_id, original_owner, exact_goal, output_path, proof_status, python_reference, agda_command, agda_exit, transitive_postulates, physical_same_object, negative_controls, remaining_leaf}`

**Status taxonomy:** `VERIFIED_AGDA` only with pinned compiler/kernel receipt; `VERIFIED_REFERENCE` only for exact finite executable check; `SOURCE_PENDING` for new Agda terms without typecheck; `CONDITIONAL` for proved implication lacking a physical hypothesis; `OPEN_MATH` for unsolved analytic producer. Never translate `SOURCE_PENDING` into `VERIFIED_AGDA`.

**Immediate work order:** F1.0 generic sorter invariant → F1.1/F1.2/F1.3; in parallel W2.0 actual action/decoder and W2.1 continuous analytic Haar. Then W2.2, A3.0–A3.4, S4.0–S4.4, C5.0–C5.3. The finite cut does *not* establish or shortcut the analytic mass-gap problem.
