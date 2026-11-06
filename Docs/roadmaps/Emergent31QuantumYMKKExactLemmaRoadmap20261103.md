# 6 November 2026 — authoritative #1460 phases, deliverables and exact remaining maximum cut

**CONCRETE PHYSICAL PRODUCER PROPOSITIONS:** [40 proposed OBS/HIL/KK/BIDI lemmas](TSFVFourPhysicalCutsExactProducerLemmas20261106.md), directly mapped to original P00–P11 IDs (NOT additional canonical IDs), with required physical source constructions and `parallel_checker` receipt. **EXECUTABLE FIVE-PHASE PLAN / 48 EXACT DELIVERABLES:** [TSFVUnificationExecutionPhasesDeliverablesExactLemmas20261106.md](TSFVUnificationExecutionPhasesDeliverablesExactLemmas20261106.md). **Lane-specific [TODO](TSFVUnificationTODO20261106.md) and [implementation/verification receipt](../physics/TSFVUnificationMaxCutImplementationReceipt20261106.md)** are updated with the same proof-status boundary. This page below remains the ORIGINAL canonical 186 P00–P11 statements **and** its separately reconciled 186-row SOURCE/KERNEL/PHYSICAL status matrix. The 48 rows are an execution *index* mapping to **101 distinct existing canonical IDs**, not 48 new lemmas nor an erasure of the other 85. Source verification: `scripts/check_emergent31_complete_186_status_20261104.py` and new `scripts/check_tsfv_unification_48_phase_cut_20261106.py` (source-written, GitHub file readback/independent crosswalk inspection PASS; exact repo CI has not executed).

**S11 actual integration completed:** YM parent fixed-physical-cube/CMP116 source was merged into #1460 via [#1470](https://github.com/chboishabba/dashi_agda/pull/1470), merge commit `1f71c1d58cc2d231a0fdc42c50b0c9969d35e49b` from parent head `572de64743ade4c3fcbb092ea4be1ce70f85a3b1`. This is a genuine parent→child Git history merge, not a copy or claim of physical YM completion. #1444 remains independently owned and continues moving; future commits after pinned head are a new reconciliation obligation. Combined Golden source root: `DASHI.Unified.TSFVParentChildRegression`, with separately qualified `BalabanRGTOERegression` (YM parent) and `TSFVUnifiedRegression` (observer/KK/OS child).

**New native source owners / alpha cut:** `TSFVAcousticLocalImpulseThirdDerivativeExact.agda` proves the selected 3-axis nearest-neighbour oscillator **dynamical third-derivative** impulse response (six first neighbour directions each read coupling (c^2/a^2), farther first-third derivatives vanish and response is mass-blind). `TSFVAcousticMassInverseBidiNoGoExact.agda` proves that the same selected measured four-dimensional principal quadratic is shared by different mass terms, while the full Fourier response at zero frequency/momentum retrieves (m^2); a measured cone cannot identify a unique microscopic Hamiltonian/OS QFT. BOTH new source modules are imported and exported by the child Golden regression. **KERNEL PENDING; actual original TSVF observer/source-instrument/continuum physically OPEN**. `scripts/check_tsfv_acoustic_impulse_mass_bidi_20261106.py` committed; equivalent independent exact-rational execution 2,764 cases PASS, not an Agda receipt.

**Separate physical status, per requested maximum cut:** S01–S04 original measured observer-to-4D cone: OPEN; S08–S09 completed original Hilbert/Stone/OS same-H and spectral/Wick: OPEN; S05–S06 original nontrivial five-dimensional Einstein–matter solution whose reduction is independently measured observer g4: OPEN; S10 full same-source BIDI/limit transport: OPEN; S11 exact-head `agda --safe`, transitive trust and independent physical receipts: OPEN despite the genuinely completed pinned parent merge. The free acoustic/flat KK/free Gaussian model is a valid chosen consistency control, **not** a physical E1 solution. YM's fixed-physical-cube `OriginalPhysicalCubeConditionals` and its R467 CMP116 route are external producer dependencies, not a replacement for constructing our observer or matching an OS Hilbert.

---

### 6 November 2026 — S02 exact source impulse, free OS spectral gap and correct scope

Committed `scripts/check_tsfv_lattice_impulse_dimension_exact_20261106.py`: exact rational chosen-source 125-site local impulse has six nonzero first offsite (t^3)-response channels at (75/8), which identify three opposite pairs via original graph response and 12 transverse pairs; all 18 distance-two sites are inactive at (t^3) and active at (t^5). This is an actually measured/readable response **inside the selected analytic model**, not a measured external apparatus, physically selected original TSVF dynamics or a proof of universal emergent (3,1). The continuum sharp cone and the discrete beyond-front tails are kept strictly distinct.

The selected free Gaussian three-mode Fock Hamiltonian has mathematically exact (Delta_{m free}=hbaromega_{min}=(7/5)(5/4)=7/4) with a standard self-adjoint multiplication operator on its complete weighted domain. The GitHub reference checker now tests that energy separation, real-time versus Euclidean semigroups and spectral projections. **Not YM/R333/Clay:** the independent original continuum OS Hamiltonian still requires the #1444 worker and the original physical TSVF observer source map remains uninhabited.


### 6 November 2026 — concrete S01–S09 control, completed #1444→#1460 merge; E1 and Agda kernel still OPEN

**Primary dossier:** [physically explicit selected scalar wave, flat 5D KK Einstein vacuum and noncollapsed free-Gaussian OS construction](../physics/TSFVPhysicalS01S11ScopedConstructiveMaxCut20261106.md). Original E1 physical TSVF-selected interacting Yang–Mills unification remains OPEN; do **not** count the scoped control as P01/P02/P03/P07/P08 physical closure. No new 186 lemma IDs or optional SM/E6/antigravity claims.

| Cut | Constructed/tested this round | Exact outstanding original physical acceptance |
|---|---|---|
| **S01–S04** | Chosen 3D positive-mass nearest-neighbour oscillator lattice, explicit local impulse observer, exact Fourier response, continuum Lorentz principal, Agda rational 3+1 metric, **actual retarded early-time 125-site spatial readout**: six third-order channels, three opposite pairs, 18 nonzero fifth-order farther sites | The original TSVF many-body physical observer's **measured** local response, spacetime dimension obtained rather than preselected in a 3D graph, genuine continuum/refinement, independent causal/volume calibration and physical signal/metric identification |
| **S05–S06** | Explicit smooth flat 5D Lorentzian KK metric on R⁴×S¹ with (b=5/3), constant nonzero (A), (g_4=mathrm{diag}(-9/4,1,1,1)), exact (det G_5=-25/4), (Gamma=R_{AB}=G_{AB}=0); Einstein **vacuum** solution with (T_{AB}=0); Schur reduction equals the SAME chosen acoustic metric. Agda now includes (t_mathrm{norm}=ct_mathrm{physical}) to prevent hidden clock mismatch | An independently selected **nontrivial** 5D Einstein–matter/YM source and original observer g4, coupling/field variation/stress, radion stabilization, physical energy/experimental data, dimensional reduction/limiting estimates |
| **S08–S09** | A **noncollapsed infinite-dimensional** massive free Gaussian Fock Hilbert (ell^2(mathbb N^M)), diagonal positive self-adjoint (H), weighted domain, dense finite-support invariant core, spectral projection indicators, real unitary and Euclidean contraction from the SAME H, analytic Wick matrix element, Gaussian 2-point reflection-positive Gram; scoped SymPy/NumPy controls passed | Actual original TSVF physical complex Hilbert, its Stone group and original **interacting** OS/Yang–Mills reconstruction on one source; the real unitary onto and common H/domain/spectral/observable algebra plus full OS axioms and Wick; external free Gaussian theorem is not the YM source |
| **S11** | **Genuine GitHub merge**: reverse integration PR [#1469](https://github.com/chboishabba/dashi_agda/pull/1469) merged parent #1444 → child #1460 at `04511937031bee49a2667a4b6fc14309f5533470`. Child showed zero commits behind donor parent after merge. 20 previously shared native paths identical; five divergent files brought to exact parent blobs; child-only edits preserved at `Docs/physics/TSFVUnificationChildOnlyAdditions20261106.txt`. Split `DASHI.Unified.TSFVUnifiedRegression` and `DASHI.Unified.BalabanRGTOERegression`, combined with `TSFVParentChildRegression`. Focused [GitHub Agda/Python CI workflow](../../.github/workflows/tsfv-physical-maxcut-source-audit.yml) committed | Agda binary absent locally; **GitHub reports zero child-branch workflow runs**. No exact merged-head Agda `--safe`, transitive trust, independent theorem referee or measured physical E1 receipt. Need execute real CI and correct errors, not infer acceptance from syntax/static tests |

**Independent local evidence:** `scripts/check_tsfv_selected_scalar_kk_os_control_20261106.py` is committed for reproducibility; a mathematically equivalent SymPy 1.14 source was executed locally and PASSED its exact lattice dispersion/response principal, full rational KK inverse/Schur/Einstein-vacuum curvature and finite-core Fock spectral/OS reference. `scripts/check_tsfv_lattice_impulse_dimension_exact_20261106.py` reproduced exact Fraction source results: 125 sites, six active (t^3) responses, 3 opposing pairs, 12 transverse pairs, 18 nonzero (t^5) farther sites, no false finite-spacing light cone. The actual committed GitHub scripts have not run through the repository CI. A finite sampled 2-point Gaussian positivity matrix alone is not a proof of all OS axioms; the complete Fock construction uses externally known free Gaussian results and does not transfer to YM.

**S11 same-source next kernel root:** `DASHI/Unified/TSFVParentChildRegression.agda` imports BOTH the latest native YM parent regression and the separate TSVF original unification regression under qualified names; CI job now attempts selected sources, both roots and the combined transitive root. **Status SOURCE-WRITTEN, KERNEL UNVERIFIED, original PHYSICAL OPEN.** As the parent evolves, freeze its next exact HEAD before further reconciliation.

### 5 November 2026 — P07 complete selected-domain operator-graph BIDI (SOURCE; KERNEL/PHYSICAL OPEN)

The original `TSVFOSRealTimeDifferenceQuotientGeneratorWeldExact.agda` now derives **whole graph equivalence**, not only a chosen forward-ket equality or algebraic operator-power identity. `OriginalObserverEnergyGraph` records `ObserverGeneratorDomain a × (H_obs(a)≡b)`, and `OriginalOSEnergyGraph` records `OSDomain (J a) × (H_OS(Ja)≡Jb)`. `originalPhysicalEnergyGraphForward` derives the forward graph map from the existing all-domain source-generated energy equality, while `originalPhysicalEnergyGraphBackward` derives its reverse from the original clock's actual `decodeEmbed` law and the earlier *derived* two-way strong-domain equivalence. `originalMatchedPhysicalEnergyGraphsBidi` proves the logical iff on **every** original observer state/output in the supplied domain, without postulating another Hamiltonian equality.

This source theorem is algebraic and CONDITIONAL on `OriginalIsometricStrongLimitSource` and `PhysicalHbarEnergyConversion`. The original OS `Hamiltonian : Set` field is not by itself a self-adjoint Hilbert operator. **KERNEL PENDING, PHYSICAL OPEN:** the actual physically selected noncollapsed complete observer/OS Hilbert, real time and scalar units, dense invariant domain, self-adjointness, spectral projections, Schwinger/OS reflection positivity and Wick continuation remain required. Equality of a chosen conditional graph is not a completed Clay YM mass gap.

The independent C² source-control runner `scripts/check_tsvf_original_os_strong_domain_bidi_20261105.py` now passed **377** cases locally: 215 real-time/Euclidean unitary/group/generator controls, 150 exact rational H^n transport identities and 12 exact graph-membership BIDI cases including incorrect-output countercontrols. The actual GitHub script source is committed but not run by a repository checkout. This is a numerical/algebraic TEST receipt, not an Agda KERNEL receipt.

All original **186 unique** canonical P00–P11 ID statements and **186 status rows** remain identical; the complete status checker has been evaluated on the live GitHub roadmap and passed. YM/Clay #1444 remains a separate worker's physical endpoint.


### 5 November 2026 — P07 two-way strong-domain BIDI and finite all-power moment theorem (SOURCE / KERNEL PENDING / PHYSICAL OPEN)

**P03.L09–11 / P07.L05–07 / P11.L05 exact source advance:** `TSVFOSRealTimeDifferenceQuotientGeneratorWeldExact.agda` now uses the ORIGINAL `OriginalTSVFToOSClock.embedObserver` **and its ORIGINAL two-sided `decodeObserver` inverse** to derive observer→OS and OS→observer sampled strong-derivative transport. It derives unique observer strong limits from original OS-limit uniqueness, and a genuine **bidirectional equivalence of generator domains** once the actual observer domain is proved complete for strongly differentiable vectors. The theorem does not assume domain equivalence as a second independently chosen H field.

**Pareto cut paid conditionally:** `OriginalIsometricStrongLimitSource` requires one shared original observer/OS distance comparison, a matched convergence-to-target predicate and its topology. The source now DERIVES both forward and inverse strong-limit continuity from that same isometry and both ORIGINAL inverse maps: `originalMetricSourceProducesInverseHilbertContinuity` and `originalMatchedMetricSourceForcesTwoSidedGeneratorDomains`. The actual physical Hilbert distance/norm, real time, Cauchy completion, strong operator topology, density, self-adjointness and source-owned OS reconstruction remain **OPEN**, not manufactured by this abstract source record.

**Algebraic energy powers on full domain:** Given one physically populated invariant energy core (the exact remaining input `OriginalInvariantPhysicalEnergyCore.originalObserverEnergyPreservesDomain`), the ORIGINAL prior same-H energy equality now inductively derives `originalPhysicalEnergyPowersIntertwine` for EVERY `n : Nat` and EVERY original observer vector in its actual domain, plus `originalSelectedForwardKetEnergyPowersIntertwine`. The result is `J (H_obs^n psi) = H_OS^n (J psi)`. It is NOT an actual selected spectral measure, a spectral-projection theorem, an OS mass gap, or proof of full-domain physical self-adjointness.

**P01/P02 independent information bound:** `TSFVOriginalFiltrationFiniteCausalDiamondNonpromotionExact.agda` adds a SHARP finite-channel result: no 1-bit source sensor combined with the ORIGINAL 3-level observer filtration reconstructs all x/y/z diamond branches; an explicitly CHOSEN 2-bit source label does reconstruct the ORIGINAL 5 diamond events. The 2-bit finite decoder is not a physical sensor, a propagation operator or an emergent 3-dimensional continuum. Legacy diamond import means this remains non-Golden.

**Independent TEST receipts:** `scripts/check_tsvf_original_os_strong_domain_bidi_20261105.py` was run in an equivalent local copy: 215 finite C² complex-unitary/analytic controls plus 150 exact rational H^n moment cases = **365 PASS**, reproducing the code committed on this branch. `scripts/check_tsfv_original_diamond_spatial_bits_bidi_20261105.py` reference: all 32 one-bit 5-event assignments impossible, all 64 two-bit spatial assignments counted, exactly 24 injective assignments, chosen finite source decoder of all 5 events PASS. These checks are independent mathematical controls; Agda compiler absent and current GitHub code not checked by Agda kernel.

**Remaining hard cut:** actual physical spatial source, 4D continuum and propagation Q (S01–S04); source-owned noncollapsed completed physical Hilbert, strongly continuous real-time Stone group and operator-domain/spectral/OS compatibility (S08–S09); actual selected smooth 5D Einstein–matter/KK solution and SAME measured g4 (S05–S06); parent YM/Clay R443/R445/R320/R333 remains other worker, source integration S11 still OPEN. Original 186 canonical lemma IDs and 186 source/kernel/physical owner rows remain untouched.

### 4 November 2026 — P00 parent/child source-integration warning

At this readback, **YM parent #1444** head `55670ec4089e3eaeab5f4454f5b8db5bbc5f5c27`; **unification child #1460** head before this documentation receipt `015f9a6d8ac1a33920385c5ba1bb5411dda62ec4`. GitHub `compare(parent branch, child branch)` returns **diverged**, child ahead by 263 commits, behind parent by 204 commits (97 changed-file entries in that compare). **P00.L02 remains OPEN:** integration needs a conflict-aware parent→child reconciliation followed by exact-head Golden Agda and regression checks. The other worker's native R443/R445/R320/R333/Clay work must not be overwritten or recast as child code. In particular a source-written #1460 theorem that imports an earlier native YM owner is not automatically typechecked against later parent changes. No clean merge/CI receipt is claimed by this note.

### 4 November 2026 — Pareto/alpha continuation after full 186-status appendix

**Roadmap coverage:** Canonical P00–P11 statements and the complete 186-ID, owner-annotated, SOURCE/KERNEL/PHYSICAL appendix below. None is promoted to physical closure by a conditional theorem, finite fixture, old parent receipt or Python reference. P05/P06 remain independently owned by the YM worker.

**High-alpha P08/P11 backward steelman:** `TSFVKKHorizontalReductionNoninjectiveBidiExact.agda` (Golden candidate) consumes the **original** `TSFVKKSelectedHorizontalMetricSchurExact.KK5Bilinear`, not a new abstract KK model. For *any* original four-bilinear `g4` and original chart connection `A`, the horizontal 4-metric is independent of radius `b²`; on a unit vertical displacement the 5D bilinear minus `g4` equals `b²`. Hence two distinct radii cannot define the same *whole* 5D bilinear although they reduce to the identical `g4`. The same source proves that two chart connections reduce to the identical `g4`, but offdiagonal 5D vertical differences read the chart `A(v)`; **distinct local potential coefficients are not necessarily gauge-inequivalent physical geometries**. This is an exact BIDI non-injectivity theorem and a necessary physical fifth-sector-measurement specification, not a 5D Einstein solution, not a measured radius, and not proof of a unique 5D lift. Regression root exports all eight new source theorem surfaces.

**High-alpha P01/P02 backward steelman:** The original `TSFVOriginalFiltrationFiniteCausalDiamondNonpromotionExact.agda` is strengthened: if a measured spatial sensor plus the original three-level filtration genuinely decodes the ORIGINAL diamond's x/y/z branches, then its readings for all three branches are **pairwise distinct**, as independently derived necessities. This supplies a precise empirical S02 spatial-discrimination target. No actual physical sensor, retarded response, 4D causal field or principal symbol is constructed. This dependency remains intentionally non-Golden because the old finite diamond import has not been audited transitively safe.

**Independent reference:** equivalent local rational tests passed 24,000 distinct-positive-radius same-g4/nonidentical-5D vertical readout cases and 36,000 chart-connection horizontal/mixed-vertical identities; the repo checker `scripts/check_tsfv_observer_kk_os_same_source_20261104.py` was extended, but its exact checkout could not be retrieved here. The original 40,000 horizontal/gauge and 20,000 invertible-shear reference checks remain separate. **No Agda compiler/typecheck or actual physically sourced fifth-sector input.**

**Next physical Pareto cut remains S01→S04, S05→S06 and S08→S09** (S07 YM delegated), plus exact-head source graph verification S11. These are physical existence obligations, not consequences of rational congruence or finite BIDI proofs.

### 4 November 2026 — completeness question answered: BIDI is needed NOW

[Exact physical completion and bidirectional steelman cut](../physics/TSFVPhysicalCompletionBidirectionalSteelmanExactCut20261104.md) audits the existing 186-ID roadmap and explicitly separates three endpoints: E0 conditional source-transport theorem, E1 *physically inhabited* selected source/observer/(3,1)/OS/optional KK existence and same-object identity, E2 universal emergence across a specified microscopic source class. **186 distinct obligations are a useful necessary-obligation inventory, not an exhaustive sufficient lemma DAG.** An actual selected instrument, physically measured propagation operator, 5D solution and complete observer/OS Hilbert can reveal additional regularity/coercivity/compactness/limit/domain/no-go obligations. This is not fixed merely by enumerating further algebraic source adapters.

**Early P11 forward/backward gate:** independent observer-source -> physical cone (and reverse retarded response/dimension/scale); physical KK Einstein action -> actual reduction (and reverse lift nonuniqueness, radion/connection/stress observables); real observer Hilbert/Stone -> physically reconstructed OS H (and reverse OS correlations, null quotient, self-adjointness, real-time vs Euclidean continuation). All comparisons require the SAME source/state/gauge/coupling/cutoff/boundary/observable/units and quantified limit error. Reuse existing FormalClaimTransportGeometryExact, SectionedProjectionProvenanceBridgeExact and YMClayFiveSectorBidiSteelmanExact, rather than defining a competing BIDI framework.

**Current smallest source-family cut:** physically selected observer instrument/pointer/conditional source; spatially resolving causal response and 4D refinement/dimension/real principal symbol; chosen smooth 5D Einstein-matter/KK solution and measured-reduction equality; actual noncollapsed observer/OS complex Hilbert/Stone/physical operator; unitary onto and spectral/Schwinger intertwinement; limit coherence and exact-head Agda safe+transitive trust audit. The #1444 worker owns the independent 4D YM/OS source, not our actual observer↔OS same-H physical identification. Explicit negative controls: finite spatial collapse, KK lift nonuniqueness, arbitrary Hamiltonian carrier not a physical operator, false Euclidean=unitary step identity, and observer-only marginal/correlation nontransport.

### 4 November 2026 — P01/P02/P03/P07/P08 focused closure and original source reuse

Original 186 roadmap lemma IDs retained. New files:
- TSFVOriginalFiltrationFiniteCausalDiamondNonpromotionExact — imports the original five-event three-branch finite causal diamond and its genuine causal edges; their natural projection preserves the original observer-access preorder but necessarily collapses all three spatial events. No filtration-only decoder can recover x/y. Non-Golden legacy dependency; physical local propagation remains OPEN.
- TSFVKKFiveMetricInvertibleShearExact — proves actual rational KK 5-metric shear/inverse and pointwise congruence to the original 4D bilinear plus fibre square, with nonzero connection allowed. Physical selected metric/source, positive radion and actual full 5D Einstein-matter solution remain OPEN.
- TSVFOSRealTimeDifferenceQuotientGeneratorWeldExact — DERIVES the original observer/OS time derivative generator intertwinement from real-time unitary group intertwinement, J linearity, strong limits and limit uniqueness, then DERIVES physical energy operator intertwinement if the same J is complex-linear for the selected i*hbar scaling. The target consumes the original OS reconstruction's Hamiltonian value, not a second Hamiltonian. Correct SI-time Euclidean semigroup is exp(-tau H/hbar); it is not directly equal to real-time exp(-itH/hbar). Noncollapsed physical Hilbert, strong continuity, densely defined self-adjoint domains, spectral calculus and analytic continuation all OPEN.

Independent equivalent Python reference passed 27 access triples, 7 finite-diamond edges, 40,000 exact rational KK horizontal/gauge equalities, 20,000 exact KK shear equalities, and noncollapsed two-level complex-Hilbert numerical real/Euclidean time controls. Actual committed script not executed from checkout; Agda binary unavailable and kernel acceptance pending. Same technical dossier: Docs/physics/TSFVObserverKKOSSameSourcePhysicalMaxCut20261104.md. Other worker exclusively owns R443/R445/R320/R333 and Clay.


### 4 November 2026 — physical same-source max-cut tightened, parent YM worker independent

**New focused technical dossier:** [original observer, actual KK metric and real-vs-OS generator](../physics/TSFVObserverKKOSSameSourcePhysicalMaxCut20261104.md). After reconciling the other worker's #1444/#1460 attachment, #1460 reused the newly present `TSVF2017ControlledComplexOrderedRateBridgeExact` and `ControlledCorrelationBornError` original Q.ABL sources. We did NOT redo their rate/correlation work or touch the independent YM R443/R445/R320/R333 physical theorem.

- **P01.L06–L10 / P02.L01, SOURCE only:** `TSFVOriginalObserverVisibilityCausalOrderExact` builds the actual original 3-level event-access partial order from `HistoryWeightFiltrationExact.visibleAt` (strict gain witnessed by original intermediate/terminal events). `TSFVOriginalObserverSectionedProjectionReuseExact` instantiates preexisting `SectionedProjectionProvenanceBridgeExact` at *actual original* observer `(PastRecord,TerminalAccess)` and populates the prior `ResidualReopening`; old fibre-constant reconstruction survives, but the original late terminal observable provably cannot factor through the early past record. This non-Golden adapter is not imported through the Golden regression root.
- **P01→P02 selected-state transport, SOURCE / PHYSICAL OPEN:** `TSFVObservedPhysicalAccessTransportExact` derives a two-way equivalence between the original event-access relation and the *same* `SelectedTSFVToLorentzPhysicalSource.observedFiltration selectedState`, with real selected-event gain and observed terminal-arrow association. It is conditional on inhabiting that existing physical source. No spacetime null propagation, dimension-4 continuum or principal symbol is manufactured.
- **P02.L09–11 / P08.L02/L12, SOURCE / PHYSICAL OPEN:** `TSFVKKSelectedHorizontalMetricSchurExact` proves genuine rational KK horizontal/Schur reduction with **nonzero** U(1) connection, five-metric off-diagonal blocks and fibre-gauge covariance; freezing the fibre coordinate instead retains a quadratic A² correction. `TSFVKKActualSelectedMetricHorizontalWeldExact` composes this with the *actual original* `SameMetricTSFVKK`, giving the exactly same observer bilinear, selected 5D/4D reduced bilinear and identical time axis **conditional** on two explicitly physical matching theorems: the selected 5D metric has the KK block form and the observed 4D bilinear is the reduced metric's bilinear.
- **P03.L09–11 / P07.L05–11: CENTRAL CORRECTION, SOURCE / PHYSICAL OPEN:** `TSVFOSRealEuclideanTimeSeparationExact` proves a hard no-go directly against original `OriginalTSVFToOSClock.oneStepIntertwines`: a norm-isometric observer/OS identification plus norm-preserving real-time observer step cannot directly equal a strictly contractive positive-time Euclidean OS step on the same excited state. The original `osStep` was only an abstract step; physical P07 must identify a **common self-adjoint OS generator** under proper real-time unitary `e^{-itH/ħ}` and Euclidean transfer `e^{-τH/ħ}` for τ in seconds (or `e^{-sH}` in inverse-energy units), with Stone/OS domains and analytic continuation. The one-step finite Nat theorem is not invalid; the false physical identification is prohibited.
- **Independent test:** an equivalent local exact Python reference passed all 27 original access-chain transitivity triples, strict original event witnesses, 40,000 rational KK Schur/connection/gauge equalities with a nontrivial frozen-fibre negative control and a finite isometry-versus-contraction negative control. Source script `scripts/check_tsfv_observer_kk_os_same_source_20261104.py` is committed as reproducible reference, but exact committed checkout was not run. This is TEST only, not KERNEL.

**Frozen physical cut:** physical measured causal light cone/4D dimension (P02) and physically selected pointer/observer N-body preparation (P01); *actual* smooth 5D metric/action and observed same-bilinear evidence (P08); strongly continuous physical observer/OS unitary **same generator** and spectral core/units/continuation (P03/P07). The OS owner currently records an abstract `Hamiltonian : Set` and element, not an automatically constructed self-adjoint Hilbert operator. These remain OPEN. Golden Agda exact-head compile/transitive zero-postulate audit also OPEN. The original 186 P00–P11 lemma IDs are untouched.

**4 November 2026 P01 correlated Born-error correction (SOURCE, kernel pending):** `TSVF2017ControlledComplexOrderedRateBridgeExact.ControlledCorrelationBornError` takes an actual complex whole-environment wrong amplitude and a separate nonnegative `delta` with `Born_global <= original independent controlled ABL wrong numerator + delta`. It derives `2^k Born_global <= 1+2^k delta` and the corrected two-channel cross inequality `(2^k+1) Born_global <= 1+Born_global+2^k delta`, without pretending reduced local density matrices factorize the global state. The selected correlated amplitude still needs a genuine original physical ABL pre/postselected ensemble, source-derived `delta` and P07 real-time/OS clock. Independent 3200 Fraction reference fixtures passed. See `Docs/physics/TSVF2017ControlledComplexOrderedRateOriginalABLMaxCut20261104.md`.

**4 November 2026 P01.L15/L16 finite-complex improvement (no new lemma IDs):** [controlled complex ordered-rate original-ABL dossier](../physics/TSVF2017ControlledComplexOrderedRateOriginalABLMaxCut20261104.md) and `DASHI/Quantum/TSVF2017ControlledComplexOrderedRateBridgeExact.agda` directly compose the original controlled complex emitter, heterogeneous independent Hermitian records, original ABL numerators/denominators and ordered rational weights. Under actual emitted-site `2*siteBorn <= 1` certificates and *actual complex gamma-product Born weight* `<=1`, source-written `(2^k+1)*wrongABL.numerator <= rightABL.denominator`; existing `3/5,4/5` is certified. The previous Nat-calibration proxy is not a prerequisite. Independent 3000 complex-Fraction fixtures / 21000 identities and 2 negative controls passed. **Agda acceptance pending; physical many-body independence, final effect, real-time/OS generator and Clay all remain OPEN.**

**4 November P00 parent/child cross-PR receipt:** parent YM #1444 contains later physically selected R445 F08–F12; downstream #1460 and parent currently diverge from their earlier shared source. Of 26 overlapping changed paths, 20 currently have exact same blob SHAs, including all overlapping YM Agda sources; 6 documentation/root-regression files differ. **P00.L02 stays OPEN** until the parent physical source modules and child's TSVF/KK changes are reconciled without overwrite, with exact-head compiler receipts. No 186-ID renumbering or change to the original 219-field Clay inventory.

### 4 November 2026 — dedicated PR #1460 original unification lane, separate from Clay/YM worker

**Division of labour (explicit):** The other worker owns standalone YM R443 (SU(N) Haar/C3/CMP119), R445 (effective coarse measure/UV), R320 (selected mixed-J CMP116), R333 (same-H physical OS gap) and the final 4D Clay theorem in parent #1444/#1440. **THIS #1460 lane owns P01 original reversible history and filtration, P02 measured causal (3,1), P03 observer Hilbert/Stone, P07 exact observer-clock/OS metric/Hamiltonian same object, and optional P08–P11 selected KK/stress/terminal comparison.** Parent YM source is imported when useful, not rebuilt or claimed to be solved. No child import into parent.

**P01.L07–L10 NEW SOURCE, physical OPEN:** `TSFVOriginalHiddenHistoryFiltrationWeldExact.agda` uses the actual original `FiniteHistoryOrientationExact.hiddenHistory`, `pastAccessibleOutcome`, `smoothedEstimate`, and the actual original `HistoryWeightFiltrationExact.visibleAt` in ONE concrete observer readout. The original two boundary choices have equal early (quiet, terminal hidden) records, unequal terminal (quiet, minus/plus) records, equal action, and no correct decoder from the early readout to both selected histories; late-to-early forgetting is explicitly noninjective. This pays a finite source-to-filtration map, NOT physical class operators, causal interventions, N-body TSVF, real temporal semigroup or entropy law.

**P02.L11/L14 + P07 NEW SOURCE, physical OPEN:** `TSFVKKSameArrowQuadraticMetricWeldExact.agda` strengthens `TSFVKKSameMetricTransportExact`. Previously we obtained the same (3,1) COUNT from one physical selected KK metric and original TSFV quadratic signs. Now, existing same-metric pointwise signs plus existing independent KK and TSFV calibrated Boolean probes imply **the exact four-axis measured probe values are pointwise identical**, because original `Lorentz31DirectionalProbeExact.classifyProbe` is injective. A direct proof constructs the KK directional witness from the original observer witness and proves even the KK source's preexisting independent directional certificate selects the **identical axis**, without an extra axiom or another 31-code. **Conditional on actual inhabitation of `SameMetricTSFVKK`, not a constructed physical metric or real observable.**

**P07.L15–16 NEW SOURCE, physical OPEN:** `TSVFOSSameSelectedClockIterateExact.agda` now derives the original Nat-indexed step iteration addition law and lifts the stricter same-physical KK observer time-axis theorem to its existing `SameMetric31ClockUpgrade`. This is the original finite TSVF ket evolution/OS-indexed H source, not a theorem of a strongly continuous real-time unitary, shared dense self-adjoint generator domain, spectrum or clock units. Real Stone/OS Hilbert physics remains the decisive missing bridge; original OS R331 transfer coordinate remains selected definitionally, but its physical meaning and one-step intertwiner are inputs.

**P01.L08/L10 and P02.L14 NEW negative source proof:** `TSFVOriginalShiftMDLArrowNonpromotionExact.agda` directly imports original `ShiftLorentzEmergenceInstance`, `ShiftRGObservableInstance` and `FiniteHistoryOrientationExact`. It proves `ShiftArrow` for the original 1+3 ternary shift is **definitionally constant zero** and cannot decode either of the two distinct original selected hidden histories under ANY history→shift map. From the actual existing coarse fixed-point `shiftCoarseFixed`, it also rejects global strict Nat MDL descent for the original selected shift step; the true earlier MDL **nonincrease** still stands. This narrows the real task to constructing a **different physically measured** observer-to-shift causal/time map, not labeling constant `ShiftArrow` as emergent physical time. This dependency cone is **non-Golden** (older shift imports), no Agda compiler receipt.

**Independent TEST:** `scripts/check_tsfv_original_same_arrow_filtration_20261104.py` executed locally: all 9 original finite history reversal/action pairs, both original boundary choices across 3 visibility levels, 16 four-axis Boolean profiles and 16 same-sign identity cases, 4 unique time axes with the deliberately false same-count⇒same-axis control, all 81 1+3 ternary constant-shift-arrow inputs. Exact reference, not Agda kernel nor physical theorem. The original **186** lemma IDs remain unchanged; no SOURCE row is promoted to PHYSICAL, Stone, KK reduction or YM.

**Immediate P0 next physical payments:** (i) actually construct a single map from original history/filtration and/or shift dynamics to the selected measured physical quadratic/cone, rather than merely interpreting preexisting finite labels; (ii) inhabit `SameMetricTSFVKK` with an actual selected 5D metric, physically reduced 4D metric and same observed state, including gravitational stress/sector consistency; (iii) construct P07 strongly continuous real-time selected observer/OS unitary equivalence with common dense generator domain, spectrum and `OS.hamiltonian` meaning, *on the original selected Hilbert source*. Other worker remains owner of YM Haar/continuum/physical mass gap.

**Verification boundary:** GitHub PR writes/readback only for the new Agda; no local `agda` installed, no exact-head Golden kernel/typecheck or transitive postulate proof. Original author/in-repo owner attribution maintained.

**P07 fail-closed correction:** the optional (3,1)/5D-KK same-metric upgrade now requires a typed actual original TSVF forward-ket → selected causal/Lorentz physical-state map with equality to the very selected reduced 4D metric-state object. Finite observer/OS one-step intertwiners still prove all finite iterates, while the earlier arbitrary ContinuumStoneOSClockMatch Set field has been removed: real-time strongly continuous group, Stone/Ward dense-core and full OS-gauge Hilbert are NOT manufactured. This respects standalone pure 4D Clay independence.

### 2026-11-03 exact 2017 complex ABL and original indexed OS-clock MAX-CUT

[New four-module quantitative source ledger](../physics/TSVF2017ComplexABLAndOSSameClockMaxCut20261103.md). Original BidirectionallyAdmissibleHistoryFibre, original Q.TSVF, original CayleyDickson complex, rational order and original R331 OS-indexed Hamiltonian ownership are reused.

- **P01.L13:** actual finite rational-complex Hermitian two-coordinate/environment source and arbitrary complex gamma products SOURCE; physical N-body apparatus with independent/correlated disturbance classes OPEN.
- **P01.L14:** nonvacuous original two-boundary histories, orthogonal complete projectors, original Q.ABLContext with constructed positive selected total and original Q.ablProbability common-denominator normalization SOURCE; physical Hilbert/pre-postselection OPEN.
- **P01.L15:** complex gamma Born product, environment overlap norm for all k=N-n, exact probability-odds cross identity, unsquared gamma i-phase no-go and exponential source bound SOURCE; physical Eq.23–25 gamma conventions and disturbance bounds OPEN.
- **P01.L16:** conditional finite original ABL robustness and adversarial gamma negative controls SOURCE; actual physical macroscopic reverse-evolution OPEN.
- **P07.L15–16:** original OS.hamiltonian reconstruction indexed by original R331 transfer coordinate, and finite all-n observer/OS step-readout commuting from explicit one-step physical intertwiner SOURCE. Full real-time strong continuity, physical unitary, Stone common domain and same-state gauge observables OPEN. Optional 5D KK same-metric continuation remains separate; standalone 4D Clay R443/R445/R320/R333/H6 unchanged.
- **Primary paper Eq25 ambiguity:** Eqs23–24 use gamma as overlaps, yet printed probability odds display unsquared gamma products. The complex i vs 1 negative control separates phase amplitudes from Born weights. The physical paper's intended convention is unresolved, not silently repaired.

**Total remains 186 exact lemma IDs; physical terminals OPEN. No kernel typechecking or original physical source claim.**

**Further P01.L13/L14 finite source strengthening:** the concrete original TSVF two-outcome projectors now prove completeness (P_R+P_W=identity), mutual orthogonality and idempotence. The source-owned two-boundary admissibility relation is no longer all-true: the chosen three-history carrier admits two outcomes and **excludes a third** by a genuine empty-admissibility proof. Both selected outcomes still use the original Q.ablProbability with one positive denominator and the same independent tensor overlap. This is SOURCE, not kernel/physical. The finite quantum state remains a rational real/nonnegative coordinate submodel, not physical complex Hilbert, and P01/P07 physical inputs remain OPEN.

# Emergent (3,1) → quantum mechanics → Yang–Mills → KK: exact-lemma roadmap

**Canonical 3 November 2026 cross-lane roadmap. Status: ACTIVE and predominantly OPEN.** This is the proof plan for the deliberately speculative [actual steelman](../physics/Emergent31HistoryQuantumYMKKSpeculativeSteelman20261103.md), not a claim that the theory is true. Preserve the original [Clay YM roadmap](ClayYMProofRoadmap.md), [core physics theorem roadmap](CorePhysicsTheoremRoadmap.md) and [complete physics unification roadmap](CompleteVerifiedPhysicsUnificationRoadmap.md) as distinct owner inventories.

## 1. Completion target and correct proof semantics

**Proposed terminal theorem:** a single selected microscopic history/observer system yields (a) a measured causal continuum with independently derived four dimensions and one time orientation; (b) a positive complex Hilbert quantum representation with one strongly continuous unitary time evolution; (c) the selected local gauge source and independently complete pure four-dimensional non-Abelian YM theory; (d) a reflection-positive Euclidean YM continuum whose OS physical Hilbert space and self-adjoint Hamiltonian are **unitarily identified** with the observed Lorentzian (3,1) quantum clock; (e) a strictly positive gauge-invariant spectral gap in the continuum and infinite-volume pure YM theory; and (f) optional but, for the five-sector steelman, mandatory consistent physical 5D spacelike KK extension, rigorous selected 2D/3D backward observable comparisons and single-source gravity/stress.

**Central same-object requirement:** physical clock state, causal metric, selected gauge field and Wilson source, Schwinger/OS state, Hamiltonian and KK-reduced metric must agree under explicit source-indexed maps. Model equality means unitary/observable/metric equivalence at **matched couplings, fields, boundary conditions, gauge group, units, limit order and physical sector**, not identical dynamics in different dimensions. Else provide a proved approximation bound or an explicit incompatibility.

**Evidence codes:** OWNED = actual existing theorem owner; SOURCE = Agda proof term written but not exact-head compiled; COND = theorem accepts missing physical certificates; TEST = independent finite numerical check; OPEN = selected physical premise unproved; KERNEL = exact-head Golden Agda acceptance including transitive no-postulate audit; PHYSICAL = same-source limit genuinely constructed and the required physical hypotheses inhabited; EXTERNAL = appropriately attributed scientific result at its original scope.

**Golden rule:** safe Agda, 0 postulates, 0 unsolved metas, 0 termination bypasses in the full proof cone; Lean downstream. No fake Bool gate, synthetic numerical fixture, uninhabited Set, assumed source equality or conditional theorem may be promoted as full physics. Record every exact lemma with its actual owner, source SHA, type signature, assumptions, numerical/negative controls, kernel acceptance and selected physical population. The inventory below is exhaustive **relative to the proposed theorem specification**; new hard-analytic sublemmas discovered during proof must be added explicitly rather than pretended away.

**Verified P00 selective source sync (3 Nov 2026):** #1444 at pinned head `7c6b2efd2a68ff4b280160af54616663f9b3a8a6` has six new all-n physical/finitely formal source files: YMClayNativePositiveBondEnumerationVectorExact, YMClayNativeFiniteGaugeVectorNaturalitySafeExact, YMClaySUNVariablePeriodicProductHaarExact, YMClaySUNVariablePeriodicGaugeHaarExact, YMClaySUNConstructedPeriodicGaugeCodecExact and YMClaySUNVariablePhysicalCutoffFamilyExact. The six source contents were **copied into #1460** and their GitHub blob SHA/content compared with #1444; all six match exactly. Two pre-existing owners BalabanFiniteEnumerationDistinctExact/CompactLieGroupCore were given the identical new upstream `--safe` header, and five new Golden modules are re-exported by BalabanRGTOERegression. The sixth moving-cutoff analysis family lacks a `--safe` header and is intentionally **not imported** by the Golden root. This is a selective file sync, **not** a full branch merge, completed typecheck or physical Haar construction; P00 merge reconciliation, Agda safe transitive audit, literal one-link Haar and R445/R320/R333 physical source remain OPEN. Route-S #1440 is upstream; KK #1241 and exotic gravity #1120/#1132/#1045/#1284 remain independent donors unless merged.

## 2. Dependency graph, deliverables and proof cuts

Phase DAG:

- **P00** owner/branch reconciliation → P01 history and P02 causal geometry + P03 quantum representation.
- P03 → **P04** actual quantum gauge source → **P05** physical finite R443 Haar/Wilson → **P06** R445/R320/R333 full constructive YM.
- P01 + P02 + P03 + P06 → **P07** same-clock/same-metric OS–Lorentz theorem. This is the decisive (3,1) bridge.
- P02 + P04 → **P08** genuine 5D KK action/metric/holonomy/decoupling.
- P05 + P08 → **P09** independently checked 4D→3D→2D observables.
- P07 + P08 → **P10** same-effective-action quantum stress/GR/exotic discriminators.
- All → **P11** global BIDI limits, independent tests, referee receipt and terminal theorem.

**Shortest immediate Pareto max-cut, with assigned workers:** **this #1460 lane:** P00 source/Agda trust; P01 physically populated selected observer/history and causal-access map; P02 actual local propagation principal symbol/dimension and measured bilinear (beyond the finished three-level access chain); P03/P07 noncollapsed Hilbert and **one real-time Stone/OS unitary and self-adjoint common generator**, not identification with the Euclidean OS contraction; optional P08 actual selected physical 5D KK metric/action/stress matching the exact horizontal Schur form. **Other worker:** P05 R443 SU(N) Haar, P06 R445/R320/R333 continuum and the independent Clay endpoint in #1444/#1440. No doubled mathematical owner or false child→parent import.

**Standalone Clay completion is independent:** physical P05/P06 alone may complete a literal Clay result if the full theorem conditions are satisfied. P01–P04 and P07–P10 are additional proposed unification statements; they may neither fabricate nor veto an independently rigorous Clay result.

## P00 — source authority, existing owners and branch integration

**Deliverable:** source-pinned proof graph, actual chosen physical source model, exact-head import compiler receipt. **Exit:** #1460 can actually see all intended #1444 modules and sources; all imported theorem owners have traceable proofs.

- [ ] **P00.L01** Pin exact SHA/base/imports and owners for PR #1440/#1444/#1460; keep #1241/#1120/#1132/#1045/#1284 separately labelled.
- [ ] **P00.L02** Integrate latest #1444 variable-periodic Haar and gauge modules into #1460 without discarding later work; verify real file readback and conflicts.
- [ ] **P00.L03** Search/import existing signed plaquette, Wilson trace, SU(N) matrix, Haar, BIDI, signature, Hilbert, Stone, Möbius and source-stress owners before creating aliases.
- [ ] **P00.L04** Check Golden focused Agda roots against a pinned Agda/stdlib revision, with 0 metas/postulates/unsafe imports/termination overrides including transitive dependencies.
- [ ] **P00.L05** Distinguish original analytic axioms/external sources from inhabited proof terms; no dummy proof object may supply the desired physical conclusion.
- [ ] **P00.L06** Create source-to-object map for microscopic state, accessible observer, clock, causal metric, Hilbert H, gauge G, selected Wilson measure, OS Hamiltonian and KK action.
- [ ] **P00.L07** Preserve original author citations for history/TSVF, Planck–Heisenberg–Schrödinger/Stone, Yang–Mills/Wilson/Balaban/OS, rigorous 2D YM, stochastic 3D YMH and KK.
- [ ] **P00.L08** Create independent TEST and KERNEL receipts for numerical sizes 2/3/5 gauge convention, five-plane omitted-fibre counterexample and any physical limit calculations.
- [ ] **P00.L09** Add same-source proof exports to BalabanRGTOERegression / TOE graph only after complete actual head imports work.
- [ ] **P00.L10** Freeze precise failure/success states: SOURCE ≠ KERNEL ≠ PHYSICAL; external results remain source-scoped.

**Owners:** ClayYMProofRoadmap, CorePhysicsTheoremRoadmap, CompleteVerifiedPhysicsUnificationRoadmap, BalabanRGTOERegression, #1444 and #1460. **Status:** branch integration OPEN.

## P01 — reversible histories and observed arrow

**Deliverable:** physically selected microscopic history/refinement and observer filtration with operational arrow but no backwards signal. **Exit:** real source/continuum state, not just a three-state toy.

- [ ] **P01.L01** Construct actual microscopic histories, involution Theta and reversible source transition with compatible refinement maps.
- [ ] **P01.L02** Prove Theta²=id, microscopic action-invariance and reversal/refinement naturality.
- [ ] **P01.L03** Give physically admissible initial density rho and terminal positive effect E with consistent normalization and strictly positive selected partition.
- [ ] **P01.L04** Build class operators and decoherence functional D(alpha,beta)=tr(E C_alpha rho C_beta†) with positivity and decoherence hypotheses for probabilities.
- [ ] **P01.L05** Prove normalized selected history probabilities, conditional-state positivity and correct operator/state domains.
- [ ] **P01.L06** Build the actual observer record algebra and filtration inclusion; show conditional expectations are positive/unital and compose on the selected states.
- [ ] **P01.L07** Prove earlier accessible measurements are unchanged under admissible later boundary smoothing although latent inferred history changes; distinguish inference from intervention.
- [ ] **P01.L08** Derive an effective directional, noninvertible observer-quotient semigroup and its order from the source, without hard-coding a metric direction.
- [ ] **P01.L09** Prove micro reversal has no globally strict Nat-rank descent when a fixed history exists; preserve globalStrictReversalRankImpossible, and do not identify MDL with entropy.
- [ ] **P01.L10** Source-weld history, filtration, collapse and shift/MDL carriers or exhibit precise non-equivalence of these different dynamics.
- [ ] **P01.L11** Prove observer probability/refinement convergence (tightness or appropriate projective/infinite source construction) and normalized physical limit.
- [ ] **P01.L12** Construct one physically continuous clock from the actual selected observer process, with operational acyclicity and state identity preserved downstream.

### 2026-11-03 highest-alpha: original Admissible + original TSVF quantum ABL exact tensor payment

**User insight vindicated:** the original BidirectionallyAdmissibleHistoryFibreExact.agda already provides the shared initial/final history fibre; TwoBoundarySystem.agda already gives initial/final compatibility and junction legs; and DASHI/Quantum/TSVF.agda already provides forwardState/backwardState, transitionAmplitude, transitionWeight, ABLContext and ablProbability. These original owners were **reused**, not replaced. They now explicitly declare --safe after local no-postulate source inspection; **no Agda kernel / transitive trust-cut receipt has run**.

**Actual Golden source-written payment** (separate from the toy majority-code analogue): [TSVFAdmissibleQuantumOverlapRobustnessExact.agda](../../DASHI/Physics/Foundations/TSVFAdmissibleQuantumOverlapRobustnessExact.agda) imports both original owners; constructs AdmissibleTSVFQuantumSource and SourceMatchedABLMeasurement; proves original source ABL normalization conditionally from correct division laws, and proves a GENERAL k-fold tensor inner-product identity. Its concrete rational real-qubit environment vectors (5,0)/5 and (3,4)/5 have unit norm, inner product 3/5 and exact squared overlap (9/25)^k. The denominator-positive BinaryRationalMass proves P_R=25^k/(25^k+9^k), P_W=9^k/(25^k+9^k) and a wrong-tail cross-product bound; weightedBornMass proves gamma-weighted numerator normalization and exposes the opposite-result counterexample GammaR=1/GammaW=100 at k=2. A jointly admissible history may nonetheless have ZERO quantum weight—formally proved.

The further [TSVFConcreteAdmissibleQubitABLExact.agda](../../DASHI/Quantum/TSVFConcreteAdmissibleQubitABLExact.agda) **actually instantiates** original Q.QuantumSurface, Q.TSVFEnsemble, Q.ProjectiveMeasurement and Q.ABLContext on a two-outcome real/nonnegative coordinate quantum submodel with explicit idempotent projectors, initial ket (1,1), final bra (5^k,3^k) and positive total. finiteOriginalABLNormalization is a theorem about **the original Q.ablProbability output** for every k, not a newly postulated probability. selectedJointTSVFSource inhabits the original BidirectionallyAdmissibleHistoryFibre record with BOTH histories allowed under the same boundary pair. **Highest-value BIDI:** selectedABLMatchesActualTensorOverlap derives a cross-multiplied same-source identity from independently computed ABL Born masses and tensor Hilbert overlap. The finite model's scalar coordinates are not a complete complex physical Hilbert system.

**New P01.L15 complex gamma source payment:** TSVFComplexGammaProductBornExact.agda imports the original rational CayleyDickson complex owner, proves |product_j gamma_j|² = product_j |gamma_j|² for arbitrary complex amplitude lists, total Born invariance under componentwise conjugation and under insertion of the exact i phase. This is SOURCE-WRITTEN algebra, NOT a physical source for gamma_j or Eq.(25), not a real antiunitary physical time-reversal map, and not a physical bound uniform in allowed disturbances. The original complex owner now carries an unverified --safe header after local source inspection. **P01.L15 and P07.L15 are not closed physically.**

**Status recut, no ID renumbering, 186 unchanged:** P01.L13 (finite tensor source proof SOURCE; actual physical N/n environment OPEN), P01.L14 (finite selected original ABL positivity/normalization SOURCE; physical complete Born/ABL OPEN), P01.L15 (exact finite squared overlap/rate + conditional weighted gamma and adversarial no-go SOURCE; physical 2017 complex gamma/pointer source and uniform rate OPEN), P01.L16 (finite selected macro robustness SOURCE from prior module; physical real apparatus OPEN), P07.L15–16 (same-source *finite* quantum/observed-branch source available; real selected causal time and OS-reflected Hilbert still OPEN), P11 physical terminal OPEN. **No Clay R443/R445/R320/R333 source or literal (3,1) OS gap is paid by this finite work.**

[Full source/referee audit and exact external source interpretation](../physics/TSVFAdmissibleTensorOverlapABLMaxCut20261103.md). Local *equivalent* exact-Fraction Python run passed 51 k values, 960 unequal gamma cases, orthogonal admissible counterexample, zero wrong and adversarial k=10 tiny GammaR. The committed script has not itself been executed and exact-head Agda cannot yet be claimed accepted. **Physical next:** realize original 2017 Eq.(25) complex gamma_j and selected many-body environment on the same physically calibrated Hilbert/time/source, then P07 genuine unitary intertwiner H_clock ↔ H_OS.

### 2026-11-03 primary-source TSVF single-branch macro-reversibility max-cut

Original 2014/2017 Aharonov–Cohen–Gruss–Landsberger / Aharonov–Cohen–Landsberger papers explicitly allow conditional **single-branch macro record reconstruction despite failed fine micro-reconstruction**. It is NOT an Everett multiple-real-worlds theorem and NOT reversed thermodynamic entropy. See [source audit](../physics/TSVFMacroscopicReversibilityMultiverseBidiSourceAudit20261103.md). Existing multiverse TSFV/attractor classifiers distinguish physical realizations from a counterfactual parameter scan. The new Golden TSVFMacroscopicSingleBranchRobustnessExact finite selected pointer majority theorem is SOURCE-written and locally reference-tested, not kernel/physical quantum verified.

- [ ] **P01.L13** Construct an actual chosen pointer/environment quantum tensor-factor source with N redundant microscopic pointer records, selected physical decoherent alternatives and specified allowed disturbance class; no finite label-only witness.
- [ ] **P01.L14** Construct an actual nonzero postselected final bra/effect and normalized ABL/Born right/wrong branch probabilities on the *same* quantum Hilbert state, with zero-denominator/orthogonality cases isolated.
- [ ] **P01.L15** Prove the original 2017 quantitative robustness ratio from the actual N−n surviving environment overlap, branch gamma disturbance factors, positive normalization and all necessary assumptions; show R grows under a genuinely sourced overlap bound rather than N≫n alone.
- [ ] **P01.L16** Prove physical same-single-branch backward macro pointer reconstruction with explicit high-probability bound while fine micro recovery may fail; distinguish source quantum reversal from thermal entropy reversal.
- [ ] **P01.L17** Preserve and prove no controllable backwards signalling: later postselection/smoothing changes conditioned inference, not earlier recorded interventions; include actual selected measurement/Born source.
- [ ] **P01.L18** Source-classify **one selected TSVF branch**, Everett decoherent branches, counterfactual multiverse parameter points and genuinely physically realized universes as different physical claims, with existing TSFVMultiverseViabilityCrossPollinationExact nonpromotion and MultiverseAttractorDiscriminatorBidiExact hypothesis fibres.
- [ ] **P01.L19** Kernel-accept and source-pin new TSVFMacroscopicSingleBranchRobustnessExact: six one-flip triple-code macro restorations, a sharp two-flip failure witness, all fine-data-change proofs, no fine decoder, same original past with different hidden branch, microscopic reversal conjunction; **SOURCE written / physical interpretation not paid**.

**3 Nov heterogeneous quantum MAX-CUT, source-written not kernel checked:** [TSVF2017HeterogeneousEnvironmentABLExact](../../DASHI/Quantum/TSVF2017HeterogeneousEnvironmentABLExact.agda) extends P01.L13--L15 from one identical 3/5 environment to a list of DISTINCT rational-complex Hermitian record pairs: actual independent-site tensor amplitude, exact Born factorization of arbitrary complex gamma lists, specialization back to original all-k owner, positive selected ABL total, normalization on the ORIGINAL TSVF.ablProbability, and same two-admitted/one-excluded history projectors. [TSVF2017HeterogeneousRateExact](../../DASHI/Quantum/TSVF2017HeterogeneousRateExact.agda) proves an all-site 2^k exponential tail when every independent site has an ordered calibrated Born mass ratio >=2 and the global disturbance-weight order is independently justified. The original 25:9 case is a specialization. A local exact-rational Python equivalent passed 2,100 complex cases, 4,500 rate cases, 45 homogeneous sizes and two negative controls. Full [dossier](../physics/TSVF2017HeterogeneousEnvironmentOriginalABLMaxCut20261103.md). **OPEN unchanged:** actual unitary pointer/environment production and correlations; real final postselection, supplied complex gamma disturbance dynamics, same-source complex-to-Nat order calibration, physical P07 Stone/OS same generator and spectrum, and independent R443/R445/R320/R333/H6. No new IDs, 186 remain; no Agda kernel run. Earlier `DASHI.Quantum.Stone` has a finite one-point conditional Stone bundle and is not a physical noncollapsed Hilbert colimit, per `StoneTheoremCarrierReceipt` / `StoneSISecondTimeParameterBridge`: do not import unsafe or empty finite carriers as a physical clock.\n\n**P01.L13 finite pulse emission advance (SOURCE, not KERNEL):** [TSVF2017ControlledPointerRecordUnitaryExact](../../DASHI/Quantum/TSVF2017ControlledPointerRecordUnitaryExact.agda) consumes original rational-complex/TSVF owners and supplies actual linear four-complex-coordinate controlled pointer/environment rotation with a derived norm-preservation polynomial, certified 3/5--4/5 rational pulse, emitted environment records and full original-ABL normalization/factorization for a list of generated pulses. Equivalent independent exact-rational check passed 20,000 controlled norm cases; actual pulse produces |<right|wrong>|²=9/25. This pays **finite emitted-site semantics** beyond arbitrary site labels, while physical N-body interacting dynamics, correlation bounds, actual final postselection, disturbance law, noncollapsed Hilbert/Stone/OS and all R443--R333 gaps remain OPEN. No original lemma ID promoted to physical completion; exact-head Agda unavailable.\n\n**P01 correlated-branch MAX-CUT, SOURCE not KERNEL:** [TSVF2017CorrelatedEnvironmentMarginalNoGoExact.agda](../../DASHI/Quantum/TSVF2017CorrelatedEnvironmentMarginalNoGoExact.agda) constructs two nontrivial rational-complex Bell two-register states with exactly equal FULL one-register reduced-density matrices at both sites, equal norm square two and global overlap zero. It proves no decoder from the same pair of full local marginals can reconstruct both global states. This is an exact P01.L13/L15 negative theorem: actual product independence cannot be inferred from local marginal record equality; a physically sourced cluster/error bound must replace the false implication. Re-exported in the Golden regression root; no Agda kernel receipt. The identical copy can have distinct global phase/correlation data. Exact reference Bell calculations executed on local Python with fractions. **Physical final-state dynamics and P07 Hamiltonian remain OPEN.**\n\n**Owners:** FiniteHistoryOrientationExact, HistoryWeightFiltrationExact, TSFVFiltrationArrowLorentzBridgeExact, TSVF/TSFVFeynman sources; original Aharonov–Bergmann–Lebowitz and Aharonov–Vaidman. **Status:** finite OWNED / physical continuum OPEN.

## P02 — independently derived physical (3,1) cone, metric and orientation

**Deliverable:** nondegenerate 4D causal manifold, three stable transverse spatial modes, exactly one clock and selected metric principal symbol. **Exit:** signature not assumed and physically calibrated.

- [ ] **P02.L01** Define operational causal order from interventions and accessible records; prove transitivity/locality/no backwards signalling.
- [ ] **P02.L02** Construct locally finite causal refinement/continuum maps preserving and reflecting order.
- [ ] **P02.L03** Construct interval counting N(I(p,q)), calibrated physical volumes and independent causal dimension estimator under refinement.
- [ ] **P02.L04** Prove dimensional scaling N(I)~C_D tau^D selects D=4 **from source**, not from storing the number four in an input record.
- [ ] **P02.L05** Prove continuum is an appropriate Hausdorff smooth four-manifold with enough differentiability for physical metric/propagation operators.
- [ ] **P02.L06** Construct finite-speed causal cone field and prove actual operational signal bounds.
- [ ] **P02.L07** Construct positive spatial quadratic h with rank exactly three on a physical stable transverse subspace.
- [ ] **P02.L08** Construct nonzero clock covector theta, one-dimensional clock complement and theta annihilation on spatial modes.
- [ ] **P02.L09** Prove Q(v)=h(v_perp,v_perp)-c²theta(v)² is the **physical propagation principal symbol**, not a hand-selected diagonal signature fixture.
- [ ] **P02.L10** Prove Q nondegenerate and has one timelike and three spacelike directions; its null cone equals the independently derived operational cone, with proper metric scale.
- [ ] **P02.L11** Select a global future half-cone from P01 filtration; prove time orientability and compatibility with physical Cauchy evolution.
- [ ] **P02.L12** Prove hyperbolic well-posedness and energy positivity for the actual physical operator, including calibration of c.
- [ ] **P02.L13** Show IntrinsicSignatureCoreAxioms, contraction and cone/isotropy axioms have actual source inhabitants rather than being supplied as assumptions.
- [ ] **P02.L14** Reconcile LargePosetContinuumLorentz31, Signature31Canonical, Signature31FromIntrinsicShellForcing, CausalForcesLorentz31 and finite orbit B4 witnesses on the same event/metric source.
- [ ] **P02.L15** Prove uniqueness among physically admissible signatures up to justified convention/physical equivalence, rejecting (2,2) or extra-time cases if hypotheses support it.
- [ ] **P02.L16** Preserve geometry negative control: H³×R+ product metric does not automatically identify with Poincaré warped H⁴; demand actual geometry transport.

**Owners:** Signature31Canonical, Signature31FromIntrinsicShellForcing, LargePosetContinuumLorentz31, CausalForcesLorentz31, LorentzEmergenceFromCausalAxioms, YMCarrierSpatialGeometryCheckReceipt. **Status:** conditional signature calculus OWNED, physical D=4/source metric OPEN.

## P03 — selected complex Hilbert structure, CCR, Planck/Heisenberg/Schrödinger

**Deliverable:** same physical clock on a positive Hilbert space with actual strongly continuous unitary one-parameter evolution. **Exit:** no invented unbounded canonical operators.

- [ ] **P03.L01** Derive conserved nondegenerate real symplectic omega from the same source fluctuation/action quotient.
- [ ] **P03.L02** Derive positive compatible real form h_q and a complete physical Hilbert quotient; establish symplectic Hilbert compatibility.
- [ ] **P03.L03** Construct A=h_q⁻¹ omega with correct operator domains and positive -A² for polar square root.
- [ ] **P03.L04** Prove selected J=A(-A²)^(-1/2) exists, J²=-1, is compatible with phase dynamics and gives the physical quantum imaginary unit, not another spacetime axis.
- [ ] **P03.L05** Prove the compatible Hermitian product is positive, conjugate symmetric, complete and admits correctly normalized Born states.
- [ ] **P03.L06** Reuse original finite C3/Heisenberg/Weyl operators, central cocycle and finite representation laws without treating finite qutrit matrices as unbounded CCR.
- [ ] **P03.L07** Prove isometric finite-to-Hilbert embeddings and operator convergence on a common dense invariant core.
- [ ] **P03.L08** Prove limiting Weyl relations and self-adjoint X,P with [X,P]=i*hbar on that core; establish correct nonzero central normalization.
- [ ] **P03.L09** Prove selected clock transfer is a strongly continuous unitary one-parameter group on **the same** H; no arbitrary reparametrisation of time.
- [ ] **P03.L10** Apply/source-verify Stone theorem and self-adjoint energy-bounded-below H_clock; prove generator domains and spectral measure.
- [ ] **P03.L11** Prove Schrödinger equation i*hbar dpsi/dt=H_clock psi and norm preservation on the actual differentiable core.
- [ ] **P03.L12** Prove quantum antiunitary time reversal and operational arrow are compatible; source dynamics may be reversible while filtering is not.
- [ ] **P03.L13** Derive Heisenberg uncertainty and Planck E=hbar omega on the same states/operators, including real metrological hbar units.
- [ ] **P03.L14** Reconcile CCRFromAdmissibleFlow, TreeHeisenbergScalingLimit, SchrodingerQuotientDescentReceipt, SchrodingerSelfAdjointEvolutionReceipt and Quantum.Stone as one actual Hilbert source.

**Owners:** FiniteTreeWeyl, CCRFromAdmissibleFlow (requires ProjectionWeylAxioms), TreeHeisenbergScalingLimit (requires domain/limiting proofs), SchrodingerSelfAdjointEvolutionReceipt (explicitly an OPEN obligation surface), PlanckHbarSIPayloadRequest. **Status:** finite algebra OWNED; continuum source, J, CCR/Stone OPEN.

## P04 — local quantum-frame symmetry to physical gauge theory and SM boundaries

**Deliverable:** independent actual U(1) and selected compact simple G non-Abelian gauge source. **Exit:** pure YM target is separate from matter/KK/gravity.

- [ ] **P04.L01** Construct local physical observable net on P02 geometry/P03 quantum Hilbert, with causal locality and positive state.
- [ ] **P04.L02** Prove local U(1) phase-frame transformation action on a real physical bundle, not only an analogy.
- [ ] **P04.L03** Construct U(1) connection, covariant derivative, Maxwell curvature, action and charged-current conservation.
- [ ] **P04.L04** Construct an actual selected compact simple G=SU(N) physical bundle/representation with local non-Abelian connection, curvature F and Wilson holonomy.
- [ ] **P04.L05** Prove selected non-Abelian gauge transformation/covariance, curvature and Wilson trace invariance, including action/source normalization.
- [ ] **P04.L06** Prove gauge action compatible with the selected H_clock and physical local observable algebra; distinguish photon, color and purely geometric phase.
- [ ] **P04.L07** Construct a rigorous decoupled **pure G** gauge sector to which Clay applies; do not use coupled Einstein–YM or SM matter as a substitute.
- [ ] **P04.L08** If full SM asserted: construct SU(2)_L, correct global SU3×SU2×U1 quotient, chiral fermion reps, charges and physical mass/CKM/PMNS sources.
- [ ] **P04.L09** If full SM asserted: prove local/global gauge anomalies and spin/global bundle compatibility, including actual E6/KK quotient if invoked.
- [ ] **P04.L10** If physical QCD asserted: prove correct beta coefficients/running, Lambda_QCD calibration, threshold/scheme matching from physical measured authority; carrier scale alone is insufficient.
- [ ] **P04.L11** Preserve negative controls: massless QED photon is not pure non-Abelian YM mass gap, and a finite ternary count does not derive real SU(3) color.
- [ ] **P04.L12** Provide direct physical U(1)/G charge and gauge observational consumers, and source-to-source comparison with existing Standard Model owners.

**Owners:** SU(N) gauge/Wilson owners, StandardModelGaugeCouplingAuthorityFrontier, QCDRunningFromCarrierScaleReceipt, #1241 KK/E6 quotient. **Status:** classical/finite conditional; full physical SM OPEN and optional for Clay.

## P05 — R443 finite variable-periodic compact SU(N) Wilson/Haar source

**Deliverable:** genuine physical one-link Haar, native bond codec, normalized Wilson–Gibbs measure and selected R124/CMP119 metric density at every cutoff. **Exit:** actual finite physical measure, not merely a parameterized Haar interface.

- [ ] **P05.L01** Construct compact matrix SU(N) over actual physical complex/real backend: determinant-one, adjoint inverse, group operations, compactness.
- [ ] **P05.L02** Prove selected real normalized ReTr/N, adjoint/inverse and cyclic trace with Bishop/legacy real transport, no unjustified equality.
- [ ] **P05.L03** Construct arbitrary-side original 4-torus **positive-link enumeration**, prove 4*side^4 bonds, all six positive plaquettes/site, signed inverse path laws.
- [ ] **P05.L04** Construct positive-bond function/Vec/setoid decoder and encoder with pointwise roundtrips, count/order and no unrestricted function extensionality.
- [ ] **P05.L05** Prove decoder gauge naturality, selected pointwise observable congruence and translation/C3 covariance.
- [ ] **P05.L06** Prove exact original signed Wilson six-plane action agrees with canonical generic SUNWilsonAction and original plaquette winding source.
- [ ] **P05.L07** Prove genuine compact normalized Borel SU(N) **one-link Haar**, positivity, integrability and bilateral invariance on selected test algebra.
- [ ] **P05.L08** Derive actual native finite product Haar/Fubini and gauge-invariant change-of-variables via one-link Haar and native decoder.
- [ ] **P05.L09** Inhabit #1444 YMClaySUNVariablePeriodicProductHaarExact using the **actual** P05.L07 oneLink and P05.L04 bond vector.
- [ ] **P05.L10** Inhabit #1444 YMClaySUNVariablePeriodicGaugeHaarExact using the **actual** bilateral Haar and OriginalPeriodicGaugeVectorNaturality.
- [ ] **P05.L11** Construct selected physical exp(-S) density, strict partition positivity and normalized gauge-invariant Gibbs/Wilson expectations, including physical real scalars.
- [ ] **P05.L12** Prove all finite integration/measure laws on the actual physical test algebra, with correct division/normalization.
- [ ] **P05.L13** Inhabit selected **CMP119/R124 E/R/B/V density**, metric source variation, counterterms and the literal beta; retain selected source identity.
- [ ] **P05.L14** Prove same-object R443 finite Wilson source equals R124/CMP119 selected density/gauge observable and R445 marked cylinder; not labels alone.
- [ ] **P05.L15** Provide physical cutoff/coupling/SI units and actual finite-positive-time reflection algebra for P06.
- [ ] **P05.L16** Execute deterministic sides 2,3,4,5 gauge regression plus deliberately wrong inverse-gauge orientation and lost-link negative controls, separately from kernel proof.

**3 Nov downstream #1444 R443/P05 selected integration:** Added native cyclic↔Fin inverse theorem, finite original bond Vec reindexing/composition/inverse, original native C3 vector/canonical-label single-permutation certificate bridge, and the actual conditional SU(N) C3 setoid Haar source copied SHA-identically from #1444 head `5e81c4f5bd5041fc7fa6259b915a6f2ce0c42261`. The selected one-vector C3 implication is SOURCE; the required concrete `LinkPermutation 1024` *program* and its single canonical Vec equality are **OPEN R443.F07**, as are compact Haar and CMP119. The old C3/Wilson imports are not transitive `--safe` certified, so only genuinely safe finite donors re-export in the Golden root. The complete [219-field inventory](YMClaySubmission219FieldInventory20261103.json) and exact [R443/R445/R320/R333 ledger](YMClayCurrentExactLemmaLedger20261103.md) are pinned copies of #1444, NOT evidence 219 lemmas were proved.\n\n**Owners:** latest #1444 YMClaySUNVariablePeriodicProductHaarExact, YMClaySUNVariablePeriodicGaugeHaarExact, YMClaySUNConstructedPeriodicGaugeCodecExact, YMClaySUNVariablePeriodicBondPointwiseExact, YMClayNativeSixPlaquetteSUNWilsonActionWeldExact, selected CMP119 and original Wilson/Haar. **Status:** actual native all-n positive-bond/Vec codec and finite gauge naturality SOURCE-WRITTEN from #1444 and now source-synced into #1460; **kernel acceptance OPEN**, and **actual compact continuous one-link Haar, selected real CMP119/R124, changing-cutoff continuum estimates OPEN**. No second arbitrary decoder axiom should be charged.

## P06 — actual 4D Euclidean Yang–Mills continuum and mass-gap analytic core (R445/R320/R333)

**Deliverable:** one genuinely physical 4D pure compact-simple-G gauge quantum theory, changing-cutoff continuum, reflection-positive OS reconstruction, strictly positive spectral gap and H6 nontriviality. **Exit:** every literal Clay source requirement is proved; fixed-lattice positivity does not suffice.

- [ ] **P06.L01** Construct directed native physical Wilson cylinder family at all scales and finite volumes, including valid observable restriction/refinement maps.
- [ ] **P06.L02** Prove actual chosen cutoff compatibility or quantified blocking/RG residuals; do not falsely equate unequal finite lattice measures.
- [ ] **P06.L03** Inhabit selected Bałaban *one-step* RG physical source bounds with true constants, analytic norms and gauge/matrix content.
- [ ] **P06.L04** Prove multiscale RG induction uniformly in regulator and volume from those true one-step estimates; no conditional one-step axiom.
- [ ] **P06.L05** Prove physical R445 uniform marked-source moments, regularity and scaling with constants independent of cutoff.
- [ ] **P06.L06** Prove R445 uniform tails/large-field control, tightness and nontrivial quantum state candidates on the actual physical measure.
- [ ] **P06.L07** Construct continuum gauge-invariant Schwinger expectation distributions as cutoff→0 with correct metric/counterterm and observable meaning.
- [ ] **P06.L08** Prove infinite-volume construction (volume→∞), valid ordering/diagonal limit, vacuum normalization and independence of approximation choice.
- [ ] **P06.L09** Prove full required Euclidean rotations/translations, symmetry and clustering where used; finite C3 invariance alone is insufficient.
- [ ] **P06.L10** Prove OS reflection positivity for selected real physical measure/cylinder algebra, preserved through continuum and infinite-volume limits.
- [ ] **P06.L11** Prove remaining necessary OS axioms, distributional/temperedness regularity and correct gauge-invariant reconstruction hypotheses on that state.
- [ ] **P06.L12** Build actual OS Hilbert quotient, vacuum, positive semigroup and self-adjoint **H_OS** from exactly those limit Schwinger functions.
- [ ] **P06.L13** Identify literal selected CMP116 **mixed-J differentiated-source** expectation, source differentiation and rooted-shell coordinates on exactly the R445 family.
- [ ] **P06.L14** Prove selected R320 uniform rooted-shell decay in cutoff, volume, sources and shell distances with physically controlled constants.
- [ ] **P06.L15** Derive Route-S R320→R333 spectral consequence for **the identical H_OS** and gauge-invariant spectrum, including validity of all analytic limit interchanges.
- [ ] **P06.L16** Prove a physical energy-unit Δ>0 independent of cutoff/volume with spec(H_OS) ⊆ {0}∪[Δ,∞), preserving actual ground-state/vacuum identification.
- [ ] **P06.L17** Prove H6 nontriviality: interacting limit theory with nonzero gauge-invariant observables/Hilbert content; rule out a trivial Hilbert/empty operator trick.
- [ ] **P06.L18** Prove all literal Clay scope: four-dimensional R^4 (not only periodic T^4), every required compact simple group or precisely scoped G, continuum axiom status and nontrivial quantum theory.
- [ ] **P06.L19** Discharge transitive Bishop/constructive-real and external analytic assumptions and quantify regularity, source group, cutoff and volume hypotheses explicitly.
- [ ] **P06.L20** Publish exact-head source/lemma/constant/dependency/referee receipts, and compare genuinely same physical OS Hamiltonian with independent proof methods.

**3 Nov R445/P06 original SU(2) blocked-link payment:** [YMClayNativeBlockedSU2PathHolonomyGaugeExact](../../DASHI/Physics/YangMills/YMClayNativeBlockedSU2PathHolonomyGaugeExact.agda) composes the exact #1444 `M*L` native blocked site/bond codec, original signed L-step path holonomy, and ORIGINAL rational unit-quaternion SU(2) group/cyclic successor-predecessor/oriented covariance theorem. It constructs an actual group-valued blocked link from the native fine bond field and proves the transformed blocked link equals `g_start * link * inv(g_walked_end)` at the correctly reblocked endpoint; L=1 is the original positive bond. This is SOURCE-WRITTEN (old dependencies not transitive safe), **not** a supplied `GaugeEquivariant` record. Independent Q8⊂SU(2) exact reference passed 11,784 bond cases including noncommuting negative control. Distinct P06.L02 leaves: independent equality to chosen coarse neighbour, gauge/plaquette/Wilson action refinement, actual reflection-compatible Gibbs pushforward, normalized Haar disintegration, R445 scale-uniform moments/decay/continuum. Full [dossier](../physics/YMClayNativeBlockedSU2TSVFBellMaxCut20261103.md). **R320/R333/H6 and pure 4D Clay remain OPEN.**\n\n**Additional closed-loop source theorem for P06.L02:** the same original rational SU(2) native blocked module now has endpoint-indexed composable blocked walks and an all-length gauge-covariance induction, followed by a *constructed* real quaternion Wilson trace, proved cyclic and invariant under closed-loop conjugation from the existing group laws. The arbitrary class-function premise is eliminated for this actual rational SU(2) example; 11,784 exact Q8 closed-loop reference cases passed. The coarse-neighbour equality, physical Wilson plaquette/cylinder action, normalized Haar/Gibbs disintegration and UV/IR analytic gates remain OPEN. **Source-written, not Agda accepted; old dependencies not Golden safe.**\n\n**Owners:** #1440 Route-S, #1444 R443–R445, BalabanClayGate4CombinedRGUVIterationExact and BalabanClayConcreteUVToMassGapDependencyExact; original Bałaban, Wilson, Osterwalder–Schrader. **Status:** significant finite and conditional sources OWNED/SOURCE; actual P06 source/limits/Δ OPEN. **This is the independent standalone Clay finish.**

## P07 — central unification theorem: observed clock = actual OS Hamiltonian/metric

**Deliverable:** a source-selected physically meaningful unitary equivalence of the same observed time and OS reconstruction, same metric/gauge observables and spectrum. **Exit:** no equality based only on two independent signature-(3,1) labels.

- [ ] **P07.L01** Select independent P01/P02/P03 clock, accessible-record state and causal metric before importing the target OS continuation.
- [ ] **P07.L02** Construct Euclidean involution/reflection theta from **that exact clock/physical source** with correct positive-time observable sector.
- [ ] **P07.L03** Prove P06 physical Wilson/Schwinger OS reflection is the same theta on selected observables, not a second invented reflection.
- [ ] **P07.L04** Prove physical Lorentzian metric/causal cone from P02 agrees with OS reconstructed geometry under actual continuation and scale/units.
- [ ] **P07.L05** Construct a unitary surjective isometry U: H_clock → H_OS with actual domains, null quotients, chosen state/vacuum and observable algebra compatibility.
- [ ] **P07.L06** Prove U U_clock(t) = U_OS(t) U for every real t, with correct source time normalization and domain continuity.
- [ ] **P07.L07** Derive U H_clock = H_OS U and spectral-projection intertwinement on the self-adjoint generator domains; transport one physical Δ.
- [ ] **P07.L08** Prove equality of selected time-correlations and Wilson/gauge-invariant observables at *matched couplings/boundaries* under the chosen U.
- [ ] **P07.L09** Construct actual physical inhabitants of SameMetricTSFVKK: arrowSource, kkSource, physicalStateOfMetric, same metric/operational orientation—not just its conditional proof term.
- [ ] **P07.L10** Prove Lorentzian/Euclidean stress/Wightman continuation refers to the same physical state when used; do not equate formal Hodge-star signatures with OS.
- [ ] **P07.L11** Prove uniqueness of selected OS analytic continuation in the relevant class, and a negative-control scenario with mismatched clock/metric or failed reflection positivity.
- [ ] **P07.L12** Prove full central commuting square with canonical sector-indexed observable keys, including independent physical interpretation of both forward and backward maps.
- [ ] **P07.L13** Verify *typed* classical finite Hodge (*²=-1 Lorentz two-forms, *²=+1 Euclidean two-forms) as convention check, not substitute for actual U.
- [ ] **P07.L14** Prove genuine same-physical-source identification with the P08 reduced KK 4-metric, if claiming the full five-sector theorem.

### Same-source macro robustness → OS-clock interaction (not a theorem from macro coding alone)

- [ ] **P07.L15** Identify the physical selected macro pointer/observer of P01.L13–16 with P07's actual Hilbert, clock and metric; separately construct/compare the time-reversal antiunitary, conditional backward quantum state and Euclidean OS reflection (three different operations).
- [ ] **P07.L16** Prove conditional single-branch macro robustness does not introduce a second timelike direction, does not invert observed filtration and preserves **the same physical OS gauge-invariant observables** under the explicitly allowed source reversal/comparison; otherwise return a quantified mismatch/counterexample.

**Owners:** TSFVKKSameMetricTransportExact, TSFVFiltrationArrowLorentzBridgeExact, YMClayLorentz31DirectionalKKHodgeExact, OS reconstruction owners and SchrodingerSelfAdjointEvolutionReceipt. **Status:** conditional same-metric SOURCE, actual U/generator equivalence OPEN. **Highest-value cross-domain lemma: P07.L05–L07.**

## P08 — spacelike fifth-circle KK effective theory and Möbius/internal holonomy

**Deliverable:** one actual Lorentzian five-dimensional EFT with correctly reduced 4D metric/action, radion, graviphoton, gauge scalar, thresholds and pure-YM decoupling. **Exit:** low-energy 4D physics matches P07 in stated sectors.

- [ ] **P08.L01** Select an actual spacelike circle principal bundle S¹ over P02 physical time-orientable 3+1 base with correct global spin/orientation.
- [ ] **P08.L02** Derive source-selected Lorentzian 5D metric ansatz and unique declared Jordan/Einstein-frame normalization, preserving one timelike axis.
- [ ] **P08.L03** Construct 5D Einstein–YM–matter **effective** action with boundary, cutoff, physical couplings, group action and counterterms, not a claimed 5D UV completion.
- [ ] **P08.L04** Compute full scalar/vector/gravity curvature action reduction including radion, graviphoton and non-vanishing cross/boundary terms.
- [ ] **P08.L05** Decompose gauge A_A = (A_mu,Phi=A_y) on the same bundle and prove F_AB reductions into 4D YM curvature, covariant scalar derivative and scalar interactions.
- [ ] **P08.L06** Prove 5D and 4D gauge transformations, source variation/stress and field equations commute with zero-mode reduction when admissible.
- [ ] **P08.L07** Prove tree-level g4²=g5²/ell and kappa4^-2=ell*kappa5^-2 only under stated unwarped/constant-circle conventions, with units.
- [ ] **P08.L08** Derive orthonormal KK modes and untwisted flat-circle m_n²=m_0²+(2πn/ell)², identifying the spectrum in the actual effective field source.
- [ ] **P08.L09** Prove physical low-energy KK truncation or integrate out massive modes with explicit E*ell-dependent Wilson/metric/stress bounds and threshold terms.
- [ ] **P08.L10** Prove stabilization or justified decoupling of radion/adjoint scalar/graviphoton, or retain their full physical observable contributions.
- [ ] **P08.L11** Construct and prove controlled *pure 4D YM* decoupling limit of the gravity/matter/KK theory, matching P06 chosen Wilson/Schwinger source.
- [ ] **P08.L12** Prove the same KK-reduced metric/time/observable algebra as P07, with controlled EFT epsilon, not merely equal signature counts.
- [ ] **P08.L13** If claiming E6/trinification, prove actual global group, chirality, nonliftable quotient bundles, anomalies, CS/WZ/eta/spin regulator and gravity-consistent source on the same field theory.
- [ ] **P08.L14** If claiming Möbius/internal twist, construct genuine associated bundle and Z₂ monodromy, one-loop flip and two-loop return with source-compatible boundary fields.
- [ ] **P08.L15** Prove internal Möbius twist leaves physical base global time orientable or supplies lawful orientable double-cover descent without contradictory operational clocks.
- [ ] **P08.L16** Preserve strict **5D Euclidean lattice ≠ Lorentzian KK ≠ stochastic auxiliary time ≠ complex i** type distinction; require typed maps to compare any two.
- [ ] **P08.L17** Transport #1460 finite ten-plane (five-axis) action/omitted-fibre no-go into the physical 5D curvature source with actual nonnegative norm and retained scalar cross-fibre terms.

**Owners:** #1241 KKSteelmanBidirectionalConsumerExact/E6 global quotient, #1460 YMClayLorentz31DirectionalKKHodgeExact/YMClayFiveSectorBidiSteelmanExact, MobiusOrientationGate (target-only). **Status:** physical 5D action/weld OPEN, finite geometry SOURCE.

## P09 — rigorous selected lower-dimensional backward checks: 4→3→2

**Deliverable:** controlled reductions and *independent* observables corresponding to the actual 2D known YM theorem and precisely scoped local 3D stochastic YM–Higgs construction. **Exit:** comparison with correct scalar/gauge/limit/coupling scope.

- [ ] **P09.L01** Construct a selected compactification and observable reduction R_(d→d-1) at d=4,3 (and 5 as P08) with selected boundary and source conditions.
- [ ] **P09.L02** Derive physical decomposition of F_d into F_(d-1), covariant adjoint-scalar Phi and scalar interactions with all gauge transformation laws.
- [ ] **P09.L03** Prove tree-level coupling g_(d-1)²=g_d²/ell plus correct loop thresholds and physical scheme/scale matching.
- [ ] **P09.L04** Prove selected Wilson-loop holonomy/cylinder source naturality under actual dimensional reduction for loops retained in the base.
- [ ] **P09.L05** Prove 4D→3D gauge+scalar low-energy effective measure/observable agreement with a quantified mode/truncation residual.
- [ ] **P09.L06** Match the *actual locally renormalized* 3D stochastic YM–Higgs gauge-covariant dynamics and mass-renormalization counterterms in the published local scope; do not infer global stationary distribution.
- [ ] **P09.L07** Prove 3D→2D gauge+scalar reduction and valid scalar decoupling to standalone pure 2D YM if claiming that comparator.
- [ ] **P09.L08** Reproduce rigorously the normalized planar simple-loop 2D Wilson expectation exp[-(g2²*C2(R)/2)*Area], in the proper representation/topological scope.
- [ ] **P09.L09** Prove correspondence of the selected 2D Euclidean/Hamiltonian Wilson observable to the external rigorous construction, not only formula resemblance.
- [ ] **P09.L10** Establish quantitative finite-circle/finite-cutoff error and legitimate order of limits for every lower-D comparison.
- [ ] **P09.L11** Retain extra d→d-1 adjoint scalar mode and gauge polarizations; mere numerical polarization accounting cannot replace field/action comparison.
- [ ] **P09.L12** Construct negative controls: wrong loop topology/representation, wrong scalar truncation, wrong coupling, noncommuting limits and invalid gauge state.
- [ ] **P09.L13** Inhabit each adjacent MatchedEuclideanGaugeTower physical observation equality before claiming automatic 5→2 transitive agreement.

**Original external owners:** Ashtekar–Lewandowski–Marolf–Mourão–Thiemann rigorous 2D YM and Chandra–Chevyrev–Hairer–Shen / Chevyrev–Shen stochastic 3D YM–Higgs results; their actual scope controls the bridge. **Status:** published 2D and scoped 3D EXTERNAL; physical DASHI same-sector maps OPEN.

## P10 — same-effective-action stress/GR and exotic-gravity consumers

**Deliverable:** physical metric-dependent effective action, conserved source stress, one positive-G metric and independent multi-channel predictions. **Exit:** source-native physics, not exotic-label promotion.

- [ ] **P10.L01** Construct selected renormalized W[g,A,Psi;B_±] on P07 physical state, including actual metric-dependent counterterms and global boundary conditions.
- [ ] **P10.L02** Prove source metric variation exists and yields T_mu nu=-(2/sqrt(-g))*δW/δg^mu nu with the declared convention and actual tensor domain.
- [ ] **P10.L03** Prove covariant Ward identity/nabla^mu T_mu nu=0 with gauge/matter anomalies, conservation and boundary flux accounted for.
- [ ] **P10.L04** Identify physical R124/CMP119 native metric/stress first variation and all ten independent symmetric stress readouts with the same selected Wilson measure.
- [ ] **P10.L05** Prove Einstein equation with the *same* P07 metric, actual normalized G_N>0 and selected QFT stress, not an independently assumed gravitational state.
- [ ] **P10.L06** Inhabit #1120 Local-C/Wightman source-first P1 Q1 (one-path first variation + reflection) and A2 (source-native stress cylinder identity).
- [ ] **P10.L07** Inhabit #1120 P2 same cosmological renormalization convention, stress×length²/apparatus physical scale, native metric perturbation and controls.
- [ ] **P10.L08** If history/birthmark gravity claimed, prove actual history-sensitive W source and Eq.(2.23) N_V>0, N_ERB≥0 signs, not entropy-memory⇒curvature.
- [ ] **P10.L09** Prove physically allowed defocusing/repulsive geometry from relevant active stress and energy constraints; negative trace alone is insufficient and scalar Kottler shift is not TT wave.
- [ ] **P10.L10** Prove one selected source→stress→metric produces coherent weight/support, geodesic free fall, clock and optical channel predictions.
- [ ] **P10.L11** Close ordinary momentum, electromagnetic, thermal and mechanical nuisance channels, match controls and replicate before observational anomaly promotion.
- [ ] **P10.L12** Preserve material-effective negative G versus universal sign-flipped G and their differing positive-density weak-field fingerprints; no universal negative-G inference.
- [ ] **P10.L13** Prove evidence promotion firewall: an antigravity report, GW signal, history label or stress fixture does not solve Clay YM or imply TOE.
- [ ] **P10.L14** Verify physical same-stress/same-metric continuation through P07 OS and P08 KK when asserted, with actual normalization, or produce discrepancy/error.

**Owners:** #1120 Local-C/Wightman and four-channel, #1132 birthmark Eq.(2.23), #1045 negative-G strongest conditional theorem, #1284 nonpromotion, #1050 source D1, #1241 KK metric/stress. **Status:** many conditional/local fixtures, physical source OPEN.

## P11 — global BIDI, exact-head Golden receipts and final proof

**Deliverable:** one fully inhabited Emergent31YangMillsKKPhysicalClosure theorem (or smallest surviving blocker certificates). **Exit:** all mandatory phases checked, with no hidden circular assumption.

- [ ] **P11.L01** Define canonical physical comparison key (selected source, state, gauge group, coupling, regulator, boundary, observable, limit) for every claimed equality.
- [ ] **P11.L02** Construct physically source-first forward construction from microscopic history → operational causal (3,1) → J/H/Stone → gauge → Wilson → OS.
- [ ] **P11.L03** Construct independent backward steelman from rigorous 2D + scoped 3D sources, independent constructive 4D YM/OS and observed 3+1 physical tests, without importing the desired source identity.
- [ ] **P11.L04** Prove Os(4D Euclidean)→3+1 is a reconstruction and 5D KK→4D is a reduction; stochastic flow auxiliary time and Euclidean five-axis YM are different typed sources.
- [ ] **P11.L05** Prove all selected Wilson/state/hilbert/spectral/time/metric same-observable commuting squares; otherwise retain explicit approximation epsilon or no-go.
- [ ] **P11.L06** Give explicit error bounds ε_O(a,L,ell,mu) for every effective comparison and exact-zero proofs only for genuinely identical sectors.
- [ ] **P11.L07** Prove spectral projection equivalence and Δ>0 on the one physical H clock/H_OS and pure G state, not a different gapped theory.
- [ ] **P11.L08** Prove stress and geometry are the same physical source across Lorentz, Euclidean OS and KK whenever a stress comparison is asserted.
- [ ] **P11.L09** Establish justified limit ordering and permitted interchanges (cutoff→0, volume→∞, KK-radius→0, stochastic time→∞, history-refinement, OS).
- [ ] **P11.L10** Pass independent selected 2D/3D observables and at least one 5D→4D coupling/action same-source comparison at known, defined scales.
- [ ] **P11.L11** Run negative controls: wrong Lorentz clock/signature, wrong Haar inverse orientation, failed OS positivity, mismatched KK scalar, curved geometry mismatch, fake finite gap and universal negative-G fingerprint.
- [ ] **P11.L12** Establish SI metrology, original publication authority, actual global gauge group, measured-coupling and empirical distinctions.
- [ ] **P11.L13** Kernel-check final source graph under Golden Agda safe/zero-postulate/zero-meta/zero-termination-bypass and provide complete exact source HEAD/stdlib logs.
- [ ] **P11.L14** If Lean mirror used, audit exact corresponding theorem and actual source content separately; no automatic Agda↔Lean proof transfer.
- [ ] **P11.L15** Produce distinct standalone Clay YM theorem/receipt and stronger 3+1/KK/GR unification theorem; optional SM and exotic experimental claims remain optional.
- [ ] **P11.L16** Independent mathematics referee audit: domains, genuine source inequalities, nontriviality, volume, spectral theory and all source preconditions; preserve failed no-go.
- [ ] **P11.L17** Independent physical falsification and instrumentation audit for measured causal dimension, lower-D observables, KK thresholds and four-channel gravity if claimed.
- [ ] **P11.L18** Prove terminal theorem only after all actually required physical fields are inhabited; else publish exact smallest unsatisfied primitive-leaf cut.

### Multiverse ontology / TSVF interpretation independent BIDI

- [ ] **P11.L19** Complete a source-matched, observable-indexed discriminator among (i) TSVF selected-single-branch, (ii) Everett/decoherent-histories observer-selection, (iii) unique-law/dynamical-attractor and (iv) actual physically realized multiverse; prove a prediction/experimental comparison or **document underdetermination**. Never promote a viable parameter or branch count into real cosmological multiplicity, (3,1) or an OS/YM gap.

**Owners:** BalabanRGTOERegression and TOE imports plus all owners above. **Status:** OPEN.

## 3. Phase acceptance matrix and deliverables

| Phase | Exact lemma count | Deliverable | Required acceptance receipt | Current status |
|---|---:|---|---|---|
| P00: source + integration | 10 | one actual multi-PR proof import graph | pinned SHAs, newest #1444 available to #1460, exact-head safe compile, transitive assumption inventory | PARTIAL SOURCE SYNC; full merge/referee OPEN |
| P01: histories and arrow | 19 | selected physical continuum observer with non-backwards-signalling arrow | source-native state/refinement/probabilities and filtration proof | finite OWNED; physical OPEN |
| P02: 3+1 causal geometry | 16 | independently derived dimension four, rank-three space and one clock | source dimension estimator, metric principal symbol, cone and time orientation | COND/OPEN |
| P03: Hilbert/quantum | 14 | symplectic-to-J complex structure and genuine Stone/CCR/Schrödinger evolution | positive completion, unbounded operator convergence, domains, hbar SI | finite OWNED; physical OPEN |
| P04: physical gauge | 12 | source-native U(1)/compact simple G, separate pure YM sector | local group/gauge bundle/connection; SM authority extra only if claimed | COND/OPEN |
| P05: R443 finite YM | 16 | actual compact SU(N) native product Haar and finite physical Wilson Gibbs | one-link Haar, function↔Vec decoder, selected R124/CMP119 density | #1444 SOURCE; physical OPEN |
| P06: R445/R320/R333 | 20 | nontrivial infinite-volume 4D pure Yang–Mills with Δ>0 | actual uniform UV/tail/mixed-J/OS/gap source, full Clay scope | OPEN |
| P07: same-clock OS | 16 | physically selected H_clock ≃ H_OS and same metric/observables | unitary/spectral/domain and reflection-positivity correspondence | SOURCE/COND; physical OPEN |
| P08: 5D KK | 17 | selected spacelike-circle EFT → same 4D geometry/gauge + scalar/radion | action reduction, couplings, decoupling, thresholds, holonomy | COND/OPEN |
| P09: lower-dimensional BIDI | 13 | correct 2D and scoped 3D known-physics observable comparison | real scalar-aware reduction and quantitative errors | external sources available, maps OPEN |
| P10: gravity | 14 | one physical stress source and one positive-G metric | Ward/conservation, real W variation, independent four-channel predictions | conditional owners, source OPEN |
| P11: finish | 19 | full physically inhabited theorem and independent referee | every matched-observable commuting square, negative tests, exact-head acceptance | OPEN |
| **Total** | **186** | **finite scoped theorem-dependent inventory** | added analytic sublemmas must be tracked as discovered | **not completed** |

### Priority and parallel worker allocation

**Track A — Lorentz/TSFV (P01+P02+P07):** prove source-selected causal dimension, unique operational clock and physically constructed metric. The selected source is the same object P07 transports to OS. First hard no-go to look for: the operational arrow and chosen causal cone may not select the same time orientation.

**Track B — quantum/SM source (P03+P04):** derive compatible complex J, positive Hilbert completion and actual Stone time generator; keep genuine pure YM source separate from full SM. First hard no-go: finite Weyl representations do not automatically converge to the claimed unbounded CCR, and a finite C3 carrier does not certify SU(3) color.

**Track C — finite Yang–Mills (P00+P05):** reconcile latest #1444 onto the chosen #1460 source and pay physical one-link compact Haar, native positive-bond vector decoder and R124/CMP119 first variation. First hard no-go: the actual selected one-link source/test algebra may not satisfy the conditional product-Haar proof owners' assumptions.

**Track D — 4D analytic/Clay (P06):** prove literal changing-cutoff R445 physical moment/tail estimates and CMP116 R320 differentiated-source decay, then same-H OS spectral inequality R333 and H6 nontriviality in the correct full mathematical scope. This track is the central independently valid Clay research programme even if the spacetime conjecture fails.

**Track E — higher/lower dimensions (P08+P09):** source-first 5D KK/4D gravity/gauge+scalar reduction with EFT errors and actual lower-dimensional 3D/2D observables. First hard no-go: nontrivial cross-fibre curvature or light radion/adjoint scalar invalidates a claimed pure YM truncation.

**Track F — common gravity/BIDI (P10+P11):** source-native real effective variation, four-channel gravitational comparator and all-sector same-observable commuting squares; independently test wrong-orientation, wrong-Hamiltonian, wrong-gauge and wrong-KK cases before promoting anything.

### Mandatory negative controls

1. Wrong number of timelike directions, wrong causal volume dimension or imposed diagonal signature must **not** certify an emergent (3,1) theorem.
2. Microscopic history reversal fixed point prevents strict global reversal-rank descent; an observer-filter arrow is a different object.
3. Negative gauge-covariance fixture with the wrong inverse gauge orientation must fail at every selected lattice side.
4. Missing fifth-axis curvature weight must fail exact 5→4 action equality unless the cross-fibre remainder vanishes; the #1460 finite one-plane fixture proves a genuine no-go in its Nat-valued scope.
5. A formally positive finite-volume mass gap that decreases to zero as volume grows must fail P06/P07.
6. Any OS Hilbert state/Hamiltonian different from the observed one must fail P07, even if both carry a positive spectral gap.
7. A 2D pure-YM area law comparison with an unremoved adjoint scalar must fail P09.
8. A Möbius orientation flip of **physical time** without justified double cover must fail P02/P08.
9. A negative trace, unverified history-sign coefficient or anomalous force without same-source metric response must fail P10.
10. A terminal theorem assembled from uninhabited records, original postulates, CI assumptions or numeric tests without real physical source proof must fail P11.

## 4. Definition of completed: four different claims

- **Finite formal tranche completed:** named finite theorems have exact-head KERNEL receipts; all assumptions/physical limitations remain explicit. Not a Clay, spacetime or KK completion.
- **Standalone Clay Yang–Mills completed:** P05+P06 all physical/analytic statements inhabited for literal Clay compact simple G, 4D continuum and infinite volume, nontrivial OS Hilbert and Δ>0. The speculative history/KK hypothesis may be false without invalidating a genuinely independent proof.
- **Emergent (3,1) quantum construction completed:** P01+P02+P03 true selected physical source and causal metric, plus P07 clock side where it is independent. If P06/P07 same-OS is not proved, do not claim the full YM/OS join.
- **Full five-sector proposed steelman completed:** all mandatory P00–P11 physical sources/limit maps, matched observable equalities and theorem terminals inhabited, exact-head Golden Agda accepted and independent mathematical/physical checks passed. Full Standard Model/E6 and experimental exotic gravity are additional separate subclaims only when explicitly asserted.

### Per-lemma closure receipt (all fields required)

| Field | Required evidence |
|---|---|
| Lemma ID | canonical Pxx.Lyy, original source module and new proof module if different |
| Proposition | fully quantified theorem type including actual group, manifold, regulator, boundary, measure, source and limits |
| Proof body | safe proof term; if analytic source is external, exact attribution/scope and in-repo same-object import theorem |
| Authority | source SHA, upstream PR/commit, original scientific theorem author, imports and no-postulate cone |
| Verification | compiler version, exact-head run result, 0 metas/unsafe bypass; independent finite reference tests as appropriate |
| Physical identity | selected original object and actual non-circular population of all conditional inputs |
| Comparison | matched observable, bounded epsilon or explicit falsifier, plus gauge/coupling/units/limit normalization |
| Residual | exact smallest unproved analytic/empirical source, if any; never silently mark it paid |

**Claim ledger accounting:** a checked source-written *conditional* lemma becomes KERNEL but remains COND until its physical hypothesis has a genuine inhabitant. A physical source lemma without executed exact-head safe checking is not KERNEL. A proof about a *finite* model is not a continuum physical theorem. Experimental tests do not replace mathematical proof; mathematical proof does not replace experimental verification for a claimed phenomenon.

## 5. Direct original-owner crosswalk

| Critical target | Existing theorem owner / donor | New exact transport obligation |
|---|---|---|
| Finite reversible history | FiniteHistoryOrientationExact, HistoryWeightFiltrationExact | P01 selected source and continuum |
| Filter → operational arrow | TSFVFiltrationArrowLorentzBridgeExact | P01.07–12 physical source |
| Intrinsic causal 3+1 | Signature31Canonical, Signature31FromIntrinsicShellForcing, CausalForcesLorentz31, LargePosetContinuumLorentz31 | P02 actual metric/continuum |
| Finite Weyl/CCR | FiniteTreeWeyl, CCRFromAdmissibleFlow, TreeHeisenbergScalingLimit | P03 complex J, domains and limit |
| Schrödinger/Stone | SchrodingerSelfAdjointEvolutionReceipt, SchrodingerQuotientDescentReceipt, Quantum.Stone | P03 real self-adjoint H_clock |
| U(1)/SU(N) | native gauge/Wilson owners, StandardModelGaugeCouplingAuthorityFrontier, QCDRunningFromCarrierScaleReceipt | P04 physical gauge representation |
| R443 finite Haar | #1444 YMClaySUNVariablePeriodicProductHaarExact / YMClaySUNVariablePeriodicGaugeHaarExact | P00 integration + P05 real Haar/decoder |
| CMP119/R124 | CMP119 source metric/E/R/B/V density owners, native SU(N) Gibbs | P05.13/14, P10.04 physical source |
| R445 UV | R445 native same-family, original Balaban RG and combined UV module | P06 true cutoff-uniform analytic source |
| R320 differentiated mixed-J | CMP116 and #1440 Route-S | P06.13/14 true source decay |
| R333/H6 OS | #1440 + #1444 reconstruction/gap consumers | P06.15–20 same-H gap |
| Same-clock and metric | TSFVKKSameMetricTransportExact, YMClayLorentz31DirectionalKKHodgeExact | P07 physical unitary and metric |
| KK/E6 | #1241 KKSteelmanBidirectionalConsumerExact, #1460 YMClayFiveSectorBidiSteelmanExact | P08 actual EFT and scalar accounting |
| Möbius orientation | MobiusOrientationGate (candidate-only) | P08.14/15 internal bundle |
| 2D/3D published comparators | rigorous 2D YM; local stochastic 3D YMH, original authors | P09 actual matching maps |
| Exotic GR/stress | #1120/#1132/#1045/#1284, CMP119 Local-C/Wightman | P10 one real W/stress/metric |
| TOE | BalabanRGTOERegression and existing TOE import graph | P11 only after actual physical close |

## 6. Source priority and status reporting protocol

**Reuse → unify duplicate source constructions → extend selected physical source → build a new carrier only if no existing owner can supply it.** Search exact terms and nearby original owners before coding; preserve original attribution.

After each update, report **exact lemma IDs, old versus new minimal dependency cut, source file + full commit SHA, actual Agda kernel status, physical population status, independent negative control and remaining smallest analytic/source premise**. "All gates closed" must never describe a numerical regression or a collection of conditional input records.

**Next concrete work:** finish the full newest #1444/#1460 integration beyond the six source-copied files, compile the focused Golden roots; in parallel begin (A) P02 real causal volume/signature source, (B) P03 Hilbert/Stone physical clock and (C) P05 genuine compact SU(N) one-link Haar/native decoder. Then concentrate P06 actual R445/CMP116/R333 analytic estimates and P07 same-H theorem. Do not postpone source falsification until the end.


## Appendix A — complete live status of all 186 exact lemma IDs

**Accounting date: 4 November 2026 · #1460 child lane.** This appendix is deliberately a second *status and provenance index*, **not 186 additional lemmas**; the verbatim exact lemma statements occur once above. Source status is a provenance judgement based on the current in-repo surfaces and does **not** imply Agda kernel acceptance. **All 186 remain PHYSICAL-OPEN and KERNEL-UNVERIFIED at this audited exact head**. In particular these statuses must not override current verification receipts from the separate #1444 YM worker: P05/P06 are delegated and not independently reaudited here. Conditional statement labels are never marked as genuinely inhabited physical witnesses.

**Legend:** `SOURCE partial` = existing finite/conditional/no-go code covers part of that obligation; `Physical proof OPEN` = no completed physical proof in this #1460 audit; `Delegated` = another worker owns the independent YM proof. Every line requires a real selected object, exact source binding, physical domains/limits, and an actual Golden proof receipt before it can become `CLOSED`.

| Exact ID | Owner | Source/kernel/physical state |
|---|---|---|
| `P00.L01` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P00.L02` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P00.L03` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P00.L04` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P00.L05` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P00.L06` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P00.L07` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P00.L08` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P00.L09` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P00.L10` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P01.L01` | #1460 | SOURCE partial — original finite reversible histories; continuum source absent · **kernel unverified / physical open** |
| `P01.L02` | #1460 | SOURCE partial — finite reversal/action involution; refinement naturality absent · **kernel unverified / physical open** |
| `P01.L03` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P01.L04` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P01.L05` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P01.L06` | #1460 | SOURCE partial — actual source filtration and lossy observer quotient; physical conditional expectations absent · **kernel unverified / physical open** |
| `P01.L07` | #1460 | SOURCE partial — original hidden-state/visible record weld; physical non-signalling absent · **kernel unverified / physical open** |
| `P01.L08` | #1460 | SOURCE partial — finite observer access order; physical evolution semigroup absent · **kernel unverified / physical open** |
| `P01.L09` | #1460 | SOURCE partial — global strict reversal rank no-go; physical thermodynamics separate · **kernel unverified / physical open** |
| `P01.L10` | #1460 | SOURCE partial — filtration/shift nonpromotion; physical source weld absent · **kernel unverified / physical open** |
| `P01.L11` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P01.L12` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P01.L13` | #1460 | SOURCE partial — finite controlled emitter/heterogeneous records; actual many-body correlations absent · **kernel unverified / physical open** |
| `P01.L14` | #1460 | SOURCE partial — original selected finite ABL normalization; physical postselection absent · **kernel unverified / physical open** |
| `P01.L15` | #1460 | SOURCE partial — complex gamma/Born and bounded correlation-error source; physical uniform error absent · **kernel unverified / physical open** |
| `P01.L16` | #1460 | SOURCE partial — finite macro branch robustness; real apparatus absent · **kernel unverified / physical open** |
| `P01.L17` | #1460 | SOURCE partial — finite no-backwards-signalling semantics; physical intervention control absent · **kernel unverified / physical open** |
| `P01.L18` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P01.L19` | #1460 | SOURCE partial — finite macro source written; kernel receipt absent · **kernel unverified / physical open** |
| `P02.L01` | #1460 | SOURCE partial — three-level partial order and original diamond edge transport; physical interventions absent · **kernel unverified / physical open** |
| `P02.L02` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P02.L03` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P02.L04` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P02.L05` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P02.L06` | #1460 | SOURCE partial — original finite causal diamond; real signal bound absent · **kernel unverified / physical open** |
| `P02.L07` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P02.L08` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P02.L09` | #1460 | SOURCE partial — conditional source quadratic calibration; actual principal symbol absent · **kernel unverified / physical open** |
| `P02.L10` | #1460 | SOURCE partial — conditional 3+1 signature; actual null-cone equality absent · **kernel unverified / physical open** |
| `P02.L11` | #1460 | SOURCE partial — conditional exact same KK/TSVF selected arrow; physical source absent · **kernel unverified / physical open** |
| `P02.L12` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P02.L13` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P02.L14` | #1460 | SOURCE partial — existing finite/intrinsic signature models; same physical model absent · **kernel unverified / physical open** |
| `P02.L15` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P02.L16` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P03.L01` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P03.L02` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P03.L03` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P03.L04` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P03.L05` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P03.L06` | #1460 | SOURCE partial — finite Weyl/Stone owners; limiting CCR absent · **kernel unverified / physical open** |
| `P03.L07` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P03.L08` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P03.L09` | #1460 | SOURCE partial — conditional original real-time group/derivative source; actual Hilbert absent · **kernel unverified / physical open** |
| `P03.L10` | #1460 | SOURCE partial — conditional generator-to-OS equality; physical Stone/self-adjointness absent · **kernel unverified / physical open** |
| `P03.L11` | #1460 | SOURCE partial — i-hbar energy matching conditional; differentiable Hilbert domain absent · **kernel unverified / physical open** |
| `P03.L12` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P03.L13` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P03.L14` | #1460 | SOURCE partial — finite Stone/colimit receipts; physical completion explicitly blocked · **kernel unverified / physical open** |
| `P04.L01` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P04.L02` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P04.L03` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P04.L04` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P04.L05` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P04.L06` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P04.L07` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P04.L08` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P04.L09` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P04.L10` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P04.L11` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P04.L12` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P05.L01` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P05.L02` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P05.L03` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P05.L04` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P05.L05` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P05.L06` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P05.L07` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P05.L08` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P05.L09` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P05.L10` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P05.L11` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P05.L12` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P05.L13` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P05.L14` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P05.L15` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P05.L16` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P06.L01` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P06.L02` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P06.L03` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P06.L04` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P06.L05` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P06.L06` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P06.L07` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P06.L08` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P06.L09` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P06.L10` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P06.L11` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P06.L12` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P06.L13` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P06.L14` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P06.L15` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P06.L16` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P06.L17` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P06.L18` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P06.L19` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P06.L20` | YM #1444 | Delegated; parent receipt required · **kernel unverified / physical open** |
| `P07.L01` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P07.L02` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P07.L03` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P07.L04` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P07.L05` | #1460 | SOURCE partial — original observer-to-OS embedding is an input, not onto Hilbert isometry · **kernel unverified / physical open** |
| `P07.L06` | #1460 | SOURCE partial — real-time group intertwiner is a conditional input, not physically sourced · **kernel unverified / physical open** |
| `P07.L07` | #1460 | SOURCE partial — derived strong difference quotient and i-hbar energy equality conditional on physical Hilbert/H · **kernel unverified / physical open** |
| `P07.L08` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P07.L09` | #1460 | SOURCE partial — SameMetricTSFVKK + selected bilinear weld conditional; inhabitant absent · **kernel unverified / physical open** |
| `P07.L10` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P07.L11` | #1460 | SOURCE partial — Euclidean-vs-real-time no-go written; OS continuation uniqueness absent · **kernel unverified / physical open** |
| `P07.L12` | #1460 | SOURCE partial — finite commutations/source-specific no-go; full physical square absent · **kernel unverified / physical open** |
| `P07.L13` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P07.L14` | #1460 | SOURCE partial — KK horizontal and same-bilinear theorem conditional on actual metric · **kernel unverified / physical open** |
| `P07.L15` | #1460 | SOURCE partial — original forward ket on selected conditional domain; macro physical state absent · **kernel unverified / physical open** |
| `P07.L16` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P08.L01` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P08.L02` | #1460 | SOURCE partial — exact rational KK horizontal ansatz and invertible shear; physical 5D source absent · **kernel unverified / physical open** |
| `P08.L03` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P08.L04` | #1460 | SOURCE partial — exact horizontal bilinear reduction; full curvature/action reduction absent · **kernel unverified / physical open** |
| `P08.L05` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P08.L06` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P08.L07` | #1460 | SOURCE partial — tree-level coupling arithmetic present; physical units/loops absent · **kernel unverified / physical open** |
| `P08.L08` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P08.L09` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P08.L10` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P08.L11` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P08.L12` | #1460 | SOURCE partial — conditional same-observer-bilinear/KK horizontal metric; solution absent · **kernel unverified / physical open** |
| `P08.L13` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P08.L14` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P08.L15` | #1460 | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P08.L16` | #1460 | SOURCE partial — typed Euclidean-vs-Lorentzian separation negative controls · **kernel unverified / physical open** |
| `P08.L17` | #1460 | SOURCE partial — finite omitted-fibre curvature no-go; physical 5D curvature absent · **kernel unverified / physical open** |
| `P09.L01` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P09.L02` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P09.L03` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P09.L04` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P09.L05` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P09.L06` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P09.L07` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P09.L08` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P09.L09` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P09.L10` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P09.L11` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P09.L12` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P09.L13` | Shared | SOURCE partial — matched finite 5→2 composition conditional; physical adjacent matches absent · **kernel unverified / physical open** |
| `P10.L01` | #1460 (conditional) | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P10.L02` | #1460 (conditional) | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P10.L03` | #1460 (conditional) | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P10.L04` | #1460 (conditional) | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P10.L05` | #1460 (conditional) | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P10.L06` | #1460 (conditional) | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P10.L07` | #1460 (conditional) | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P10.L08` | #1460 (conditional) | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P10.L09` | #1460 (conditional) | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P10.L10` | #1460 (conditional) | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P10.L11` | #1460 (conditional) | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P10.L12` | #1460 (conditional) | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P10.L13` | #1460 (conditional) | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P10.L14` | #1460 (conditional) | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P11.L01` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P11.L02` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P11.L03` | Shared | SOURCE partial — forward/backward steelman audit source-written; physical reverse reconstructions absent · **kernel unverified / physical open** |
| `P11.L04` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P11.L05` | Shared | SOURCE partial — conditional commuting squares/negative controls; physical source alignment absent · **kernel unverified / physical open** |
| `P11.L06` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P11.L07` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P11.L08` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P11.L09` | Shared | SOURCE partial — limit-order requirements documented; no analytic interchange proofs · **kernel unverified / physical open** |
| `P11.L10` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P11.L11` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P11.L12` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P11.L13` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P11.L14` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P11.L15` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P11.L16` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P11.L17` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |
| `P11.L18` | Shared | SOURCE partial — smallest source-family cut S01–S11 documented; terminal physical theorem absent · **kernel unverified / physical open** |
| `P11.L19` | Shared | Physical proof OPEN; no complete verified source · **kernel unverified / physical open** |

### Non-exhaustive primitive-source leaf map, ordered by Pareto/alpha

| Leaf | Critical physical source not yet constructed | Relevant canonical IDs |
|---|---|---|
| S01 | Real micro/observer state and decoherent pointer record | P01.L01–L07,L13–L17 |
| S02 | Spatially resolving causal interventions, retarded response and signal cone | P01.L08–L12; P02.L01,L06 |
| S03 | Independent 4D continuum dimension/volume/scale proof | P02.L02–L05,L13–L15 |
| S04 | Real physical hyperbolic principal symbol, null cone, time orientation | P02.L07–L12 |
| S05 | Five-dimensional smooth bundle/action/metric/radion/Einstein–matter solution | P08.L01–L06,L10; P10.L01–L05 |
| S06 | Same selected observer-measured 4-metric = actual KK reduction | P07.L09,L14; P08.L07–L12 |
| S07 | Genuine physical 4D YM Schwinger/OS self-adjoint H | P06.L07–L18 (YM worker) |
| S08 | Completed noncollapsed observer Hilbert, Stone and SI-time | P03.L01–L14 |
| S09 | Unitary onto J, common dense H domain, spectrum/observables/Wick | P07.L05–L08,L10–L16 |
| S10 | Cutoff/volume/KK radius/history limit matching and errors | P00.L06; P11.L01–L10 |
| S11 | Exact-head Agda, trust and independent BIDI/referee receipts | P00.L04,L08–L10; P11.L11–L18 |

**Pareto/alpha next:** pay S01→S02 first with *source-specific* observable spatial discrimination and independent retarded response, rather than another signature mask; in parallel pay an actual physical H/OS operator representation S08–S09 (not just abstract time-indexed maps), and P08 S05→S06 physical lift/source fields. Add a native BIDI non-injectivity theorem for the **original** KK horizontal reduction: different fifth-sector connections may have the identical reduced four-metric, so the reverse 4D→5D lift cannot be justified without independent fibre observables. This appendix is not a claim all future analytic lemmas are already known.

**Closure threshold:** source-written only ≠ Agda kernel-accepted ≠ physically inhabited; no checkmark can be set by a Python fixture or a conditional source record. P05/P06 are not re-implemented here.
