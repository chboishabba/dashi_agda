# Yang–Mills: canonical current exact-lemma ledger
**Snapshot:** 3 November 2026, YM [PR #1444](https://github.com/chboishabba/dashi_agda/pull/1444), stacked on Route-S #1440. PR #1460 is downstream TSVF/Lorentz/KK work, **not** a Clay YM proof premise.

**Proof-status rule:** `SOURCE` means source-written Agda terms with GitHub readback, **NOT** typechecked, unless a pinned exact-head Agda transcript is separately attached. `CONDITIONAL` means a compiler/theorem requires an unconstructed selected physical producer. `OPEN` is a literal theorem-bearing leaf, not a missing name. `TRUST` is source or kernel/axiom acceptance debt. No item below is labelled kernel accepted. Do not decrement a frozen physical family from a finite calculation or a conditional compiler.

## A. The three inventories are distinct — no false equivalence

1. **Clay endpoint:** `DASHI/Physics/YangMills/YangMillsClayProblemContractExact.agda` defines `ClayYangMillsSolution`: 8 preconditions, 9 postconditions, 11 invariants, requiring a nontrivial four-dimensional quantum Yang–Mills theory on R⁴ and strictly positive physical gap with the stated gauge-group scope. **NO witness produced.**
2. **Submission inventory:** `YangMillsSubmissionExactCutset.agda` + `YangMillsSubmissionObligationCardinalityExact.agda`: `58+56+13+10+13+20+21=191` theorem-spine obligations (Gate4, local Step V, RG transfer, fixed-lattice gap, thermodynamic limit, continuum limit, OS endpoint); plus `15+13=28` foundation/gauge-structural obligations; **219 total**. These are record fields/inventory counts; do not claim 219 proved.
3. **Frozen research-cut A–D:** `BalabanClayHighestAlphaRound87FourAnalyticLemmaExact.agda` and `BalabanClayFrozenFourCompletionContractExact.agda`: A positive/tuned same-history beta, B selected differentiated marked-J/locality/stress-shell energy, C same-density gap/Heat–Doob or competing source-native physical route, D OPE/AF/stress same quantum family. **All four physical rows remain open.** The R443/R445/R320/R333/P5 rows below are **producer gates**, not substitutes for the Clay endpoint, 219 fields, or four physical completions.

## B. R443: original finite Wilson/Gibbs + compact SU(N) Haar

| Exact ID | Source owner / statement | Current state | Remaining literal proof |
|---|---|---|---|
| R443.F01 | `YMClayNativePositiveBondEnumerationVectorExact.originalPositiveBondCountFormula` — original \(4L^4\) bond count and side-four 1024 | SOURCE | Exact-head Agda kernel acceptance |
| R443.F02 | `originalBondsDecodeEncodeAt`, `originalBondsEncodeDecodeExactly` — original field/Vec correspondence | SOURCE | Exact-head Agda kernel acceptance |
| R443.F03 | `YMClayNativeFiniteGaugeVectorNaturalitySafeExact.encodeGaugeNatural`; SUN constructed physical adapter | SOURCE / CONDITIONAL | Kernel check; identify actual SU(N) gauge group against selected matrix carrier |
| R443.F04 | `YMClayNativeSideFourC3VectorWeldExact`: existing C3 site/axis action, inverse, cube, original native Vec compatibility | SOURCE | Kernel check, finite adjacent-swap program |
| R443.F05 | `YMClaySUNConstructedNativeC3SetoidHaarExact.originalNativeC3SetoidCodec`: real SU(N) Gibbs setoid encoding and original C3 witness reduction | SOURCE / CONDITIONAL | One `LinkPermutation 1024` program matching canonical native C3; one-link Haar for physical application |
| R443.F06 | `YMClayNativeC3SingleVectorPermutationCertificateExact.singleVectorC3ImpliesAllVectors` | SOURCE | No universal vector certificate as a primitive: derive from **one** program equality on `canonicalLabelVector` |
| R443.F07 | Concrete adjacent-swap program and `permuteLinks program canonicalLabelVector ≡ C3.forwardVector canonicalLabelVector` | OPEN | Build `program` and prove/decide its **single 1024-label vector equality**; the existing F06 theorem transports to all Link vectors |
| R443.P01 | True compact continuous SU(2)/SU(N) matrix group and real/Bishop/legacy scalar identification, with full chosen observable class | OPEN / LEAN DONOR | Bring actual selected group + matrix + trace to Golden Agda; Lean PR #15 has real SU(2) finite-Haar donor but not an accepted same-object Agda import |
| R443.P02 | Normalized compact Haar on a defensible measurable/integrable one-link test algebra | OPEN | Construct (not assume) integration and normalization with correct domain; existing `OneLinkProductHaar` is a **total-function interface**, not the measure construction |
| R443.P03 | Selected one-link measurable Haar/Fubini + product integration, positivity/full support and Wilson Gibbs normalization | CONDITIONAL | Match `CompactLieAnalyticPackage.NormalizedHaarTheory.Integrable` to the original finite SU(N) Gibbs/cylinder functions; avoid all-functions-vs-measurable conflation |
| R443.P04 | Original selected CMP119 R124 E/R/B/V nonlinear metric insertion, boundaries and counterterms | OPEN | Same literal physical action/density/evaluator and printed-source constants, not a gauge-invariant surrogate |
| R443.P05 | Original six-plane/ordered-plane trace/adjoint C3 and real-action correspondence | SOURCE / CONDITIONAL | Kernel-accept selected original matrix/trace representation and all-source correspondence |

## C. R445: actual changing lattice, physical refinement and continuum

| Exact ID | Source owner / statement | Current state | Remaining literal proof |
|---|---|---|---|
| R445.F01 | `YMClaySUNVariablePhysicalCutoffFamilyExact` — original \((n+1)^4\) changing site lattice, \(4(n+1)^4\) links, β(n), same conditional finite Gibbs/Haar source | SOURCE / CONDITIONAL | True Haar and coupling, physical scaling; varying β at fixed side four **does not** count |
| R445.F02 | `YMClayNativeCyclicFinIsoSafeExact` two exact roundtrips | SOURCE | Agda acceptance |
| R445.F03 | `YMClayNativeBlockedPeriodicBondWeldExact` same-original \(M L\) four-torus site/bond ↔ Bałaban blocked coordinates, both inverse laws | SOURCE | Kernel acceptance; this is **label geometry**, not a blocked gauge field |
| R445.P01 | Original group-valued coarse link as ordered fine-path holonomy | OPEN | Construct on original positive bonds; reuse `BalabanClayGate4PeriodicBondPathBianchiExact.pathHolonomy` with concrete block-edge directions |
| R445.P02 | Gauge-equivariant blocked-link/plaquette map, same Wilson action | OPEN | Reuse `pathSiteGaugeCancellation`; match coarse endpoints and show selected Wilson/cylinder naturality |
| R445.P03 | Reflection-halfspace/OS-compatible block and Wilson measure | OPEN / CONDITIONAL | Same physical reflection + `BalabanReflectionPositiveCoarseGrainingTransportExact`; mere positive weights do not imply RP |
| R445.P04 | Actual Gibbs pushforward, normalized disintegration/reopening kernel | OPEN | Same continuous SU(N) measure, source beta, fine/coarse expectation; reuse `BalabanFiniteRGObservableReopeningExact` only after its actual hypotheses |
| R445.P05 | Spacing \(a_n\), physical volume, beta(a), renormalized scale map | OPEN | Tune same generated RG history; no arbitrary Nat index masquerading as a continuum lattice |
| R445.P06 | Uniform source moments, tails, coercivity/tightness, surface/volume constants | OPEN | Physical estimates independent of spacing and relevant infinite-volume cutoff |
| R445.P07 | Cylinder/projective compatibility, gauge/OS observables, source-consistent continuum extraction | OPEN | Physical measures and source spectra, not only type-level limit fields |
| R445.P08 | Thermodynamic and continuum existence/uniqueness and selected O(4) covariance | OPEN | Precisely the 13 thermodynamic and 20 continuum field obligations in the full submission inventory |
| R445.P09 | Same-limit nontriviality and fourth-cumulant or appropriate non-Gaussian witness | OPEN / CONDITIONAL | Source nonvanishing estimate in the completed physical limit, not just the generic `FourthCumulantWitness` record |

## D. R320: selected physical CMP116 mixed-J decay

| Exact ID | Current state | Literal remaining payment |
|---|---|---|
| R320.P01 | OPEN | Differentiate the **same physical** selected logarithmic partition \(\partial_{J_1}\partial_{J_2}\log Z\), not an unrelated real covariance |
| R320.P02 | OPEN | Construct common marked-source analytic radii, complete local J domain and actual source differentiability |
| R320.P03 | SOURCE / CONDITIONAL | Existing P06 support/DFS/rooted shells/entropy combinatorics reusable; kernel and literal marked-source bridge still necessary |
| R320.P04 | OPEN | Selected CMP116 uniform-in-cutoff/volume rooted-shell exponential envelope and quantitative constants |
| R320.P05 | OPEN | Physical mixed-J connected clustering/decay from that envelope on the exact original Gibbs measure |
| R320.P06 | OPEN | Match decay transfer to the **same** OS reconstruction and physical time/space scaling; no separate covariance family |

## E. R333: same OS Hamiltonian and mass gap

| Exact ID | Current state | Literal remaining payment |
|---|---|---|
| R333.P01 | CONDITIONAL | Original selected Wilson finite-lattice reflection positivity and complete CMP119 E/R/B/V action; match published Osterwalder–Seiler / Menotti–Pelissetto theorem hypotheses on same gauge carrier |
| R333.P02 | OPEN | Original blocked physical reflection positivity through the actual R445 maps and limiting full reflected Gram forms |
| R333.P03 | CONDITIONAL | Use one OS null quotient, Hilbert completion, vacuum, semigroup and positive selfadjoint Hamiltonian; Kato/generic OS compilers are not selected physical producers |
| R333.P04 | OPEN | Same-Hamiltonian identification: Wilson transfer, reconstructed time translation, action variation/domain/core and physical scale |
| R333.P05 | OPEN | Construct cutoff/volume uniform **strict positive** gap, in physical units, for this exact OS Hamiltonian |
| R333.P06 | OPEN | Prove gap survives both thermodynamic and UV limits (not merely fixed lattice/β clustering) |
| R333.P07 | OPEN | Vacuum uniqueness, locality/spectrum conditions, full Wightman/OS endpoint and nontrivial physical excitation |

## F. Final Clay / trust gates

| Exact ID | Status | Final obligation |
|---|---|---|
| CLAY.P01 | OPEN | Selected nontrivial 4D quantum YM with gauge-invariant local operators and accepted axiomatic QFT framework |
| CLAY.P02 | OPEN | Physical O(4)/Poincaré covariance, locality, regularity and same-family short-distance/OPE/AF |
| CLAY.P03 | OPEN | The prescribed compact simple gauge-group scope, positive physical mass gap and literal `ClayYangMillsSolution` witness |
| TRUST.K01 | OPEN | Exact PR-head Agda typecheck of all new finite sources and TOE root; zero holes, no unsafe escape |
| TRUST.K02 | OPEN | Transitive postulate/source authority audit. `DASHI/Foundations/RealAnalysisAxioms.agda` explicitly postulates the real carrier and laws. `BalabanClayFrozenFourCompletionContractExact.agda` carries `--safe` while importing that authority. Local `--safe` syntax ≠ accepted trusted proof |
| TRUST.K03 | OPEN | Independent compiler clean-room receipt, exact theorem names, revisions, dependency graph, author/source provenance and manuscript correspondence |

## G. Programmatic checks and stable owners

- Sources are under `DASHI/Physics/YangMills/`, with the new native owners re-exported by `DASHI/Unified/BalabanRGTOERegression.agda`. The repo is authoritative; Lean donor results must be same-object mapped into Agda before counting as Golden closure.
- Finite references: `scripts/check_ym_native_periodic_bond_vec_codec.py`, `scripts/check_ym_original_c3_bond_vector_reference.py`, `scripts/check_ym_original_blocked_bond_reference.py`. C3 integer orbit fixture at side 4 has 16 fixed labels and 336 disjoint 3-cycles (1024 positive bonds). These are **reference** results, not compiler/kernel acceptance.
- Source trust scanner: `scripts/check_ym_golden_agda_trust_cut.py`; static/source read only.
- Preferred same-source terminal cut still uses `BalabanClayCurrentTerminalCutsetRound191Exact` and the old Eq.119/Kato/T5 producer owners. The 219-item submission inventory remains the full A–I *field* inventory; the 4-row analytic cut remains a *research compression*. Neither is decremented by the finite R443/R445 work.
- Highest-alpha order: **F07** one 1024-label adjacent-swap certificate → R443.P01–P05 genuinely physical Haar/measurability and selected action → R445.P01–P08 original blocked gauge/path/refinement and physical limits → R320.P01–P06 selected CMP116 mixed-J decay → R333.P01–P07 same OS Hamiltonian physical gap → Clay contract. Parallel work on physical Haar and R445 path blocking is permissible; they do not imply R320/R333 automatically.
- The other worker's TSVF selected-branch macroscopic record and proposed same-clock compatibility live downstream in PR #1460; no identification with OS reflection positivity/time semigroup is established. Avoid reverse import into #1444.
