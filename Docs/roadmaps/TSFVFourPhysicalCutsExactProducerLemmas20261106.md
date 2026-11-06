# #1460 — four physical maximum cuts: exact producer lemmas (6 November 2026)

**Authority:** These 40 named *proposed producer theorems* are NOT additional canonical P lemma IDs and are NOT new Agda proof receipts. They are a focused concrete implementation/dependency contract for the existing 186 original P00–P11 statements and 48 execution deliverables. The original Yang–Mills OS producer and CMP116/PCUBE proof remain solely in #1444.

**Physical acceptance rule:** Each theorem must construct from the SAME original microscopic TSVF/observer state, physical instrument, observable algebra, clock and action; a record asserting its conclusion is not an inhabitant. Selected acoustic lattice, flat KK and free Fock examples serve as independent positive/negative controls, not the selected original physical source.

**Dependency schedule:** OBS01–OBS06 + HIL01–HIL05 in parallel from the actual micro source; OBS07–OBS09 to physically measure (3,1); KK01–KK08 from that observed g4; HIL06–HIL11 only after #1444 supplies its real OS construction; BIDI01–BIDI08 close the measured commuting limits, kernel, falsification.

## 6 November 2026 — source-implemented finite OBS05 precursor and fresh YM dependency

- **New child owner:** `DASHI.Physics.Foundations.TSVFOriginalInterventionRetardedPrefixExact` uses the original `QuantumSurface.evolveKet`, `QuantumSurface.apply`, and `TSVFEnsemble` initial/middle/final time fields. It constructs the actual selected prefix ket, an after-prefix intervention and later evolved readout. `originalNoLaterChoiceRewritesEarlierRecord` is the finite operational retarded-prefix fact; `originalEqualTerminalKetsGiveEqualReadouts` transports a genuine terminal-ket equality. Imported by `TSFVUnifiedRegression`.
- **Status:** source-written finite precursor only; not yet exact-head Agda-kernel accepted. It is **not** the OBS05 Kubo derivative, a space-local propagation bound, universal no-retrocausality under postselection or a four-dimensional causal cone. OBS01–OBS10 physical completion remains open.
- **YM synchronization:** latest independently inspected parent #1444 head `c1ea5c692637737a6007a597442be473bf41dd43` adds `YMClayOriginalWilsonR445R320TwoSourceSameFamilyExact` and `YMClayCMP119122116SelectedProducerWeldExact`. The former proves finite original n=3 literal mixed-log jets equal the actual R445 blocked/R320 pushforward covariance; the latter reuses selected R342/R467/R479 with explicit source, limit and energy/rate premises. Neither creates a physical observer/OS state dictionary, so HIL06–HIL11 and S10 are not discharged.
- **Integration guard:** GitHub comparison against the child head before this update reported 119 parent-ahead commits. Do not treat this document or a normal merge of source files as an Agda kernel receipt. Respect the parallel checker and reconcile concurrent changes without overwriting #1444's owners.

## 6 November 2026 — Karp-influenced all-order moment compiler and sourced 5D control

**Karp PR #1445 reuse:** `Karp21MichaelLevinObserverCutQuotientBoundaryExact` proves that globally flipped labelings have the same actual signed cut score yet distinct first-vertex raw observations. This is an explicit negative control against promoting equality of a selected quotient observable (or covariance) into identity of physical state. Its result is relevant to the OBS/HIL observable-separation gate; it is not an observer GNS or Yang–Mills construction.

**S10/HIL07 finite theorem:** `DASHI.Physics.Foundations.TSVFOriginalAllWordMomentTransportExact`, imported by `TSFVUnifiedRegression`, proves `originalWordEvaluationNaturality` by structural induction for every finite word. Given one actual source map, letter-level matching and the **same** expectation pushforward, `allOriginalFiniteWordMomentsFromSamePushforward` proves *all-order* finite moment equality. `originalAllPairingWordsTransport` applies this to arbitrary selected paired/adjoint words. No extrapolation from degree-two covariances. The physical pushforward is a premise to be instantiated with the exact R445 source after parent integration, NOT a newly manufactured Gibbs distribution. OS reflection, noncommutative products and positive observer state remain separate.

**KK04 nonflat source control:** `scripts/check_tsfv_5d_ads4_circle_winding_matter.py` checks the full 5x5 Ricci tensor, scalar Euler–Lagrange equation, stress tensor and Einstein equation for a independently specified Einstein–Lambda–periodic-scalar action. Exact local solution: `AdS4(L) x S1(R)`, circle-valued scalar `phi=n theta (mod 2 pi)`, nonzero integer `n`, `L²=3R²/(kappa5² n²)`, `Lambda=-3 kappa5² n²/(2R²)`. Nonflat, nonzero winding stress, horizontal reduction to **AdS4**, not the observed TSVF metric. This is a physical-equation example beyond flat KK but not KK08. Radion stabilization, observer physical calibration and YM gauge-sector agreement unproved.

**S11:** the wrapper `scripts/run_tsfv_unification_maxcut_20261106.sh` now passes the three newly source-written unification candidates (retarded prefix, all-word Gram setoid, all-word moment transport) through the canonical `run_agda29_parallel_check.sh` selected safe-source path. Do not require SymPy as an implicit Agda dependency: the 5D symbolic control is an independent Python receipt. At writing, Agda kernel acceptance, complete transitive trust review, and fresh parent conflict-free integration remain unverified.

## S01–S04: actual microscopic observer → measured causal 3+1

| Proposed producer lemma | Canonical original IDs | Exact proof target |
|---|---|---|
| **OBS01** — `selectedMicroscopicInstrumentExists` | `P01.L01,L02,L13` | Construct an actual microscopic Hamiltonian/unitary with the original pointer/environment, local intervention operators, calibrated state and reference observables; do not supply an abstract uninterpreted record. |
| **OBS02** — `selectedHistoryABLAndDecoherencePositive` | `P01.L03–L05,L14–L17` | From OBS01 derive positive normalized history class operators, nonzero selected partition, ABL/Born probability and admissible postselection/no-signalling. |
| **OBS03** — `originalRecordAlgebraConditionalExpectations` | `P01.L06–L08,L10` | Construct nested observable record algebras, positive unital conditional expectations, and the original filtration order directly from the selected physical state. |
| **OBS04** — `originalContinuousClockAndOperationalCausalOrder` | `P01.L11,L12;P02.L01` | Derive a continuously calibrated clock and retarded intervention-accessibility order; distinguish state filtering from reversed microdynamics. |
| **OBS05** — `originalKuboRetardedResponseFromInstrument` | `P02.L01,L06` | Prove the measured response derivative is the correctly signed retarded commutator of actual original local probes, not a second assumed Green operator. |
| **OBS06** — `originalLatticeSignalBoundAndContinuumFront` | `P02.L06,L12` | Derive a genuine uniform causal-response bound from the original microscopic interaction; prove any claimed sharp front only at the justified continuum limit. |
| **OBS07** — `originalIndependentDimensionFourScaling` | `P02.L02–L05` | From original event/interval counts and calibrated volumes prove a refinement-stable logarithmic dimension limit equal to four and construct its smooth causal 4-manifold; no preselected cubic 3-space. |
| **OBS08** — `originalPrincipalSymbolEqualsOperationalLorentz31` | `P02.L07–L10,L13–L15` | Extract the *actual* continuum response principal quadratic, prove rank-three spatial form, unique clock direction, one negative eigenvalue and exact operational null cone equality with calibration. |
| **OBS09** — `originalFutureConeHyperbolicEnergyWellposed` | `P02.L11,L12` | Prove global physical future orientation from selected filtration and source operator well-posedness/positive energy, not merely signature convention. |
| **OBS10** — `originalSignatureOwnersAndMassNoGoWeld` | `P02.L09,L14–L16;P07.L04` | Reconcile existing Lorentz source owners; use existing mass-sensitive response no-go to prevent a causal metric from being misidentified with a full quantum Hamiltonian. |

## HIL07/HIL08 2026-11-06 additional proof

- `DASHI.Physics.Foundations.TSVFObserverOSCyclicGramSetoidExact` is now in the child Golden regression. It proves the all-test Gram-observational equivalence relation reflexive, symmetric, transitive, reflected by the physical word map, and (with explicit OS word coverage) preserved in both directions. Pairings are preserved on all mapped words from one all-word Gram equality. This is a genuine *word-level setoid compiler*, **not** completed GNS Hilbert, a physical positive form, or proof that `allWordGramMatches` is inhabited.
- Key correction: vanishing of one mixed cross-pairing is NOT the GNS null equivalence relation. The implementation uses equality against every test word. The positivity/Cauchy–Schwarz lemma relating that equivalence to the usual norm-null quotient is still required.
- Latest YM parent's `YMClayOriginalWilsonR445R320TwoSourceSameFamilyExact` establishes original n=3 mixed-log two-source covariance on R445/R320. This is only a degree-two / centered-moment source, **not equality of arbitrary observable-word Schwinger Gram kernels**. A true HIL07 instantiation needs finite *all-order* moments from original Wilson products, same-order OS reflection pairings, physical observer state identification and compatible continuum measures. Do not silently promote matching covariance to full isometry.
- Independent OS word coverage at finite words is stronger than the physically natural dense cyclic range. Prove density, extend the isometry by Hilbert completion, then derive surjectivity from dense closed range. Domain and spectral compatibility remain distinct HIL09–HIL11 gates.
- Source read/write completed on child; exact-head `parallel_checker` has not executed, and no trusted kernel receipt is claimed. New YM parent file is not in this branch yet; do not import it before a conflict-resolved source merge.

## S08–S09: actual observer Hilbert/Stone and physical YM OS identification

| Proposed producer lemma | Canonical original IDs | Exact proof target |
|---|---|---|
| **HIL01** — `observerStatePositiveOnOriginalStarAlgebra` | `P03.L01,L02,L05` | From the original record instrument construct a positive normalized state omega with omega(A* A)>=0 on its physically anchored observable algebra. |
| **HIL02** — `observerGNSNoncollapsedHilbertCompletion` | `P03.L01–L05` | Build null quotient, positive complex inner product, Cauchy completion, nonzero distinguishable vectors and compatible source-derived symplectic J when claimed. |
| **HIL03** — `observerWeylCCRCommonDenseInvariantCore` | `P03.L06–L08` | Construct the selected finite-to-complete Hilbert operators, Weyl relations and a genuine dense common domain for CCR with correct nonzero hbar; reject finite qutrit promotion. |
| **HIL04** — `observerSourceTimeAutomorphismsStronglyContinuous` | `P03.L09,L12` | Prove the same original dynamics induces state-preserving automorphisms and strongly continuous U_obs(t) on the completed observer Hilbert with the physical clock. |
| **HIL05** — `observerStoneSelfAdjointEnergyAndSpectralMeasure` | `P03.L10,L11,L13` | Using Stone on HIL04, derive a densely-defined self-adjoint H_obs, its domain, spectral resolution and correct i*hbar derivative; prove lower boundedness separately. |
| **HIL06** — `sameOriginalObserverOSSchwingerStateSource` | `P07.L02,L03` | Accept the actual independently built YM OS theory from #1444; identify its selected state, gauge observable sector, Euclidean reflection, coupling and physical time with the observer source. |
| **HIL07** — `observerOSCyclicGramEqualsOnAllObservableWords` | `P07.L05` | Prove all original cyclic observer/OS word-pair Gram matrices equal under a specific source-indexed dictionary, implying null-quotient well-definedness; not merely a selected ket. |
| **HIL08** — `observerOSWordMapExtendsToOntoUnitary` | `P07.L05` | Construct W on the dense cyclic words, prove complex linearity, isometry, null preservation and density on both completed Hilberts; derive surjectivity rather than asserting it. |
| **HIL09** — `observerOSStoneGraphIntertwinesOnFullDomain` | `P07.L06,L07` | Prove W U_obs(t)=U_OS(t) W for all physical real times, then use actual strong differentiability to derive W Dom(H_obs)=Dom(H_OS) and W H_obs=H_OS W. |
| **HIL10** — `observerOSSpectralProjectionsAllBorel` | `P07.L07;P11.L07` | From HIL09's true self-adjoint operator identity derive W E_obs(B)=E_OS(B) W for every Borel B; gap transport requires the independent physical YM spectral result. |
| **HIL11** — `observerOSAllCorrelatorsWickUniqueness` | `P07.L08,L10,L11,L13` | Match actual gauge-invariant Wilson/time correlation functions and prove holomorphic continuation/uniqueness with the same physical clock, distinct from time reversal. |
| **HIL12** — `physicalTSVFPointerOSStateAndBackwardRobustness` | `P07.L15,L16;P11.L19` | Construct the actual TSVF macro-pointer as matched physical observable and test allowed backward conditioning without changing earlier operational records or inventing a second time axis. |

## S05–S06: original selected nontrivial five-dimensional KK Einstein–matter

| Proposed producer lemma | Canonical original IDs | Exact proof target |
|---|---|---|
| **KK01** — `measuredObserverBaseHasPhysicalCircleBundle` | `P08.L01,L02` | Construct an actual spacelike principal circle bundle over the OBS07 physical M4, global cocycles, physical radius/connection and inherited time/spin orientation. |
| **KK02** — `selectedEinsteinGaugeMatterActionWellDefined` | `P08.L02,L03` | Construct the actual 5D Einstein–gauge–matter action on the KK bundle with radion, couplings, boundaries, regulators and diffeomorphism/gauge invariance. |
| **KK03** — `completeFiveCurvatureVariationStressAndGaugeSplit` | `P08.L04–L06` | Derive all field equations from that SAME action, scalar/vector/tensor curvature terms, conserved stress and the actual 4D YM+scalar zero-mode reduction; retain F_mu5 cross-fibre modes. |
| **KK04** — `selectedNonflatOrNonzeroStressFiveSolution` | `P08.L03,L06` | Exhibit one source-selected smooth 5D field/metric solving every coupled Einstein–matter equation and boundary with nontrivial field/stress where required, rather than the existing flat vacuum toy. |
| **KK05** — `physicalKKModesCouplingAndClockCalibration` | `P08.L07,L08` | Prove 4D/5D coupling relations, KK eigenmode normalization and thresholds in the actual frame with matched physical radius/clock/Planck units. |
| **KK06** — `radionAndHeavyKKControlWithExplicitError` | `P08.L09,L10` | Prove physical stabilization or retain fields; justify truncation by a uniform EFT error in E*ell, cutoff/volume and observable norms. |
| **KK07** — `pureYMGaugeSectorDecouplesOrCounterexample` | `P08.L11` | If matching the YM worker's pure SU(N) theory, prove gravity/matter/KK decoupling for that SAME action/measure/observable class, otherwise report no-go. |
| **KK08** — `KKReducedMetricEqualsIndependentObserverMetric` | `P08.L12;P07.L09,L14` | Prove reduction of KK04's actual five-metric equals OBS08's independently extracted observed g4 (or a quantified epsilon), with one source, clock and gauge dictionary—not a chosen equal label. |
| **KK09** — `fifthCrossFibreCurvatureAndTypedDimensionWeld` | `P08.L16,L17` | Use native 5D/4D 10-plane-to-6-plane comparison to retain physical cross-fibre curvature and distinguish Lorentzian KK, Euclidean gauge and stochastic axes. |
| **KK10** — `fourMetricCannotRecoverUniqueFiveLiftWithoutProbe` | `P08.L12;P11.L08` | Extend existing vertical radius/connection noninjectivity by constructing actual fifth-sector observable probes or keeping the gauge-equivalent family explicit. |

## S10: source/limits BIDI and independent falsification

| Proposed producer lemma | Canonical original IDs | Exact proof target |
|---|---|---|
| **BIDI01** — `singleOriginalPhysicalStateAndObservableKey` | `P11.L01,L12` | Construct proof-relevant identity for original source, state, interventions, gauge G, couplings, regulator, boundary, clock, observable and 5D bundle across all transports. |
| **BIDI02** — `originalObserverOSForwardBackwardCommutingSquare` | `P11.L02,L05` | Prove the original source-to-Hilbert/OS forward diagram commutes on all relevant test vectors and that independent reverse observable predictions satisfy source-specific constraints. |
| **BIDI03** — `originalObserverKKMetricStressCommutingSquare` | `P11.L04,L08` | Prove original observer metric/stress and true KK-reduced field quantities agree at the same physical source and units; prevent Wick/star/auxiliary-time confusion. |
| **BIDI04** — `orderedCutoffVolumeKKHistoryOSLimitsBounded` | `P11.L06,L09` | Quantify interchange errors for a->0, volume->infinity, KK radius, history refinement and OS reconstruction; refuse interchange without Cauchy/tightness estimates. |
| **BIDI05** — `bidirectionalIndependentNegativeControls` | `P11.L03,L10,L11` | Produce counterexamples/witnesses for mismatched clocks, wrong signature, mass-blind principal, incorrect RP, fifth-fibre loss, false finite-to-physical gap and wrong gauge. |
| **BIDI06** — `terminalE1OnlyFromConstructedPhysicalWitnesses` | `P11.L07,L15,L18` | Derive terminal source-identical unification theorem only after actual OBS/HIL/KK/BIDI producers and independently supplied YM OS physics are inhabited; no Set-field or free toy promotion. |
| **BIDI07** — `parallelCheckerExactHeadGoldenTrustReceipt` | `P11.L13,L14,L16` | Use repository run_agda29_parallel_check.sh on selected sources and separate/combined roots; record compiler/stdlib/head/exit plus full transitive axiom audit and independent analysis. |
| **BIDI08** — `originalPhysicalFalsificationAndInterpretationReceipt` | `P11.L17,L19` | Supply independent observable/dimension/spectrum/KK threshold tests and explicitly distinguish selected TSVF branch, Everett alternative and merely viable universes. |

## Mathematical endpoint

For the one selected original physical source M, prove a physical Lorentzian g_obs(M), an independently constructed complete complex observer Hilbert with self-adjoint H_obs, a genuine 5D Einstein–matter solution G5(M), and an onto state/observable-preserving unitary W onto the independently reconstructed YM OS Hilbert, with:

\[\operatorname{KKReduce}(G_5(\mathcal M))=g_{\mathrm{obs}}(\mathcal M),\qquad W\operatorname{Dom}(H_{\mathrm{obs}})=\operatorname{Dom}(H_{\mathrm{OS}}),\]
\[WH_{\mathrm{obs}}\psi=H_{\mathrm{OS}}W\psi,\qquad W E_{\mathrm{obs}}(B)=E_{\mathrm{OS}}(B) W\quad\text{for all Borel }B.\]

**Actual verification entrypoint, not direct Nix or system Agda:**

```bash
AGDA_JOBS=4 bash scripts/run_tsfv_unification_maxcut_20261106.sh
```

This wrapper calls `scripts/run_agda29_parallel_check.sh`, which manages the selected Agda29/compiler, stdlib, vendor/bishop, parallel checks, cache, logs and memory limits. Source/Agda kernel and independent physical meaning are separately audited; no completion is claimed merely by writing this contract.

**YM dependency:** The other worker's fixed-physical-cube coefficient C^(a,L)w<=q w at fixed physical ell, literal CMP116 marked-J decay, physical Wilson continuum, OS reconstruction and positive spectral gap are NOT re-proved in #1460. HIL06/HIL09-HIL11 consume the ACTUAL OS Hilbert/H and physical observer dictionary only after they are established.
