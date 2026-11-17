# Smith/Filsinger / Sun–Earth: exact phases, deliverables and remaining lemmas
**16 November 2026 — programme continuation / user-origin steelman.**
**Scope and verification:** source-audited on PR #1524 at `ba5269f4b043836eeaec8f898d9a91932b933c5c`, PR #1521 at `88b53fcb24b68bc37e0834a00a55279306f87018`, and PR #1519 at `792646c73d7d05f4a38cf32afc3261aa3a08f23b`. This roadmap is not a new kernel result or physical device receipt. Prefer Agda golden, local pinned check; no ESD writes, no forced TOE promotion.

## Steelman / source-owner boundary
A relatively small, timed, nonlinear electromagnetic controller may sustain two coupled, phase-offset source/receiver branches with **propagation, causal delay, material memory and source backaction**. By altering physical impedance/mode overlap and environmental response it may increase useful energy transferred from a *separately replenished* source. Controller work, initial donor charge, outgoing energy, loss, material-modulation work and real useful output remain explicit. Filsinger's recorded Earth-ground apparatus, *proposed* common-midpoint/golden plate and Don Smith's independently sourced figures are NOT established as one hardware identity. User's source/sink+solar+rain interpretation is a new conditional extension.

Distinct source regimes:
- **W (coherent wave):** two-port TCMT with natural incident wave, driver wave, spatial modes, reflection `s_-=-s_+ + K†a`; external wave/controller phase may matter if coherence is physical. Random independent natural phases erase mean quadratic cross terms in the specified linear regime. Actual external coherence and power not measured.
- **B (biased DC/slow source):** independent DC/low-frequency natural Thevenin source, with *internally* anti-phased controlled load/conductance branches; no externally supplied RF phase reference is required. For matched ideal fixed-R source anti-phase can stabilize total conductance and reach its fixed-source maximum but cannot exceed it or prove environmental source origin.
- **N (nonlinear history-dependent):** open, dispersive Maxwell–plasma–soil/cloud state where source response may depend on delayed controller action, memory, field coupling and natural replenishment. This is the main physical target. Neither W nor B alone establishes N.

## Headline acceptance status
- Merged producers: PR #1507 causal nonlinear source-port BIDI, #1514 hybrid/regime/source-identity, #1515 two-kernel acoustic spectral observation; each remains scope-specific. #1519 multirate motors is a *methods donor*, not Smith's original device.
- Draft #1521: nonlinear dispersive material port, Hall/Pedersen work separation, 1D line+finite donor+recharge and source admittance. Its M1–M7 have source-equivalent local numerical/symbolic receipts; M8/M9 abstract repeatable-cycle bounds, no Agda exact-head receipt and no original physics admission. Replenishment deficit persists in example.
- Draft #1524: `SmithFilsingerSunEarthCoupledSourceExact.agda`, `SmithFilsingerMidpointPhaseWorkExact.agda`, coherent source-controlled 2-mode/2-port (17 local tests), complementary DC Thevenin branch (12 local tests), **29/29 local source-equivalent tests reported**; no pinned kernel nor independently run current-head verification. Newest PR head should always be read before executing.
- No original-world same-unit source work, port geometry, calibrated phase, climatic-control gain or physical atmospheric bridge demonstrated.

**Important naming:** programme delivery phases Q0–Q6 below are separate from the canonical *physical gate* identifiers S0/P1/P2/R1/R2/R3/D1/D2 already used in #1521.

## Dependency-ordered delivery phases
| Delivery phase | Status | Concrete deliverable | Promotion test |
|---|---|---|---|
| Q0: original source + source identity | Documentation completed; physical S0 open | Typed reel/patent/claimed-plate graph with source IDs and separate ground/portable candidate configurations | Every claim traceable to source; not inferred pin continuity |
| Q1: exact finite mathematics | Models source-authored; kernels open | Agda checked source-separated signed port bounds, anti-phase matching theorem, incoherence negative controls, two-world non-identifiability | Pinned Agda 2.9 exact-head + source-equivalent tests; explicit hypotheses |
| Q2: full time-domain physical operator | Open, with #1519/#1521 method donors | One causal spatial field/material memory/receiver transfer operator and passive energy identity | Strict causal propagation, memory, Hall/Pedersen, Maxwell/Poynting, passivity, retarded phase at receiver |
| Q3: physically bounded source access | Open | Site/source-specific measured terminal `Voc, Rs` or nonlinear loaded `v(t),i(t)` kernel and uncertainty; real plate/electrode geometry | Independent natural real power, calibrated same-object return and two-load / time-varying counterfactual |
| Q4: one selected actual apparatus | Open | Driver+shunt+coils+cap banks+switch+diodes+ground/plate+acoustic source model with one parameter set | Reproduce start/hot/null/shutdown and *actual* power, no cross-reel conflation |
| Q5: sustainable matched extraction | Open | Repeated steady/cyclic tuned/control source–receiver, natural source backaction and no storage drawdown | Positive net independently replenished natural work at actual receiver, controller/drive/loss all metered |
| Q6: environmental/atmospheric extensions | Open and conditional | Sun-wind/ionospheric, plasma THz/IR, cloud rain/local cold-pool kernels and independent measured gain; TOE intake only after acceptance | All mechanism arrows sourced and quantified; local rain cooling distinct from global TOA effect |

## Exact remaining MATHEMATICAL lemmas: unclosed / unpromoted
| ID | Exact target | Reuse owner / proof strategy | Current cut |
|---|---|---|---|
| F01 `phaseCommonDriverRatioInvariant` | for energy-normalised linear `a_j=H_j s` with fixed nonzero common `s`, positive amplitude rescaling leaves `arg(a_2/a_1)` unchanged | #1524 `SmithFilsingerMidpointPhaseWorkExact`, two-mode Python | local numeric, no general Agda proof |
| F02 `receiverPhaseIncludesRetardedPath` | `Δφ(x,ω)=arg(s2H2/s1H1)`; pure delays give `−ω(τ2−τ1)` modulo 2π, but not a universal dispersive-group-delay law | `SmithFilsingerTimeIndexedTransferExact`, #1519, #1524 | pure-delay numeric, no physical-operator weld |
| F03 `detunedFreePhaseCannotRemainFixed` | two undriven uncoupled modes with distinct real frequencies cannot have constant relative phase on any nontrivial interval; distinguish common-drive lock | #1524 two-mode tests | not Agda general math |
| F04 `independentUniformPhaseCancelsQuadraticCrossTerm` | phase average of linear coherent cross term vanishes when external phase is independent uniform; no such claim for nonlinear/hysteretic response | #1524 `incoherent_phase_average` | 128-sample numeric, analytic/Agda generalisation open |
| F05 `fixedSourceMatchGapSquare` | `Voc²/(4Rs) − Voc² G/(1+RsG)² = Voc²(RsG−1)²/[4Rs(1+RsG)²]`, `Rs>0,G≥0` | #1524 DC matching SymPy, #1521 SP2 | symbolic local, Agda theorem over rationals/ordered field open |
| F06 `complementaryConductanceFlatAtPi` | `G1=g+a sin(t),G2=g+a sin(t+π)` gives `Gtotal=2g` at all t; with `2g=1/Rs` output attains fixed-source match bound | #1524 DC script | symbolic local; exact Agda/closed model theorem open |
| F07 `phaseOptimumDependsOnSourceImpedance` | counterexample that anti-phase is universal optimum, when `Rs`, load, delays or coefficient change | #1524 DC source-mismatch comparison | model counterexample local; portable finite exact witness unpromoted |
| F08 `naturalPortWorkMustBeSigned` | incident minus outgoing; if natural incoming=0 then naturally *net supplied* power cannot be positive in passive model; controller may radiate outward | `MidpointTwoPortWorkExact` + #1521 TCMT | Nat counterexample authored, physical port weld open |
| F09 `phaseReadoutCannotIdentifyNaturalSource` | two physical-source classifications with identical coherent-phase observation reject unique inference of source from phase alone | `MidpointTwoPortWorkExact.phaseReadoutAloneCannotIdentifyNaturalWork` | source-authored Agda, kernel open |
| F10 `retardedNonlinearMaterialEnergyIdentity` | Poynting + time-varying polarization/relaxation/modulator work with causal constitutive memory; no unaccounted material-work term | #1521 M1–M4 + existing Maxwell adapters | symbolic 1D/constitutive model only, 3D coupled theorem open |
| F11 `wholeSystemMatchedTrajectoryDifference` | same initial state/exogenous forcing: `δW_load−δW_drive−δW_mod = δW_nat−δW_loss−δU_final` for same well-defined boundary, including outgoing radiation in loss term | #1521 M4/M9, #1524 two-port | proof/physical source backaction weld open |
| F12 `replenishedCycleVsTransientDiscriminator` | full-state cyclic return implies useful work must be paid by ongoing source+driver+controller, not initial donor; positive net after costs requires independently positive replenishment | #1521 M8/M9 `RepeatableSourceReceiverCycle`, `TerminalCapRepeatableCycle` | abstract bounds source-authored, kernel/real-world open |
| F13 `fullColumnSoilIonosphereAccessWeld` | physical collection estimate using calibrated `J,E,σ,ε,Σ_{Hall/Pedersen}`, geometry and retarded boundary response | #1521 P2-PHYS and `AdmittedNaturalAccessCap` | simplified slab/column only |
| F14 `allRegimesOnePhysicalParameters` | one selected apparatus model explains startup, hunting, phase nulls, dual acoustic shutdown peaks, simultaneous electrical power | merged #1515 source audio + #1521 | original A1/A2/A3/B1/B2/B3-PHYS all open |
| F15 `sourceEnvironmentLoadSameCycle` | real signed natural work positive after drive/controller and losses over repeatable matched cycle with source replenishment and terminal access | original C3/R3; #1521 + #1524 | decisive physical endpoint open |
| F16 `electricControlRainColdPoolCausalGain` | independently attributable controller→cloud field→drop size/rate→evaporation/cold pool→surface anomaly, with energy/heat and counterfactual uncertainty | #1524 S4a/S6a/S6b/S6c/S7a, original Tinsley etc | end-to-end physical link open |

## NON-MATHEMATICAL hard receipts, not derivable from re-labelling Agda Set fields
- **S0/A1** original Smith vs Filsinger plate/netlist pin continuity; precise source claim and selected real circuit.
- **P1/A2** simultaneous V/I/switching clock, capacitor initial/final state, shunts and microphone; do not map 7.8 kHz acoustic to 7.8 Hz Schumann.
- **P2-sourceOperatorSameFilsingerCircuit** independent source voltage/current/admittance under actual load/phase, not chosen "Earth current" parameter.
- **R1/A3/B1–B3-PHYS** same-device nonlinear joint physical inverse explanation of on/hot/null/off.
- **R2/C1–C2** actual 3D Maxwell–ground–ionosphere with causal plasma and Hall/Pedersen/soil/material response, not finite discrete flight alone.
- **R3/C3** environmental positive signed net natural *replenished* work on matched complete cycles; controller/loss accounting and natural driver.
- **D1** pinned Agda 2.9 kernel receipts at exact PR heads (including #1521 and #1524, imports and finite gates).
- **D2** original measurement, source attribution and evidence-tier BIDI, user/Smith/Filsinger/Waker/Tinsley/HAARP correctly distinguished.

## Recommended MAX-CUT order and immediate deliverables
1. **First mathematical cut F05/F06/F07**: promote fixed-source matching square, anti-phase constant aggregate conductance and source-impedance counterexample into exact ordered rational/finite functions in the inherited Agda owners; prove field invariants, test negative controls; no new electrical theory required. Separately F01/F03/F04 phase coherence.
2. **Then F08/F09/F11/F12**: pinned Agda source-work and two-world proof plus matched trajectory repeatability; no false physical claim. Run pinned acceptance for #1521 then #1524, instead of merging source-only modules as kernel complete.
3. **Next F02/F10/F13**: bridge selected full causal distributed Maxwell/memory, natural source admitted parameters, and actual mid-point boundary response. Reuse multirate #1519 only as techniques, do not transplant motor parameters.
4. **Then F14/F15**: source-specific same-original source-to-receiver mechanical/acoustic/electrical and repeatable environmental-work observations. Without these, no physical over-input, solar or atmosphere work promotion.
5. **Last F16**: cloud/rain/cold-pool application only once small control actually perturbs a measured atmospheric field and cloud state in a verified causal model. Keep local cooling real even if global energy budget doesn't change.

## Research references and lineage
- Don Smith original Kelly/Darrer source and Filsinger reel provenance: `Docs/research/DonSmithFilsingerReelsOriginalClaimBidi20261111.md`; `Docs/research/FilsingerDonSmithGoldenRectangleLissajousMaxCut20261111.md`; `Docs/research/SmithFilsingerGoldenFibonacciSingleWaveMaxCut20261112.md`.
- Temporal coupled-mode theory and energy conservation: Zhao/Guo/Fan (2019) https://cguo.org/pdf/zhao2019a.pdf; Wu/Lalanne (2024) https://doi.org/10.1364/OE.517237.
- Source-dependent Earth/ionosphere work and storms: Lukianova et al. (2025) https://doi.org/10.1007/s10712-025-09914-7; Lin et al. (2026) https://doi.org/10.1029/2025GL118532; Tinsley (2023) https://doi.org/10.1175/BAMS-D-23-0065.1.
- HAARP nonlinear retarded current/echo: https://doi.org/10.1029/2011GL049263 and https://doi.org/10.1029/2009JA014610.
- Electric fields and rainfall / natural cold pools: https://doi.org/10.1029/2021GL093577; Kirsch et al. (2021) https://doi.org/10.1175/MWR-D-20-0197.1.
- Infoton source/thermodynamic crosswalk: `docs/research/InfotonP30WalkerMaxCut20261115.md`; no physical Infoton proof used in energy ledger.


## 16 November next max-cut execution: exact finite mathematics committed (NOT Agda kernel checked)
**New owner** `DASHI/Physics/Motors/SmithFilsingerFinitePhaseMatchingExact.agda` reuses existing Nat solver examples (`HydrogenEfficiencyCrossMultiplyExact`) and the existing midpoint signed-port work. No new competing Maxwell/circuit ontology and no changes to ESD or accepted TOE.

| ID | New source-owned concrete certificate | Independent acceptance / limit |
|---|---|---|
| F01 | `commonDriverCrossRatioInvariant`, polynomial equality for a common positive scalar multiplying two Nat channel responses | Algebraic cross-ratio proxy only; full complex phase remains open |
| F04 | `fourPhaseQuadraticCrossCancellation`, exact signed four-phase finite cancellation | Finite 0/90/180/270 phase ensemble, not arbitrary nonlinear or random atmosphere |
| F05 | `sourceMatchSquareGapAbove/Below`, `sourceMatchRationalAbove/Below` | General Nat polynomial square-gap certificate after rational cross multiplication. Positive denominator/physical Thevenin values remain separate |
| F06 | `complementaryConstantTotal`, arbitrary nonnegative finite two-slot conductance complement | Exact discrete version of phase opposition; no physical switch-loss/timing claim |
| F07 | `resistanceOneAntiStrictlyBetter`, `resistanceThreeInphaseStrictlyBetter` | Strict exact rational witness: best phase depends on source impedance |
| F08 | `naturalOffCannotSupplyPositiveNet` | Abstract signed-port source-off impossibility; not independently measured environmental port |
| F09 | Reuse `Midpoint.phaseReadoutAloneCannotIdentifyNaturalWork` | Existing source-authored witness; no duplicate |
| F11 | `matchedWorldsCrossBalance`, additive two-trajectory work equality at shared initial storage | Formal paired-world bookkeeping, not dynamic Maxwell/exogenous-forcing identity |
| F12 | Reuse #1521 `RepeatableSourceReceiverCycle`, `TerminalCapRepeatableCycle` | Do not duplicate on this unmerged branch; same-original replenishment open |

**Exact resistor-phase discriminator** (normalized `V_oc=1`, instantaneous `P(G)=G/(1+R_s G)^2`, two-slot in-phase `G=1/2,3/2`, anti-phase `G=1`):
- `R_s=1`: anti `1/4` versus in-phase `52/225`; exact anti advantage `17/900`.
- `R_s=3`: anti `1/16` versus in-phase `196/3025`; exact **in-phase** advantage `111/48400`.
- For `R>0`, `P_anti-P_in=-R*(3R^3-12R-8)/[(R+1)^2(R+2)^2(3R+2)^2]`. This expression has a single positive crossover in the interval `(9/4,23/10)` (~2.2743). The preferred phase is **source-dependent**, not dictated by 1:1.618 geometry.

**Validation evidence:** independent local exact `Fraction`/SymPy replay **9,112 arithmetic assertions PASS** and receipt at `Artifacts/smith-filsinger/finite_phase_maxcut_exact_receipt_20261116.json`. Code/test entrypoint: `scripts/check_smith_filsinger_phase_maxcut_exact.py`, `scripts/test_smith_filsinger_phase_maxcut_exact.py`. Exact-head Agda 2.9 target: `scripts/check_smith_filsinger_finite_phase_agda29.sh`. The pinned Agda compiler was unavailable in the analysis runtime: **D1 remains OPEN**; do not claim the committed scripts or new Agda were executed at their GitHub head. The independent replay is a separate arithmetic check, not a kernel certificate.

**Updated mathematical-status cut:** F01/F04/F05/F06/F07/F08/F11 have substantially stronger source-authored exact witnesses; F09 reused. They are **not yet pinned Agda accepted**. F02/F03/F10/F12 physical weld/F13/F14/F15/F16 remain as originally scoped. No original-world physical S0/P1/P2/R1/R2/R3/D1/D2 gate is newly closed.


### Latest cross-PR reuse: retarded phases and dynamically replenished source
The finite-Agda proof owner now imports `SmithFilsingerTimeIndexedTransferExact` for two explicitly scheduled paths that arrive at the same clock time after *different launches*. `twoPathsReachSameTime`, `arrivalDoesNotIdentifyLaunchPhase`, `freeRunningDifferentClocksStartAligned`, and `freeRunningDifferentClocksCanSeparate` are finite causal-clock counterexamples for F02/F03. They do **not** establish a physical Maxwell dispersion relation or continuous phase entrainment. This prevents the old error of identifying identical drive-terminal phase with interaction-region phase.

The newly added **#1524** owners `SmithFilsingerReplenishedCycleCapExact.agda` and `scripts/check_smith_filsinger_dynamic_replenishment.py` are independent but directly relevant F12 producers. They were added concurrently; do NOT duplicate their derivation. The continuous model is:
\[
C\dot v = g(V_{\rm up}-v)-G(t)v,\quad U=Cv^2/2.
\]
For *any selected nonnegative time-dependent G(t)* under a fixed positive linear upstream source and a capacitive state,
\[
\underbrace{\int_0^T G(t)v(t)^2\,dt}_{W_{\rm load}}
+\underbrace{U(T)-U(0)}_{\Delta U}
+g\int_0^T(v(t)-V_{\rm up}/2)^2dt
=\frac{gV_{\rm up}^2T}{4}.
\]
The square term is nonnegative; if every store is restored after a periodic cycle, useful load work cannot exceed the fixed linear source's matched terminal cap, and controller costs reduce *net useful* work further. This generalizes the earlier quasi-static source matching bound to the selected finite-memory ODE, **not** to a nonlinear solar/magnetospheric source operator. The new Python method analytically integrates each **piecewise-constant** segment; sampling its sinusoidal branch pattern at segment midpoints is not an exact continuous-sine integration. The `RepeatableSourceCycle` Agda record is a finite Nat conditional source cap, not a proof that the environmental input is naturally replenished. As of this addendum no independent pinned kernel or exact-head Python rerun was obtained.

The physically important remaining contrast: `W_nat` measured at a real terminal must be positive net of reflection and initial donor drawdown, whereas atmospheric solar forcing may change in response to loading. A fixed-voltage Thevenin cap does **not** limit all nonlinear upstream solar source adaptation; it is a falsifiable null model. Full Maxwell/plasma/solar boundary-weld F10/F13/F15 remains OPEN.


## Maximum-cut continuation 2026-11-16: F11/F12 finite replenishment accepted locally

**Current PR provenance:** #1524 adds the tested dynamic-source producer and finite Nat proof consumer to the pre-existing coherent-wave/phase and fixed-DC source interpretation. #1521 remains the owner of the physically distinct Earth/atmospheric/soil source-access estimates and nonlinear constitutive-port work. #1519 (head observed 41fd0c37f8a8b70b73616f1fb75ee3c2c1d9e625) is an independent multirate exact-energy **method donor only**, not original Smith/Filsinger hardware. Existing source owner, finite reservoir owner, signed reflection owner and retarded flight owner are reused.

### Exact outputs and acceptance hierarchy

| Formal item | Strongest completion supported now | What is NOT closed |
|---|---|---|
| F05 fixedSourceMatchGapSquare | Full real algebra identity by square completion; 2026-11-16 passive time integral extends it when the source is fixed | Unrestricted nonlinear/plasma source ceiling; ordered real field Agda theorem |
| F06 complementaryConductanceFlatAtPi | Exact sine anti-phase identity and a constant matched-load stationary solution; the finite-capacitance program demonstrates it again | Original capacitor/switch transistor implementation |
| F07 phaseOptimumDependsOnSourceImpedance | Existing counterexample with other Rs and separately chosen optimum; fixed-parameter periodic source benchmark | Same-original physical optimum |
| F08/F09 signed work/phase nonidentifiability | Earlier Agda source owner, 29/29 locally tested source-equivalent numerical comparisons | Pinned Agda, physical source classification |
| **F11** wholeSystemMatchedTrajectoryDifference | New exact capacitor ODE energy identity and integrated signed natural source/terminal/driver loss; 37 additional Python tests, same-branch phase controls | Actual nonlinear retarded two-world Green/Maxwell; same-device synchronized work |
| **F12** replenishedCycleVsTransientDiscriminator | A new finite-Nat source-authored cancellation proof, cyclic natural+controller bound and independently admitted cap; exact segment-integrated finite source/donor negative controls | Kernel acceptance; physically admitted cap/independent replenishment |
| F13 fullColumnSoilIonosphereAccessWeld | Ideal 1 m² full-column static fixed-source Pmax = 0.1475 µW, 60-s Emax=8.85 µJ | Real plate/earth source operator and geometry/field weld |
| F10 / F14 / F15 / F16 | Producer interfaces plus conditional source-separated research gates | Actual retarded 3D system, original joint hardware, natural repeatable work, weather effects |

New GitHub files:
- DASHI/Physics/Motors/SmithFilsingerReplenishedCycleCapExact.agda
- scripts/check_smith_filsinger_dynamic_replenishment.py
- scripts/test_smith_filsinger_dynamic_replenishment.py
- scripts/check_smith_filsinger_dynamic_replenishment.sh

The **3/3 Git blob SHA comparisons** of producer, 37-case test and Agda module match locally tested source files exactly. Source-equivalent local Python acceptance: **37/37 new; 66/66 targeted aggregate** including the earlier coherent-wave and fixed-DC phase controls. No pinned Agda/Nix executable here. Source-authored finite lemmas are not yet kernel checked.

### Mathematical cut theorem: no depletion means no hidden source

Source access is a selected physical port, not an adjustable parameter. For the **passive fixed linear** upstream voltage source V_s with feed conductance g, controlled load G(t) and finite storage C v²/2:

\[
W_{\rm terminal}=W_{\rm load}+\Delta U,\qquad
\frac{gV_s^2T}{4}-W_{\rm terminal}
=g\int_0^T(v-V_s/2)^2dt\ge 0.
\]

The time integral is independent of how the two internal branch phases are scheduled; **timing can improve matching, not expand the assumed source**. Source-off long-pulse model: Wload ~0.5 and DeltaU ~-0.5, zero natural work. At a genuine periodic full-store return DeltaU=0, useful load <= natural fixed-source matching ceiling. Real device source backaction and changed natural source law (N regime) require a separate physical boundary PDE with correctly attributed external work.

The abstract Nat theorem derives Wload <= admitted Wnat + Wcontroller on repeatable cycles. Its cap receipt is **assumed and explicit**, not inferred from atmospheric fair-weather J or global voltage. The actual Wnat measured for Filsinger remains UNKNOWN.

### Remaining endpoints, ranked by actual original goal (not toy theorem count)

1. **S0/P1 - pinned configuration and simultaneous ports:** original Filsinger Earth circuit vs proposed portable common-midpoint/plate vs Smith patent/editor diagrams remain non-identical. Record source, shunt/rectifier/return pins, real controller current and voltage, capacitor stored-state before/after, acoustic/electrical clocks, load and Earth terminals on ONE selected configuration.
2. **P2 - the decisive physical source operator:** obtain actual under-load port v(t),i(t), two or more external load conditions, signed incoming/outgoing RF or earth conduction, measured driver-controlled phase and matched natural forcing. The global full-column ideal E/J figures are explicitly NOT this receiver's available watts.
3. **R2 - replace fixed g/Vs with 3D physical response:** one causal spatial Maxwell/material/plasma/soil boundary; Poynting, Hall/Pedersen, nonlinear memory, return path, finite propagation and source backaction. Reuse PR #1521 constitutive source, #1519 multirate method if applicable; no speed-of-light or acoustic interpretation inferred from a temporal phasor.
4. **R3 - renewable real work, not depletion:** solve/test matched tuned/control trajectories under same external forcing, with all initial/final local AND source storage, pump, controller, loss, outgoing radiative flux, electrode and chemical potential. A physical same-cycle positive environmental work receipt is mandatory, not merely mathematical source work.
5. **R1 - original startup/hunting/null/pump-off:** one hardware-selected model explains actual acoustic plus synchronous electrical observables; no cross-reel evidence substitution or chosen normalization.
6. **D1/D2 - kernel + actual admission:** run shell wrapper with --agda on pinned Agda host, check exact heads and create authentic same-original source-to-proof weld; do not auto-merge/TOE-promote. No ESD editing.
7. **Q6 - conditional Sun/cloud/rain/local-cooling extension:** requires controller-to-local-electric-field evidence, causal charge-to-droplet-to-rain experiment, local enthalpy/cold pool and separately climate TOA controls. Different goal from positive electrical harvesting and still wholly OPEN as an end-to-end intervention.

**Programme status:** Q1 mathematically advanced and locally tested, pinned kernel still OPEN; Q2 linear finite RC submodel advanced, physical Maxwell remains OPEN; Q3/Q4/Q5 physical apparatus admission remain OPEN; Q6 environmental effects OPEN. The strict original physical gate count remains **0/8**. Reports of conditional models do not change that count.


## 17 November continuation: F10/F13 source/reference/solve (selected-model result)
Read [the new F10/F13 dedicated report](https://github.com/chboishabba/dashi_agda/blob/research/sun-earth-coupled-source-20261116/Docs/research/SmithFilsingerF10F13FieldToPortMaxCut20261117.md). Consumer of the *unmerged* PR #1521 material/Hall/Pedersen and source-admittance owners; no shadow circuit or Maxwell ownership.

* **F10 selected-model symbolic PASS:** passive Debye ADE with time-varying chi, explicit signed controller modulation work and positive tau*Pdot²/(eps*chi) relaxation; time-varying instantaneous epsilon negative-control; Hall zero Joule heating in NEUTRAL frame only; lab-frame neutral-wind energy; Poynting partition with no doubled terminal loss. **F10 full 3D nonlinear retarded source/material solution OPEN.**
* **F13 selected exact Laplace benchmark PASS:** Phi(r)=V*a/r for hemispherical equipotential contact in isotropic homogeneous half-space, G=2*pi*sigma*a; geometry-distinct ideal disk boundary G=4*sigma*a; independent 1D stratified tube R=H*(1-exp(-h/H))/(A*sigma0). No claim these are an exact generic 3D atmosphere/soil/ionosphere solution. **F13 real source impedance/effective aperture/ionospheric operator OPEN.**
* Prior citation correction: A. Tip (1998) is **Phys Rev A 57, 4818**, `10.1103/PhysRevA.57.4818` (“Linear absorptive dielectrics”); Wu & Lalanne (2024) title is *Exact Maxwell evolution equation of resonator dynamics: temporal coupled-mode theory revisited*.
* Local independent selected-model verifier **14/14 pytest PASS**; committed checker added to `scripts/check_smith_filsinger_dynamic_replenishment.sh`. No exact-head Agda compiler run, no calibrated Filsinger measurements. F15/R3 and rain-cooling F16 OPEN.
* Crucially, the environmental-power steelman is a **dynamic Sun/Earth source**, possibly ample enough to pay MW pump expenditure if physically transferred. The passive half-space Thevenin matched-load example is a **null** not a bound on solar-wind Poynting flow or nonlinear, source-responsive, spatially distributed power.


## 2026-11-17 source-first Maxwell value-of-information cut (F10/F13-F16)

**Full detailed source/verification record:** [SmithFilsingerMaxwellValueAndSourceFirstCut20261117.md](SmithFilsingerMaxwellValueAndSourceFirstCut20261117.md). New exact-head code, tests, original missing-evidence schema and conditional acceptance runner are on PR #1524.

**Highest alpha decision:** calibrated source-to-terminal work precedes a large 3D Earth/ionosphere Maxwell model. Spatial Maxwell/plasma is worth implementing after one selected apparatus has authentic geometry/materials, loaded natural-source response and a physical anomaly which a reduced DC/1D/port law cannot explain. It cannot produce a measured natural generator by choosing a boundary amplitude. Acoustic 7.8kHz is not an electrical phase measurement.

| Target | New restricted result | Strict remaining original-world wall |
|---|---|---|
| F10 / R2 | Exact symbolic local vector Poynting + nonlinear time-varying polarization + Hall/Pedersen/neutral-wind + generator signed work; 8/8 tests | Full calibrated causal Maxwell/plasma/soil/material source operator |
| F13 / P2 | Crowley 2011 Eq.25,28–37 isolated spherical fair-weather collector physics; 2m/0.1m conditional example ~0.1483 nW, 2.97 pA and 6.74e13 Ω; unit/model negative controls | Actual Filsinger electrodes/plate source identity and voltage/current geometry; no global 250kV assigned locally |
| F14 / R1 | Original-load-only energy balance rank 1/nullity 3; drive, natural supply and donor depletion counterworlds indistinguishable at load | Original actual pin graph, simultaneous driving/source/shunt/load/switch, acoustic waveforms and one parameter set |
| F15 / R3 | Conservative signed v*i interval receiver; requires independent source identity and full stored-state return; passing external flags is not an empirical receipt | Positive independently replenished natural work at selected original port over whole cycles |
| F16 / Q6 | Two causal models give identical natural electric-field/rain observations but differing controlled effect; 2021 paper establishes observational relation only | Actual controller→cloud electric-field transfer, causal rain/drizzle response and local cooling with controls |
| D1/D2 | 4/4 Git blobs parity; 33/33 new tests, 99/99 combined local source-equivalent tests | Pinned Agda kernel, original-world evidence admission and same-head CI |

**Source correction:** Crowley calls pi*d² a sphere's geometric cross section while defining d as diameter; physical projected disk is pi*d²/4 (fourfold convention discrepancy). Eq.28 Isc, Eq.35 R and Eq.37 Pmax do not change. Neither Crowley sphere nor earlier 1D slab are measurements of Filsinger's actual grounded/portable collector. Source: https://electrostatic.com/research/c11theatmos/c11atmo.html, 2026 Borok https://doi.org/10.1016/j.asr.2026.01.090, 2021 cloud raindrops https://doi.org/10.1029/2021GL093577, Tinsley https://doi.org/10.1029/2021JD035954.

**Execution:** scripts/check_smith_filsinger_source_first_maxcut.sh; 99 local targeted model tests **PASS**, all four new code/test blobs byte-identical to branch, no exact-branch CI nor Agda proof checker. No original same-unit physical gate is closed. All S0/P1/P2/R1/R2/R3/D1/D2 remain **OPEN (0/8)**. Retain W/B/N source regime distinctions and source-qualification; no ESD edits and no premature TOE promotion. F16 does not authorize weather intervention or indicate local/global cooling gain.


## 17 November correction: genuine Agda F10/F13/F14/F15/F16 welds

**Previous work was numerical/pytest modelling, not the requested formalisation.** The new proof-based analysis and actual Agda source signatures are in [SmithFilsingerFormalWeldMaxCut20261117.md](SmithFilsingerFormalWeldMaxCut20261117.md). This update supersedes the previous simulation-focused emphasis for formal gate tracking.

**New Agda consumer** DASHI/Physics/Motors/SmithFilsingerSourceMaxwellBoundaryWeldExact.agda imports and explicitly connects the existing MaxwellExteriorCalculusAdapter, TimeIndexedTransfer MemberState/RetardedFlight, ReflectedPortBidi original-source config, SunEarthCoupledSource port/regime, MidpointPhaseWork signed incident/outgoing real-work port, FinitePhaseMatching source-off and complementary-phase theorems, and ReplenishedCycleCap original stored-state cycle. Dependent SourceOwner prohibits swapping Smith compiled, filmed Filsinger Earth and proposed Filsinger portable hardware. FormalFieldToPort connects the original member and symbolic curvature carrier to one source-qualified boundary without claiming that the Maxwell source/Hodge PDE is solved.

**Genuine derived F15 lemma:** signedPortBalanceAfterFullStoreReturn, by exact Agda Nat semiring normalization plus cancellation, deduces natural net incoming + controller net incoming = useful load + loss from TWO original signed incident/outgoing laws, original MidpointTwoPortWorkWindow conservation, and full store return. The equality is NOT assumed as a second independent cycle law. signedNaturalAndControllerWorkPaysSamePortLoad instantiates this result; signedPortLoadBoundAfterStoreReturn bounds the very same load; sourceCapTransfersToSameOriginalPort transports an independently admitted natural-access cap through an exact port-identity witness. Source-free natural input cannot yield positive net natural work; finite flight does not arrive before launch.

**New Agda consumer** DASHI/Physics/Motors/SmithFilsingerCloudCausalWeldExact.agda explicitly preserves observed-natural-association evidence tiers for the electric field/raindrops and cold-pool papers; composes same-source controller-to-cloud, cloud-to-droplet, droplet-to-rain and rain-to-local-cold-pool arrows as conditional typed evidence; proves observationalCloudRainAssociationDoesNotWeld via observationally identical worlds with distinct intervention effects. Global climate promotion is separately conditioned, and original source-specific F14 acoustic/electric regime demands its own evidence.

**Acceptance boundary:** Agda proof source committed, but no Agda/Nix compiler is available in this session and NO kernel acceptance is claimed. scripts/check_smith_filsinger_formal_weld_agda29.sh is the pinned type-check target. Earlier 99/99 Python tests are irrelevant to kernel acceptance. The symbolic Maxwell adapter remains explicitly unpromoted: complete physically sourced 3D R2/F10, calibrated original source F13/P2, original combined F14/R1, sustained original-work F15/R3 and actual cloud causation F16 are PHYSICAL OPEN. No ESD edits and no premature TOE import.


## 17 November: nonlinear carrier / causal admittance / finite-source max-cut continuation
**Implementation:** [SmithFilsingerNonlinearRetardedSourcePortMaxCut20261117.md](https://github.com/chboishabba/dashi_agda/blob/research/sun-earth-coupled-source-20261116/Docs/research/SmithFilsingerNonlinearRetardedSourcePortMaxCut20261117.md), `scripts/check_smith_filsinger_nonlinear_retarded_source_port.py`, `scripts/test_smith_filsinger_nonlinear_retarded_source_port.py`. Existing original-world `source_first_original_evidence_contract_20261117.json` is not modified; separate *model-only* schema receipt added.

**F10-PLASMA conditional:** Electron continuity with independent pair-creation, attachment and recombination rates; `U_ion=Vch Epair n`, explicit paid ion-pair creation, ionisation loss, controller auxiliary input, and finite electronic channel resistance. Exact algebraic power/storage cancellations are model identities, and symbolically checked. This does not prove a complete air-plasma chemical/thermal/ion inventory (F10-3D OPEN).

**F13-RET selected:** Positive-real Foster trial port with signed Debye and Lorentz state energies and dissipations. This is a *surrogate* for an unknown waveguide impedance, not a fitted 3D Maxwell/soil/ionosphere Green operator; positive real excludes *passive* negative dissipation for state-returning cycles, not externally energized nonlinear source response.

**F13-NL selected:** `G_series=Gch Gext/(Gch+Gext)`. Channel `Gch∝n` may change substantially without raising the composite series limit beyond `Gext`. Cubic toy `I(V)=G0 V+γ V³` gives `Gdiff=G0+3γV²` versus `Gpower=G0+γV²`; different quantities.

**Finite source backaction:** Added finite upstream capacitor state `Cs Vs'=g_recharge*(Vexo(t-delay)-Vs)-I`. Natural signed replenishment, receiver load, exterior/channel heat, ion creation/loss, controller auxiliary input and all final storage tracked. The static external source is now an explicit *causal exogenous forcing of a finite reservoir*, not a fictitious fixed infinite battery. It remains a conditional 0D/1D nonlinear analogue and does NOT incorporate ionospheric Hall/Pedersen geometry or upstream Sun–Earth magnetospheric power.

**100× gain metric:** model reports `Wload/(Wcontroller+Wion_pair_creation)` and threshold; **neither sufficient nor a source validation** without actual source power, *every* pump cost (plasma thermal, chemistry, bridge), complete return cycle, error bars and physical source admittance.

**R2/R3/F15 physical frontier remains OPEN:** exact 3D soil/air/ionosphere Maxwell, fitted electron/ion kinetics, independently measured real source work under source backaction, controller+bridge losses and fully restored repeatable cycles. No original-world gate passed. The full committed test suite has no exact-head replay/kernel receipt in this runtime; selected SymPy identities were independently verified.

**Caution:** Externally sourced solar power could be orders of magnitude above fair-weather local-collector power, but only a causal interface with a source-supported phase/current/aperture and measured reservoir replenishment can establish that for the actual device.


## 17 November second Agda cut: internal Maxwell/material work-port cancellation

The current formal maximum cut is **not a simulation**. New owner DASHI/Physics/Motors/SmithFilsingerMaxwellMaterialEnergyCutExact.agda proves a generic shared-interface cancellation and composes two independently witnessed, same-original field-source and material-receiver work laws. It explicitly retains net natural-source input (not gross incoming waves), net driver work, paid material modulation, recovered modulation, electromagnetic/radiative loss, dissipative material loss, field storage and material storage.

The Agda source provides cancelSharedInterface, fieldMaterialCombinedWork, fieldMaterialRepeatableWork, fieldMaterialLoadBoundOnRepeatableCycle, netNaturalUnderExistingAdmittedCap, and sameOriginalMaterialCapWithControllerAndModulator. The resulting *conditional* selected-load inequality is: useful original load <= independently admitted net natural cap + net powered controller work + explicitly paid material modulation. This cannot hide material work in a purported external source or count field/material interface flux twice.

Original physical Poynting/current and nonlinear material conservation identities are still uninhabited physical hypotheses. The separate #1521 DispersiveMaterialPortExact donor is not present on #1524's branch; avoid a fake import and perform exact cross-branch join after the source trees converge. Full F10/R2 Maxwell, F13/P2 source operator, F14/R1 original history, F15/R3 replenished natural work, F16 actual cloud intervention remain OPEN.

Pinned Agda acceptance script scripts/check_smith_filsinger_formal_weld_agda29.sh now targets **three** formal modules; **Agda/Nix unavailable here**, so none of the new source-authored proofs is claimed kernel-checked. Full detailed signature/proof dependency in SmithFilsingerFormalWeldMaxCut20261117.md.


## 17 Nov Agda direct donor-to-field/material typed weld

The original #1521 canonical DispersiveMaterialPortExact.agda source has been *reused byte-for-byte unchanged* on #1524: same Git blob fb4039927678b370f359b3151c1fc2a2286c33ab on both branches. All extensions are in new DASHI/Physics/Motors/SmithFilsingerDispersiveMaterialWeldExact.agda, which imports the actual donor, not an abstract surrogate or numerical simulation.

The new Agda proofs derive originalDispersiveRepeatableWork from the existing MemoryMaterialPortLedger.fullBalance with **environment and material storage individually restored**, then prove originalDispersiveLoadBound. CanonicalDispersiveSameObject ties the donor's natural recharge to **net** natural work, driver work, paid modulation, returned modulation, real load, field+material loss, and all four initial/final source and material storage identities on one selected original configuration. donorOriginalLoadBelowAdmittedNaturalCap proves the donor's same-original load cap. Crucially, donorStorageReturnTransfersToSplit derives the split full-store return from donor receipts and matched storage states; canonicalDispersiveFieldLoadBelowNaturalCap instantiates the F10 field/material shared-work cancellation and resulting F15 bound **without re-assuming storage restoration**.

**Formal acceptance:** pinned script check_smith_filsinger_formal_weld_agda29.sh now includes FOUR new proof consumers and the original material donor; no Agda/Nix executable is available here, so source-authored theorems are NOT yet kernel checked. Physical F10/F13/F14/F15/F16 original-world gates remain OPEN and no empirical natural source is fabricated.


## 17 November maximum-cut — distributed finite-source / plasma topology (latest)

**New executable owner:** `scripts/check_smith_filsinger_distributed_causal_energy.py`; regression `scripts/test_smith_filsinger_distributed_causal_energy.py`; source/acceptance evidence `Docs/research/SmithFilsingerDistributedEnergyMaxCut20261117.md` and `Artifacts/smith-filsinger/distributed_source_plasma_maxcut_20261117.json`. Integrated into existing `scripts/check_smith_filsinger_dynamic_replenishment.sh`. No ESD changes or new parallel theorem graph.

**Completed selected-model mathematical cut:** N-node finite LC/telegrapher analogue, N−1 link-current energy, finite rechargeable source storage, causal delayed stipulated exogenous source waveform, carrier number/ion pair energy, source feed/line/bridge/load resistive loss, signed recharge work and paid ionization/controller energy. All interior link powers cancel by exact discrete telescoping; SymPy identity checked for N=3,5,8 and local **16/16 tests PASS**. The continuous semidiscrete ODE is NOT a strict light-cone Maxwell PDE.

**Adversarial source-connected control:** For the same carrier amplification ~4.29×, a plasma *shunt* reduced delivered load by ~2.25%; a plasma *series link* increased load by ~110.31% under its own stated parameters. This establishes **topology matters**. Neither configuration produced net useful work after assumed ion creation + controller cost, and source/storage failed full return. No sustainable natural harvest or original Filsinger netlist identity is claimed.

**F10 remaining:** Formal all-N induction, real Maxwell 3D space/matter/Hall/Pedersen/neutral-wind and complete plasma chemistry, plus physical effective moving channel interface. **F13 remaining:** measured conductor/collector topology and effective source-connected input admittance; actual causal soil/atmosphere/ionosphere Green operator (not fitted from our synthetic source); nonlinear return path and replenishment. **F15/R3 remaining:** independently verified net natural source work over source-restored matched repeated cycles after all bridge/ion/thermal/controller costs; 100× benchmark assessed only then. F14 original integrated regime and F16 cloud/cold-pool causal link remain distinct OPEN.
 
**Next high-alpha tranche:** (1) promote finite spatial telescoping energy and source ownership into the pre-existing Agda Maxwell/source port graph, with pinned kernel check; (2) construct selected field-to-port operator subject to actual source/geometry data, nonlinear series-vs-shunt interpretation and causal time-phase transfer; (3) source-backed same-original sustained-cycle acceptance; (4) conditional atmospheric branch. No amount of symbolic algebra can supply missing original P1/P2 measurement.


## 17 November — all-N spatial work plus retarded-time Agda weld (latest)

**Source and exact proof surface:** [SmithFilsingerSpatialRetardedAllNFormalMaxCut20261117.md](SmithFilsingerSpatialRetardedAllNFormalMaxCut20261117.md). New canonical consumers:

- `SmithFilsingerSpatialPortChainExact.agda`: `SpatialCell`, dependent `SpatialChain`, `spliceSharedWork`, `spatialChainWorkBalance` **for all finite N**, `spatialLoadBoundedByAdmittedInputs`, `sourceFreeSpatialChainHasZeroLoad`; concrete two-cell witness. No duplicate Maxwell source.
- `SmithFilsingerTimedSpatialPortChainExact.agda`: reuse canonical `RetardedFlight`, all-N `allTimedPathsArriveAfterLaunch`, `timedSpatialEnergyConservation`, two-flight 1→3→7 witness. Finite causal clock ≠ Maxwell light-cone proof.
- `SmithFilsingerSpatialSourceBoundaryWeldExact.agda`: SOURCE-INDEXED `SpatialToOriginalSourcePort` uses original `SelectedBoundary` / `FormalFieldToPort`, requires original physical field-to-port input AND output work identifications; derives matching selected original-port law from all-N cells. Missing measurements remain explicit, not silently constructed.

**Execution:** local **900/900 independent exact integer finite-chain checks PASS** (N up to 64); earlier local **16/16 distributed LC/plasma tests PASS**. Added `scripts/test_smith_filsinger_spatial_chain_exact.py` to existing `check_smith_filsinger_dynamic_replenishment.sh`, and the three new Agda owners to existing `check_smith_filsinger_formal_weld_agda29.sh`. **No exact-head GitHub combined run or pinned Agda 2.9 verification**; D1 OPEN. The reported 900 checks are an independent arithmetic replay, not compiler-proven.

**Gate movement:**
- F10 *finite spatial algebra*: all-N Agda proof candidate source authored, no pinned kernel. **F10 actual nonlinear 3D Maxwell/material/Hall–Pedersen R2 OPEN.**
- F02 finite causal time: source-authored all-N ordered flight. **Physical phase at interaction region and retarded Green operator OPEN.**
- F13 original source: stricter same-source indexed boundary work interface; **actual solar/soil/ionospheric impedance, geometry, full wave Maxwell solution P2 OPEN.**
- F15/R3: existing finite-source matching/replenishment gating intact; **independently measured source work over fully restored cycles OPEN**.
- User's steelman retains arbitrary source size and possibility of large pump expense where independently measured source work dominates; the source-free and finite-donor counterexamples stay in acceptance.

**Next highest-alpha physical route:** pinned kernel first, then selected actual source/geometry/terminal waveform identification, causal Maxwell material port with independent natural-source boundary and full return. Avoid using random finite-chain receipts to stand in for original astrophysical power access. No ESD edit or unverified TOE promotion.
