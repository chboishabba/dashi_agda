# Smith/Filsinger hybrid circuit, four regimes and literature BIDI max-cut
**2026-11-15 · continuation of merged PR #1507 and #1509. Not a claim of environmental power or a same-device build.**

## Canonical state, not isolated anecdotes
Use `Circuit36927ComponentGraphExact`, `Circuit36927SwitchStateExact`, `Circuit36927RecoveryEnergyBoundExact`, `SmithFilsingerTimeIndexedTransferExact`, `MaxwellExteriorCalculusAdapter` and `SmithFilsingerHybridRegimeStudyBidiExact`. Treat ZVS as the driven pump and the spark-gap as a capacitor-bank dump/switch, not a new independent source.

One **time-indexed, source- and pin-qualified system**: powered oscillator→bank/spark dump→mutually coupled coil/core/capacitor/diode/ground circuit→natural and radiative Maxwell ports→mechanical/air microphone observers. Each member has distinct phase, loss, nonlinear state, propagation delay and signed energy flows. Preserve Smith Figure 10, Figure 11, later Figure 40 and Filsinger's different reels separately.

## Real source audio regime partition
- **35–38 s activation:** complex short transient (median 7.7–7.9k intensity +9.28dB vs 39–50s), not a steady tone to force into an FM model.
- **Driven/hunting (~38–60 s):** elevated 52–55s (+2.74dB), moving carrier roughly 7785→7824Hz, nonidentical FM and AM, 3–5 and 6–10Hz modulation projections.
- **Deep nulls:** near 39.546, 41.738, 43.596, 47.064, 51.316, 53.000, 55.102s; some exploratory nearly π phase changes; post-hoc 1.922s recurrence weakens with spacing-conditioned null (p around .055–.08). A continuous two-mode phasor explains nulls without forcing oscillator shutdown; cannot yet exclude gate/switching/AGC.
- **Switch-off ~60.3–60.7s:** 7.6–7.95k carrier loses dominance; upper 7.95–8.4k band rises in *relative* amplitude from .014× (59.7–59.95s) to .34× (60.4–60.6s) to 12.16× (60.7–60.9s); a weaker 5.5–7.5k band is present. Carrier-band log-amplitude fit τ≈0.0998s, R²≈.697 (60.34–60.78s): observational pseudo-decay, NOT measured electrical tank Q. Other source sounds may overlap. A single damped fixed-parameter oscillator has constant damped frequency; the full shutdown is potentially changing/multiple modes, not yet one proven down-chirp.

## Closed LOCAL mathematical subgates (source authored, not all Agda kernel checked)
| ID | Exact scope | Status / acceptance |
|---|---|---|
| `H01 phasorNullMinimumExact` | Symbolic |a+b exp(iφ)|²=a²+b²+2ab cosφ, min (a−b)² at π | local SymPy PASS; physical cause not proven |
| `H02 freeSingleModeRingdownFixedFrequencyExact` | Homogeneous q''+2γq'+ω₀²q=0 admits decaying single damped frequency | local SymPy PASS; one fixed mode assumption |
| `H03 twoModeNonlinearPumpEnergyIdentityExact` | dH/dt=driver work+natural work+modulator work−losses for x²y mixer | local SymPy PASS; material coefficients not identified |
| `H04 pumpOffPassiveWorkBoundExact` | Driver-off AND natural-source-off AND parameter-static implies no growth in stored energy | existing Circuit36927 boundary owner + local identity |
| `H05 sourceStudyNotExperimentalEvidenceExact` | Patent, source narrative and experiment are distinct evidence tiers | new Agda source, NOT kernel checked |
| `H06 twoHopEnvironmentalFlightExact` | F-region heating→magnetosonic transfer→E-region Hall current needs two nonnegative flight legs | Agda source + Python PASS; time constants not identified |
| `H07 postPumpStateSeparateFromDrivenExact` | Switch-off regime distinct from powered operating state | Agda source, NOT kernel checked |
| `H08 acousticCannotIdentifyNaturalSourceExact` | An acoustic signature alone does not uniquely identify signed source work | existing Agda owner, not hardware claim |
| `H09 threeRegimeSourceFeatureReplay` | 35–38s onset; 52–55s hot; 59.45–61.35s shutdown spectral bands | local original-audio replay PASS |

## Exact remaining original-world gates
| ID | Exact scope | Status / acceptance |
|---|---|---|
| `A1 originalCommercialMidpointRectifierPinWeld` | Selected Filsinger commercial schematic with exact diode polarities, transformer midpoint, spark dump, white/blue/green capacitors, shunt and meter pins | physical reel terminal continuity |
| `A2 selectedDriverElectricalClockEqualsAcousticMode` | Synchronous switching/V(t)/I(t)/mic phase; actual electroacoustic transfer function | real calibrated same-session traces |
| `A3 sameCircuitNonlinearCoreDiodeCapMaterialWeld` | MOSFET C(V), B-H hysteresis and saturation, diode recovery and shunt bias effects in the SAME circuit | component selected parameter/electrical sweep |
| `B1 oneSystemOnHotNullOffInverseFit` | One parameter set fits startup, hot 52–55, seven nulls, and pump-off using same state and held-out events | cross-validated hybrid model with uncertainty |
| `B2 nullPhaseVsFeedbackGateIdentifiable` | Compare two-source cancellation, real supply blanking, dynamic switching and microphone AGC | model selection on complex source signal and repeat captures |
| `B3 pumpOffModalPoleAndStoredEnergySameState` | Separate 7.8k line, upper post-off peak to 8.26k and lower 5.6–7.3k content with multiple poles, no invented continuous chirp | post-off multivariate pole estimate and matched control |
| `C1 causalFilsingerToEnvironmentGreenOperator` | Retarded ground/air/ionosphere Maxwell kernel; physically distinct port speeds, conductive and plasma memory | same-object source and receiver geometry |
| `C2 sourceAttributedNonlinearTwoStageFieldToHallWeld` | Physically dimensioned thermal conductivity, magnetosonic and Hall coupling in correct materials | no import of HAARP parameters as tabletop coefficients |
| `C3 actualExtraEnvironmentalWorkFromSamePorts` | Signed natural, pump, driver, radiated, thermal, storage and load work through whole cycle | same-object calibrated ports and source controls |
| `D1 AgdaHybridRegimeAndStudyKernelAcceptance` | Agda/Nix exact-head typecheck of new module and existing dependencies | kernel receipt required |
| `D2 sameOriginalObserverAndSourceAttributionBidi` | Separate patent claim / academic observation / original Smith diagram / Filsinger reel / derived code result | explicit source-to-theorem promotion witness |

### Study to theorem contracts: never rediscover or silently promote
The machine-readable `Artifacts/smith-filsinger/source_study_contracts_20261115.json` carries **22 individually linked entries** (8 theory/experimental papers, 11 patents/applications, 3 original Filsinger reels). Each keeps author/source scope, mechanism, evidence tier, and `verified_same_apparatus=false`. The Agda `Study` constructors and `evidenceTier` function preserve paper→patent→reel boundaries.

**Physical mathematical kernels, explicitly conditional on selected media:**
1. **Golkowski et al. 2010 magnetospheric whistler echoes** ([DOI](https://doi.org/10.1029/2009JA014610)): nonlinear delayed amplitude/phase response; experimental input-amplitude/onset sensitivity. Formal target: retarded echo operator and complex phase trajectory, with independently supplied wave-particle energy.
2. **Cohen et al. 2010 geometric modulation experiment** ([DOI](https://doi.org/10.1029/2009JA014410)) and **Cohen et al. 2011 model/satellite comparison** ([DOI](https://doi.org/10.1029/2010JA016194)): temperature-dependent conductivity, Hall/Pedersen current and spatial phase; reported 5–7dB is a *specific modeled heating comparison*, not Filsinger's output gain.
3. **Papadopoulos et al. 2011 theory** ([DOI](https://doi.org/10.1029/2011GL047368)) and **ICD experiment** ([DOI](https://doi.org/10.1029/2011GL049263)): source-specific causal F-region diamagnetic current→magnetosonic field→E-region Hall current secondary radiator. Encode `t0+τ_F→MS+τ_E`; link to Maxwell only with the proper constitutive and observed source currents.
4. **Foster & Finch 1974** ([DOI](https://doi.org/10.1126/science.185.4147.256)): absorbed microwave field→thermoelastic pressure *in matter*, a different observer than free-air microphone.
5. **Kim et al. 2026** ([Nature Communications](https://doi.org/10.1038/s41467-026-73604-0)) and **Kim/Zhong/Jing 2026** ([DOI](https://doi.org/10.1109/TUSON.2026.3689544)): nonlinear air difference-frequency field with acoustic and elastic modes / passive metasurface phase focus.
6. **Patents** [US12185058B2](https://patents.google.com/patent/US12185058B2/en) (carrier versus sideband phase), [US20180310111A1](https://patents.google.com/patent/US20180310111A1/en) (virtual-source propagation), [US20170289722A1](https://patents.google.com/patent/US20170289722A1/en) (localized parametric audio), [US6470214B1](https://patents.google.com/patent/US6470214B1/en) (RF-auditory patent) are claim/architecture analogues, not measured Smith effects.
7. Source candidates [Tesla US787412A](https://patents.google.com/patent/US787412A/en), [Hings US3361957A](https://patents.google.com/patent/US3361957A/en), [Plauson US1540998A](https://patents.google.com/patent/US1540998A/en), [Earth Energies 675](https://patents.google.com/patent/US20150102675A1/en) / [676](https://patents.google.com/patent/US20150102676A1/en), [Ion collector US9331603B2](https://patents.google.com/patent/US9331603B2/en), and [Smith Mexican application](https://patents.google.com/patent/MXNL02000035A/en) retain actual provenance. No patent alone certifies delivered power.

## Mathematical welds to reuse
For an assumed paired acoustic response, `|a+b exp(iφ)|²=a²+b²+2ab cosφ` has minimum `(a−b)²` at π. This **explains possible nulls**, not proof of two specific vibrations. For homogeneous fixed-parameter RLC post-off, `q''+2γq'+ω₀²q=0` has `exp(−γt)cos(sqrt(ω₀²−γ²)t)`; multi-peak spectra require a richer observation model. For nonlinear source-coupled modes with `H=(vx²+vy²)/2+kx(t)x²/2+ky(t)y²/2+g(t)x²y+β(t)x⁴/4`, `dH/dt` must record driver/natural/modulator work separately from damping and end storage. **All three identities** checked via exact SymPy in a self-contained source module.

**Acceptances:** local full replay 13/13 pytest with actual 105.7959s MP3; original MP3 is not redistributed. This branch's Agda module is source-authored and **not kernel-checked**; source-specific electrical measurements, full Maxwell plasma solution, and actual net environmental work remain open.

**Milestone order:** P0 (this PR) regime+study proofs and reproducible audio; P1 one-param-set physical four-regime inverse fit and pin-continuity weld; P2 selected full retarded Maxwell/plasma boundary and natural work; D1 pinned kernel check as independent acceptance. Do not claim completion of P1/P2 from a synthetic audio example.


## Source-specific forward-operator audit (seven more passing local tests)
The source-kernel comparison is now executable at `scripts/check_smith_filsinger_study_forward_operators.py`. Original authors' field results are *separate from our synthetic mathematics*.

- **Golkowski et al. 2010** nonlinear magnetospheric echo growth. Conditional unchanged-threshold exponential inverse: a 14 dB reduction of seed amplitude delays onset by approximately one second, yielding **g = ln(10^(14/20)) / 1s ≈ 1.612 s⁻¹** for that chosen toy growth law. It is not a measured actual plasma g, and never a Filsinger coupling coefficient. [DOI](https://doi.org/10.1029/2009JA014610).
- **Cohen et al. 2011** time/spatial modulation. The **5–7 dB source-reported modeled injected-power improvement** is a 3.16–5.01 power ratio for the stated heater comparison; not a universal efficiency multiplier. [DOI](https://doi.org/10.1029/2010JA016194).
- **Papadopoulos / ICD 2011** causal F-region→MS wave→E-region Hall current: a two-hop retarded discrete model explicitly distinguishes independently supplied natural Hall current. [Theory](https://doi.org/10.1029/2011GL047368) · [experiment](https://doi.org/10.1029/2011GL049263).
- **2026 nonlinear acoustics** square-law source shows the acoustic difference-frequency phenomenon under hypothetical low-pass observation; no electromagnetic Earth coupling inferred. [Nature Communications](https://doi.org/10.1038/s41467-026-73604-0).
- **Foster/Finch 1974** abstract causal thermoelastic pressure from a specified absorbed-heat history; not a free-air microphone or exposure design. [DOI](https://doi.org/10.1126/science.185.4147.256).

Updated local full replay and symbolic/model acceptance: **20/20 tests PASS**, 22 separately attributed source-study/patent/reel records. GitHub-head exact source scripts and Agda kernel are still not independently checked in the pinned toolchain. Open original-world gates A1–D2 above remain unchanged.


## 2026-11-15 exact-head source continuation: unobscured onset and TWO delayed pump-off peaks

Original user attachment `image.png` has a bar/overlay obscuring an apex. The exact hidden crest **cannot** be reconstructed by extrapolating screenshot pixels. Generated a separate unoccluded original-audio waveform and band-resolved source plot. Provenance: original `ReelAudio-93787.mp3`, fs=44100Hz, 105.795918s, SHA256 `573eb6b205bdf1c29cb33fad5e28eeb00dee18c5566aee7290679aac0396c4c6`. This is **microphone acoustic energy**, not measured V/I, not the external environment's Poynting flux.

### Source-acoustic subgates now numerically closed
- `pumpoffUpperAbsoluteAmplificationSourceExact` (**acoustic observation**): changing nperseg to 2048, pre-off 59.7–59.95 versus upper-dominant 60.7–60.9 yields **19.65× absolute increase** in the upper 7.95–8.4kHz acoustic band and **31.83× decrease** in carrier 7.6–7.95kHz. Lower 5.5–7.5kHz rises **12.90×** from pre-off to 60.4–60.6. The rise is NOT solely caused by dividing by a weak carrier. No watt inference.
- `pumpoffTwoPeakWindowRobustSourceExact` (**acoustic observation**): upper-band strong peak times survive five STFT window resolutions nperseg=1024,1536,2048,3072,4096. First peak ~60.403–60.417s; next ~60.708–60.716s; difference **0.296–0.308 seconds**. These are observations, NOT proof of a global echo flight time.
- `pumpoffOneSourceTwoResponsePathConstructiveExact` (**specified forward kernel**): single pump-off trigger with two causal nonnegative Erlang-like response kernels of different shapes `G_j(t)=1_{t>=t_j} exp(k_j[1+ln((t-t_j)/tau_j)-(t-t_j)/tau_j])`. A common first transition at **60.323s**, extra effective delay **0.303s**, fits the upper-band envelope with **in-sample R²=0.970**. The same data admit a two-independent-acoustic-pulses model R²=0.917 and a one-causal-response model R²=0.392. The two-path model has **9** fitted parameters versus 7 for independent pulses and 5 for one response: no physical identification from a fit alone.
- `pumpoffTwoPathBlockedHoldoutSourceExact` (**exploratory model comparison**): five contiguous holdout blocks yield mean held-block MSE 0.0466 (two paths), 0.0635 (independent events), 0.2259 (single response), with several poor fold-specific scores. STFT windows are highly overlapping and results should **not** be treated as independent significance tests.
- `pumpoffAcousticOriginIdentifiabilityNegativeExact`: a non-injective acoustic source map can associate the **same two-peak observation** with one switched system with two delayed pathways OR two independent acoustic events. The source alone cannot force the first mechanism.
- `postPumpUsefulBound` (**source-authored Agda only**): if driver, natural input and modulator contribute no work after switch-off, an initial Nat-grid stored-energy balance implies `usefulOutput ≤ initialStored`. Its isolation premise is explicit; not asserted for a real Earth-coupled system. Likewise `sameInitialEventForTwoPaths` and `first/secondPathCannotArriveBeforeSource` reuse `RetardedFlight`. Module `SmithFilsingerPumpOffDualPathExact.agda`; **Agda kernel acceptance PENDING**.

Scripts: `scripts/check_smith_filsinger_pumpoff_source_models.py` for original audio, and local package source replay with unobscured line plots and both candidate fits. **11/11 new independent local regression checks PASS** (separate from previous 20/20), and exact source-required script locally executed. No new phantom source-port measurements.

### Original-world gate refinement (do not re-open completed subgates)
`B3-OBS1/B3-OBS2/B3-MODEL` above are now locally **CLOSED** at the specified acoustic/model level. Original **B3-PHYS** remains OPEN: identify same-apparatus circuit eigenpoles, calibration and initial stored energy. `B1` (one same physical parameter set for startup/hot/null/off), `A1/A2/A3`, `B2`, `C1/C2/C3`, `D1/D2` remain OPEN as original-world gates. In particular **a 0.303s acoustic response delay is not an Earth–ionosphere propagation-time measurement**; it may include switch dynamics, mechanical resonance, noise, audio capture, multiple wave paths or feedback. Do not infer a source scale from that alone.

### Immediate acceptance order
1. P0a: run pinned `scripts/run_agda29_parallel_check.sh DASHI/Physics/Motors/SmithFilsingerPumpOffDualPathExact.agda` and existing inherited owners; no Agda kernel pass claimed yet.
2. P0b: original full-audio source replay and multi-window tests against the exact merged/PR head, preserving the SHA256 and amplitude/phase observations.
3. P1: single nonlinear ZVS–spark-dump–cap-bank–split-coil–rectifier state fit across **all** regimes. Include electromechanical observation and a physically distinct Earth/ionosphere return, rather than selecting post-off fit parameters independently.
4. P2: pin-level source continuity, real measured switching and multichannel electrical/acoustic traces, Maxwell–plasma field response and signed source/driver/load work admission. Neither patents nor prior study results substitute for these physical receipts.


## 15 November — B3-SPEC same-source *spectral* distinction of two fitted response kernels
Original source SHA256 `573eb6b205bdf1c29cb33fad5e28eeb00dee18c5566aee7290679aac0396c4c6` (`ReelAudio-93787.mp3`). Fit coefficients derive from the **same-original 60.26–61.20s upper-band acoustic envelope**. `scripts/check_smith_filsinger_two_kernel_modal_source.py` fails closed on changed audio SHA. An accompanying unoccluded local image compares normalised upper-band spectral density at the two peaks with the fitted *nonoscillatory* causal kernels.

**Numerical subgate B3-SPEC closed locally (4+1 consistency checks)**:
- Common envelope trigger time 60.32281s, fitted first peak 60.41427s and second peak 60.71659s; separation 0.30231s, secondary-path *effective onset offset* 0.30322s. These two time intervals are not automatically electrodynamic time-of-flight.
- Same-window-length 100 ms FFT/Welch analysis, 7.95–8.4 kHz band at first 60.36–60.46s and second 60.66–60.76s. First acoustic spectral centroid **8173.66 Hz**, spectral flatness **0.66571** and entropy **0.92178**; second centroid **8028.10 Hz**, flatness **0.00908** and entropy **0.54143**. Later acoustic response is considerably more tonal, even though both appear in the same *upper-band* observation. First is broadband and could include switching/contact/mechanical excitation; second plausibly a selective resonant ring. **No actual circuit eigenmode is yet identified.**
- Phenomenological envelope kernels `h_j(u)=H(u) A_j (u/tau_j)^k_j exp[k_j(1-u/tau_j)]`. Fitted `tau=(.091463,.090555)s`, `k=(3.79543,1.46246)`. Their late-time exponential scales `tau/k` are **.02410 and .06192s**, respectively. These are observable envelope-decay scales, **NOT resonant periods, Q values or individual R/C product identification**. Noninteger `k` cannot be read as exact number of physical stages; a single component can have several modes.
- A common drive-off transition with two distinct response kernels is a valid *reduced-order input–output map*. Identifying physical nodes needs complex post-off mode fits from `ReelAudio` plus the selected Smith/Filsinger component graph. The upper-band early broadband versus late tonal signature favours considering different response/mode channels; it does NOT prove two separate hardware pieces or a planetary reflection.
- `0.303s` is a **response offset**, corresponding to approximately 3.30 s⁻¹ as a reciprocal time scale, and is not itself a measured 3.3Hz oscillation or 7.83Hz Schumann resonance. Do not infer a frequency merely by taking the reciprocal of a fitted peak separation.

**New exact outstanding lemma name**: `sameCircuitPumpOffModalResponseOriginWeld` — from one selected circuit/netlist, derive two identified complex poles/eigenvectors with energy residues and acoustic observation coefficients whose predicted original onset, tonal spectrum and amplitude envelope match the source. Existing `SmithFilsingerPumpOffDualPathExact` supplies only causal pathways and an energy upper bound. Requires full circuit identity and electrical/acoustic calibration for physical closure.

The one-switch/two-response acoustic spectrum is an empirical **model-discrimination bridge**, not a claim that independent environmental real work entered the circuit. Do not reopen already-closed general resonance or nonlinear mixing lemmas.
