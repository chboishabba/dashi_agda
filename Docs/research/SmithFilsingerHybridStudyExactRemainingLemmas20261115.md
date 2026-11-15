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
