# Earth-port multirate reverse-solve / C3 geometry roadmap (2026-11-20)

Continuation of SmithFilsingerPhaseDeliverablesExactRemaining20261116.md (F01–F16 and Q0–Q6 unchanged); SmithFilsingerMultirateSchumannMaxCut20261120.md; switched ADE and harmonic transfer max-cuts. PR #1524 parent 950b35491af77afc179ce0bf7b9fb4c8eefdad. User-origin steelman: powered ZVS may mediate nonlinear coupling between pre-existing fast and slow modes and a separately replenished Earth-facing source. Frequency division is not the objective. Separate original Earth apparatus, proposed portable plate, Smith figures, electrochemical/galvanic, DC, RF and Schumann source hypotheses.

## Evidence and reverse solve
Archived FilsingerEarthThreeElectrodesZVSFrequencyPull20261110 reports 3.8 V, 0.4 W and 48 V across capacitors, not simultaneous calibrated source/output power or Earth open-circuit voltage. JointCarrierAMFMFSKSourceCut20261115: 3–5 Hz FM and 6–10 Hz band, 7785–7824 Hz acoustic ridge; 3.915 Hz half nominal Schumann is a candidate, not a measured independent oscillator. Prior #1507 2:1 FM PLV .07198, shift p .6447; AM .18425, p .053 uncorrected; no established entrainment. 7800/7.83=996.17; intentional 1000x tuning not source-confirmed. Do not force exact clock quotient. 7.8 kHz is audio, not calibrated switching frequency.

ReverseRadarSourceOptimisation20261112 and F05 already provide fixed-source passive bound; use dimensionless u=Rs G, target fraction a=4u/(1+u)^2. Discriminant 16(1-a), so a>1 impossible for this source model. No numerical original-device optimal excitation without identified source/load/driver operator. Compare identical source/initial storage and signed total boundary work; judge incremental useful work net of driver and modulation costs, with loss and final storage accounted. Distinguish power and circulation Pareto objectives. Nonlinear history-dependent source requires independent fitted and held-out operator and uncertainty, not arbitrary adjustable source power. No high-voltage construction or atmospheric intervention prescriptions.

## Geometric shortcut
RelationalTernaryPhaseGeometry.eisensteinDoubleSlitLaw and ternaryRootsCancel; C3 projector scope script alexander_horned_f7_spin_c3_projector_scope.py (finite-field donor, not same physical actor); Base369Ternary27StratifiedFibreHolonomyExact (noncommuting fibre transport analogue); #1444 spatial C3 Wilson covariance; #1460 same-clock/KK/TSVF conditional source. Use sparse (fast, slow, C3-character) indices; products add frequency indices and character mod 3. Physical spatial sector reduction requires actual symmetry/intertwiner. Threefold character is not a full azimuthal winding number; ell and ell+3 alias. A scalar AM cannot establish rotating field. Distinguish electromagnetic polarization, azimuthal winding, helicity, toroidal/poloidal circulation, and gravitational torsion; no equivalence implied. Half-frequency quadratic contribution can have twice the slow frequency but is not evidence of independent ELF radiation. Full vector field and signed flux required.

## Exact gates (append, do not supersede F01–F16)
MR01 archived source provenance and competing observations — source audit; direct original 1000x intent open.
MR02 fixed-source reverse bound and feasibility — local symbolic PASS; actual source parameters open.
MR03 sparse fast/slow/C3 products and alias preservation — finite implementation PASS; material-memory solver open.
MR04 C3 symmetry projector and broken-symmetry negative control — finite PASS; actual geometry/equivariance open.
MR05 quadratic doubled slow-frequency and scalar-AM null — finite PASS; measured spatial phase open.
MR06 369 coarse/fine transport, phase/order retention, commutation and physical decoder — OPEN.
MR07 nonlinear distributed line owner check_smith_filsinger_dispersive_finite_line.py plus Lorentz ADE, full vector Green and harmonic transfer; independent clocks, measured constitutive memory, retarded fields — OPEN.
MR08 source-bounded forward/inverse comparison of passive match, drive-only return path, electrochemical source, coherent wave and nonlinear replenished source with identical boundary and complete signed work — OPEN actual source.
MR09 spatial field diagnostics and handedness null, distinguish polarization from winding and useful output — OPEN measured.
MR10 original reel netlist, synchronized electrical and acoustic trace, source impedance and independent source coherence — OPEN.
MR11 full source/material/receiver state return and net useful work contrast, all ports — OPEN (F15).
MR12 optical 2023 temporal diffraction and 2025 spacetime diffraction raw data replay; stationary and switched ADE/Floquet, physical scattering/Poynting normalization — OPEN.
MR13 Paper 2 time-indexed hyperfabric, Bishop exp/Fourier, #1444 Wilson, KK compact spatial index distinct from temporal harmonics, #1460 coherent TSVF histories and OS same-clock — OPEN physical weld.
MR14 multi-cell multi-input exact harmonic acceptance and sparse error/alias controls — OPEN.
MR15 local SymPy acceptance and exact source readback, no CI, Agda deferred — 21 assertions executed on new source; no physical gate promoted.

Sources: 2023 optical DOI 10.1038/s41567-023-01993-w; 2025 DOI 10.1038/s41467-025-60159-9; Earth-ionosphere mode variability DOI 10.1029/2006JA011726; EM polarization vs orbital angular momentum DOI 10.1103/PhysRevA.84.033838. Keep all existing F01–F16, physical Q gates and attribution intact. No original optimal settings, net environmental energy, or spacetime torsion claimed.


## User correction: HF-induced slow cavity response is a first-class hypothesis

The near-1000-times nominal Schumann acoustic carrier must not be relegated to attribution or recast solely as extraction from a pre-existing ELF source. Distinguish (A) drive-funded emergence/reinforcement of a slow collective mode through nonlinear dynamics and cavity feedback, (B) modulation of access to an independently replenished source, (C) acoustic/mechanical or local circuit response without a cavity field. Test all three forward and reverse; pure-tone memoryless polynomial exclusion is a relevant null, not exclusion of dynamic subharmonic response. Nominal 7800 Hz is 30 Hz below 1000*7.83 Hz; 3.915 Hz candidate half-frequency. Neither exact lock nor electrical carrier is established. Do not assume ELF is intrinsically less energetic or universally more dispersive: physical response and energy depend on actual source, modes, attenuation and damping.

Reuse SmithFilsingerGoldenFibonacciSingleWaveMaxCut20261112 (single incident wave / orthogonal modal quadrature fixture), SmithFilsingerSchumannPhysicalSourceMaxCut20261112 (local field scale and standing-wave flux caveat), sparse C3/369 phase algebra, nonlinear material ledger, switched ADE, Floquet and temporal diffraction owners. Quadrature is not proof of spatial winding or toroidal flux; source-specific field reconstruction remains open.

MR16: abstract frequency bookkeeping, quadratic envelope observation, opposite-handed equal-intensity counterexample and source/dissipation/storage ledger: 9 exact SymPy assertions executed locally in check_smith_filsinger_cavity_response_discriminators.py. These are discriminators, not a calibrated cavity model or excitation prescription. MR17: distinguish a real slow field from a quadratic readout and local acoustic envelope, verify independent spatial-field observation and complete source work. OPEN. MR18: causal model discrimination among drive-funded slow response, independently supplied natural work, and local-only response. OPEN. Keep original MR01–15, F01–16, optical/KK/YM/TSVF and Earth battery gates intact. No CI or Agda run. No physical atmospheric excitation or original apparatus optimum asserted.
