# Smith/Filsinger original-audio transient-to-hunting discriminator (2026-11-15)

## Source and ownership
Source: original 105.7959s user-supplied `ReelAudio-93787.mp3`; source SHA256 `573eb6b205bdf1c29cb33fad5e28eeb00dee18c5566aee7290679aac0396c4c6`. No electrical oscilloscope, phase-current probe, Earth ionosphere receiving meter, or source-specific terminal continuity supplied. Respect speaker Filsinger vs Don Smith vs editorial circuit diagrams (Smith fig10 p28, fig11 p29, later Fig40 p65). Source-owned recorded acoustics are observations, not independently calibrated switching source work.

## New local replay
Py source `recheck_hunting_20261115.py` (STFT 4096 Hann 22.05kHz; 256 hop, short STFT 1024) and `if_dip_phase_analysis.py` (heterodyne near 7800Hz, 500Hz complex baseband, 95Hz filtering) are included with raw-derived CSVs, plots and explanatory README in the conversation package `filsinger_hunting_recheck_20261115.zip`. Non-operational scientific three-channel receiving/observation contract has 6/6 local pass. No source audio redistributed.

7.7–7.9kHz acoustic STFT energy, referenced to median 39–50sec:
- 35–38sec activation **+9.285dB median**;
- 52–55sec **+2.740dB**;
- 56–59sec **+3.346dB**, with stronger high-percentile surges;
- 59–62sec **−3.915dB**, declining tone.

**Switch-off (~60–61sec):** dominant 7.82–7.83kHz high-confidence ridge persists through ~60.3sec. Weaker peak appears around 8.0–8.26kHz between ~60.7–60.9sec; then weaker scattered ~5.6–7.3kHz peaks appear after ~61sec. The baseline 7.8kHz carrier is then ~27–37 dB reduced. An authentic upward excursion followed by altered lower-frequency spectral content is visible, but **single continuous high-confidence chirp down to 6kHz is not established**: distinguish phase/frequency hopping, another mode, discharge, speech and tracking artifacts.

**IF mask dips:** 12/1136 samples (1.06%) across 8 short mask-runs 36.5–59.2sec. Times 39.52,39.58,41.74,43.58,47.06,51.30,53.00,55.10sec. Median failed-mask intensity ≈−21.3dB compared with 0dB reliable; this conditional association is partly *by construction* because mask uses low carrier intensity. Spacing median about 2.1 seconds but variable, **not demonstrated clock periodicity**. At finer complex-heterodyne resolution, selected deep minima near 39.546,47.064,51.316sec exhibit exploratory approx π phase rotations; phase at a null is fundamentally ill-conditioned.

A synthetic two-vibration-path model `z=A1 e^{iφ1}+A2 e^{iφ2}` with continuously operating sources and slowly changing detuning reproduces sharp intensity minima and apparent frequency spikes without hardware switching. This is a real **counterexample** to interpreting low-IF masked events as FSK or ZVS stopping. Both source-gated blanking and mode interference remain candidates, may coexist, and require a common physical multi-member inverse model.

## Combined three-transduction scientific model (NO harmful transmitter design)
Use separate causal source→observation Green operators:
1. nonlinear airborne acoustic self-demodulation (parametric ultrasonic literature);
2. material thermoelastic pressure driven by absorbed electromagnetic energy (microwave hearing literature; mostly *internal perception*, not a free-air microphone signature);
3. nonlinear electronics/coil electromechanical coupling producing ordinary air sound (candidate explanation for the present physical recording).
All three can be terms in one field–material–measurement model **with separate receiving locations, energy sources and observation channels**, but are not evidence Smith's tabletop 7.8kHz tone involves ultrasound or microwave perception. No beam emission hardware, pulse regime, targeting parameters, absorbed-dose recipe or DEW build is specified.

Additional interacting Earth/ionosphere environmental member: physically supplied conductivity, Hall-current and magnetosonic modes, with retarded field response. 2010 HAARP nonlinear whistler echoes ([DOI 10.1029/2009JA014610](https://doi.org/10.1029/2009JA014610)) demonstrate measurable phase/amplitude memory and source-strength-dependent onset delay. Geometric heating-sweep study ([DOI 10.1029/2010JA016194](https://doi.org/10.1029/2010JA016194)) calculated 5–7 dB more ELF/VLF injection under its facility model; not a Smith/Filsinger efficiency parameter. Ionospheric current drive ([DOI 10.1029/2011GL049263](https://doi.org/10.1029/2011GL049263)), nonlinear ultrasonic metasurfaces ([2026 Nat Commun](https://www.nature.com/articles/s41467-026-73604-0)), microwave thermoelastic mechanisms ([Foster & Finch 1974](https://pubmed.ncbi.nlm.nih.gov/4833827/), [Lin review](https://doi.org/10.1109/JERM.2021.3062826)) remain separately attributed. Retarded source flux has to be modelled explicitly, not inferred from microphone dB.

## Cross-lane attached note
User-supplied *Pasted text.txt* is on the separate 2026-11-15 KSW668 AdS5 moving-brane / TT wave problem, including a fixed-half-space moving-boundary transform, homogeneous-flux uniqueness and a same-observer proper-time distinction. These are **potential abstract techniques for causal boundary-indexing**, not empirical Filsinger evidence, Maxwell source laws or superluminal EM propagation.

## Original remaining gates
A: actual same-object selection and pin-level wiring/meter ground connections in Smith/Filsinger reel.
B: simultaneous complex electrical driver/current/transformer and microphone response with a calibrated transfer and time sync.
C: source-specific full coupled ZVS/pump+spark-dump+diodes+nonlinear magnetics/materials+field route that jointly reproduces onset, hot windows, masked nulls and shutdown.
D: Earth/atmospheric/ionospheric source Green functions, nonlinear material response and signed retarded work with real source spectra. Avoid unconditional substitution of 7.8kHz **acoustic** line for electrical frequency.
E: actual paid natural source work and output ledger (separating pump energy and natural ports).
F: pinned Agda kernel acceptance for the existing owner weld, plus numerical parameter uncertainty and model identifiability.
