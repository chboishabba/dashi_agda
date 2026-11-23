# P2-F4 — Duga original source clocks to passive HF receiver and power budget

**23 November 2026.** Source-aware exact **conditional** receiver and source/field boundary. NOT original Duga recorder replay, measured Soviet ERP or a medical finding.

## Reused original and repository source owners

1. First-hand contemporary source is the [August 1985 *Monitoring Times* Woodpecker RF-monitoring article](https://www.worldradiohistory.com/Archive-Monitoring-TImes/1980s/Monitoring-Times-1985-08.pdf), describing four 7-ms assignment windows in a 10-Hz/100-ms repetition mode, carrier switching and different alternate 16/20-Hz operating modes. Secondary source [EDN's technical historical recap](https://www.edn.com/a-nightmare-for-ham-radio-operators-the-russian-woodpecker/) reports the same particular 16,450/16,490/16,570/16,390-kHz channel assignment. Author/receiver observations are distinct from unknown original Soviet transmitter specifications.
2. Soviet-period [Babakin 1991 article, government JPRS-UMA-91-012 translation](https://coldwar.tech/archive/documents/jprs-oth-radar-1991), identifies original OTH early-warning purpose and difficult polar ionosphere propagation. The 1991 original is not a calibrated 1985 receiver test.
3. **Reuse, not duplicate:** [existing four-window source model](../../scripts/radiobio_p2_duga_original_four_windows_sympy.py), [original 1991/1985 audit](RadioBioP2DugaPrimarySoviet1991AndReceiver1985Weld20261123.md), [P2 original identity/source attribution](RadioBioP2ColdWarSourceIdentityDugaLazarus20261123.md); existing [Smith/Filsinger Maxwell–Lorentz ADE energy donor](../../scripts/smith_filsinger_lorentz_ade_sympy.py) and [Filsinger Sun–Earth source/receiver boundary](SmithFilsingerSunEarthCoupledGlobalCircuitMaxCut20261116.md). The new calculation addresses only the **conditional receiver/energy accounting**, not a new Agda source type or measured Maxwell–ionosphere solution.

## Original 100-ms window geometry versus model pulse occupancy

Four original reported **7-ms available windows** occupy 28 ms of a 100-ms frame (28%). We choose an **illustrative** 4-ms RF-on pulse in each window, within the reported approximately 3–6-ms values; **16 ms actually keyed-on** is 16% of that source-model frame. The final 72 ms after all four slots are silent, but **an additional 12 ms within the four 7-ms slots is unused**. Hence the **full RF-off fraction** in this fixture is **84%**, not 72% or 28%. Different original configurations / 16 or 20 Hz modes require their own timing. This corrects possible duty-factor conflation.

The model source frequencies are four independent **HF** carriers, never a single 10-Hz RF carrier: 16,450, 16,490, 16,570, and 16,390 kHz. A demodulating receiver's local 10-Hz amplitude/pulse rhythm is not a calibrated direct 10-Hz radiation field and its presence does not establish Schumann coupling.

## P2-F4 exact passive receiving boundary

[New SymPy independent receiver audit](../../scripts/radiobio_p2_duga_receiver_work_sympy.py) takes the four published receiver-observed HF channel identifiers as distinct. With peak incident (NOT transmitter ERP) power flux density **S_peak at each of four distinct HF frequencies**, illustrative unity antenna receive gain and no polarization/mismatch loss, available receiving aperture per source frequency f_i is

    A_eff,i = G_receive,i * c² / (4π f_i²),    G_receive,i = 1 in the fixture.

Each channel is active only for one 4-ms illustrative pulse per 100-ms period. If the four channel fluxes are equal, their average available RF power adds as

    P_RF_available = (4 ms / 100 ms) * S_peak * Σ_i A_eff,i.

More generally, **each original frequency requires its own measured flux and antenna gain/polarization/match**:

    P_RF_available = Σ_i [ (pulse_i / frame) * S_peak,i * A_eff,i * pol_i * match_i ].

The first expression is an **illustrative equal-flux assumption**, not an actual receiver geometry, beam illumination, 1985 reception strength, biological receptor exposure or received wattage. Values of effective aperture are idealized for antenna theory; without **receiver calibration, bandwidth, incident flux, load and impedance**, detected signal strength alone cannot determine incident power.

A nonnegative passive detector/receiver work budget is

    P_intercepted_HF = P_LF_load + P_dissipation + dU/dt

for a source-free receiving converter across a selected control surface (appropriate cycle averaging / sign of storage-change). Electrical 10-Hz load modulation after rectification is **paid by absorbed HF**, rather than proof of a separate low-frequency transmitter. If other sources participate (controller battery, local electrical supply, ambient field or storage discharge), they must be added separately without double counting.

**Identifiability counterexample:** demodulated voltage z=receiver_gain × incident_field. Scale the incident field by k and inverse scale receiver gain by 1/k. The same z results while incident power density scales with k². Hence amplitude without calibrated gain cannot identify received power. Different source-path assignments, ionospheric attenuation and polarization also remain unknown.

## Local receipt and unclosed gates

Local **SymPy 1.14.0** confirmed exactly: 4×7/100 = 7/25 source slot occupancy, 4×4/100 = 4/25 RF duty, 72-ms trailing slot-free duration, 84-ms total RF-off time, original-channel centre-frequency distinctness, symbolic per-frequency effective aperture identity, average available-power composition, and the arbitrary-gain inverse counterexample. Example equal-flux / isotropic effective-aperture sum is approximately **105.405 m²** at the four illustrative source frequencies, **not** actual antenna collecting area or historical receiver data. This local test reproduced the core equations; the newly **committed script was not independently run from its exact GitHub blob** in this step. No GitHub CI or Agda kernel.

**Next physically payable gates:** actual original Woodpecker full calibrated HF receiver recording / receiver impedance and gain; contemporaneous bearing/antenna pattern; transmitter duty/power measured with uncertainty; ionospheric propagation and antenna coupling; authenticated Soviet radar waveform/circuit object and actual loaded receiver. No source-calibrated Duga-to-tissue coupling, LF free-space field or direct receiver load power has been established. Link historical and engineering owners; do not promote generic RF demodulation to biological effects.

Attribution: original contemporary receiver investigators and Soviet author retain their own findings; antenna aperture physics is established general electromagnetic theory, while source-conditional mathematical receipts are new DASHI calculations.
