# P2 — Duga original Soviet radar source (1991) and near-contemporary RF observation (1985)

**Date 23 November 2026, Brisbane.** Original-source escalation to a *directly inspected* Soviet-era article via government translation, plus independent near-contemporary receiver descriptions and a locally tested exact finite signal fixture. Not a historical biomedical programme or an original Soviet transmitter schematic, not original RF waveform bytes, and not evidence of induced Schumann or human neurological effects.

## A. First direct Soviet-side original source: Babakin 1991

**Original Russian publication:** Major **Aleksandr Babakin**, “Fortresses Alone Are Ineffective, or Why the Over-the-Horizon Radar System Was Shut Down,” *Kommunist Vooruzhennykh Sil* No. 3, **February 1991**, signed to press **11 February 1991**, pages 23–28.

**First-hand government translation:** U.S. **Joint Publications Research Service** report **JPRS-UMA-91-012**, published **3 May 1991**, report pages **45–48**, article reference **91UM0569A**. The full archival PDF is [publicly accessible here](https://coldwar.tech/media/pages/archive/documents/jprs-oth-radar-1991/1090cd240b-1783705138/jprs-uma-91-012.pdf), with exact PDF pages 47–50 (zero-indexed, mapped to printed pp. 45–48). Government report provenance also identifies Defense Technical Information Center **ADA333791**. Original and translator are **distinct source identities**; translations, third-party mirrors and the Soviet original must not be conflated.

**Verification level:** the actual scanned page images of PDF pp. 47, 48 and 49 were opened and visually inspected, in addition to extracted text. **Original USSR-language magazine was not inspected independently**, nor were raw internal radar telemetry or design/acceptance protocols.

Original-source assertions in this 1991 account (author's retrospective reporting, not independent line-by-line test of state commission files):
- Chief designer **F. Kuzminskiy** developed the proposed two-site over-the-horizon early-warning radar system, aimed at detecting missile launches from as far as **6,000–10,000 km**.
- The Soviet State Commission reviewed the design **spring 1971**, the **first site was constructed in 1975**, and a second near **Komsomolsk-na-Amur** was developed during testing.
- During tests the **Chernobyl-region radar** fell short of design requirements for **single and small groups of ballistic-missile launches**, even though larger salvos were more detectable. The account reports significant **electromagnetic attenuation passing through the polar ionosphere**, as well as engineering modifications and disputed acceptance decisions.
- The account treats polar ionospheric propagation as a *difficult variable physical channel*, not an ideal unlimited energy conduit; it records Kuzminskiy's later theoretical/experimental work attempting to improve propagation modelling.
- The **1986 Chernobyl nuclear accident** ended research at the nearby site according to the account; the Komsomolsk site's programme was later withdrawn amid budget/policy and performance changes. The article alleges inefficient management and costly procurement: attribute those judgments to Babakin, not to an independent auditor.

**Critical correction to previous roadmap:** an original Soviet-period account now exists and **has actually been inspected**, so the blanket “original Duga technical history absent” claim is outdated. This paper **does not report the operating pulse voltage/current, full per-transmitter RF phase, calibrated detector-field amplitudes or health studies**, so those remain open; it also does **not itself validate all 1985 Western monitored frequency assignments**.

## B. 1983/1985 near-contemporary independent RF receiving evidence

- The original **September 1983 *Practical Wireless***, “Over-the-Horizon Radar Systems — Beyond the Blue Horizon,” [archived period issue](https://www.worldradiohistory.com/UK/Practical-Wireless/80s/PW%201983%2009.pdf), describes RF receiver/oscilloscope techniques and a typical approximately **4 ms RF pulse in a 100 ms repetition**, discussing multiple echoes and use of intermediate-frequency and detected signals. Parsed archival source text was examined; PDF screenshot failed (HTTP 403), so do **not** claim visual inspection of the original oscilloscope figures in this turn.
- The original **August 1985 *Monitoring Times*** receiver/oscilloscope investigation, [archived contemporary issue](https://www.worldradiohistory.com/Archive-Monitoring-TImes/1980s/Monitoring-Times-1985-08.pdf), distinguishes **10 Hz, 16 Hz, 20 Hz repetition** (10 Hz common), **static** and **dynamic** frequency/time-window patterns. Its **10 Hz** case consists of four adjacent **7 ms transmitting windows** in each 100 ms frame plus **72 ms silence**, with actual pulse widths estimated **3–6 ms** within a window; approximate bandwidth often **40 kHz**. Static example frequencies: **16450, 16490, 16570, 16390 kHz**; dynamic example **8070, 8230, 8310, 8260 kHz**, with six-second window reassignment forming a 24-second cycle. The magazine authors note receiver reaction time, multipath and uncertain pulse substructure. Parsed text inspected; the original PDF screenshot also returned HTTP 403, so exact oscillogram-image analysis and instrument recalibration remain OPEN.
- This is not a claim that the two independent 1983 and 1985 receiving reports establish one invariant waveform used at every Duga site/time. They report **receiver-side conditions** and instrument limits. Recorded repeat rate **10 Hz** is neither a 10 Hz carrier nor a demonstrated 7.83 Hz Schumann drive.

## C. New source-structured exact, testable signal bridge

[Original-window SymPy script](../../scripts/radiobio_p2_duga_original_four_windows_sympy.py) explicitly uses **T=100 ms**, **four 7 ms windows** at t=(0,7,14,21) ms, **4 ms example rectangular RF envelope pulses** in each (the 4 ms pulse is an *illustrative choice within the reported range*), and **72 ms remaining silence**. For the four observed 1985 static carrier channels, a 4 ms single-channel pulse per 100 ms has exact per-channel envelope duty **1/25 = 4%**, and all four channels have a combined non-overlapping model duty of **4/25 = 16%**; these are model fractions, NOT original measured transmitted power. Model dynamic assignment has 4 configurations at **6 s** apiece, completing at **24 s**.

For one periodically repeated model pulse at window origin, baseband gate Fourier coefficients have:

    c_n = sin(pi*n*w/T)/(pi*n) * exp(-2*pi*i*n*(t0+w/2)/T), n≠0,
    c_0 = w/T = 1/25.

The exact squared coefficient at n=1 is **sin(pi/25)^2/pi^2**. Multiplying the envelope by an RF carrier shifts these coefficients to **f_RF ± n × 10 Hz**; the Fourier envelope's baseband coefficient does **not** mean a separate 10 Hz antenna carrier was radiated. This source-patterned fixture gives more realistic source timing than the earlier single sinusoidal [RF-carrier discriminator](../../scripts/radiobio_p2_duga_pulse_carrier_sympy.py), but retains the real unknown source pulse internal modulation and ionospheric propagation kernel.

**Local test:** exact SymPy finite checks PASS: four non-overlapping 7 ms windows, 28+72 ms framing, allowed 4 ms pulse, 1/25 duty, 4/25 total, correct Fourier first-harmonic squared coefficient, distinct four RF frequencies, and 24 s frequency-to-window permutation return. Python compilation PASS. **Exact local git hash-object** of executed code `0c283df543351f8d844872b069266af40676ba88` matches the code fetched back from GitHub, byte-for-byte. No CI, no original RF sample arrays and no Agda kernel acceptance.

## D. Source-to-model and cross-programme boundary

- **SURA 2026:** physically measured HF pump ionospheric modification and plasma spectral structure, separately documented in [SURA/Filsinger source audit](SmithFilsingerSURA2026OriginalIonosphereHeatingWeld20261123.md). Duga's measured/retrospective *pulse-train radar interference*, and its 1991 original polar-ionosphere attenuation record, provide useful **source-to-propagator uncertainty** and **instrument demodulation negative controls**. Neither 1985 pulse rhythm nor 1991 original history establishes a SURA daughter-wave interaction or a Filsinger energy-harvesting interface. Different geometry, source, era and instruments.
- **PANDORA:** original RF exposure and animal experiments have separate ownership in [ColdWarBioelectronicLineagePareto20261025.md](../Investigations/ColdWarBioelectronicLineagePareto20261025.md) and [PandoraBizarreRFHistoricalEvidenceExact.agda](../../DASHI/Governance/PandoraBizarreRFHistoricalEvidenceExact.agda). Reuse those documents without claiming that Duga conducted the same animal experiment or an administrative PANDORA programme link.
- **“Lazarus” allegation:** still no matching named, 1965 original official contract/report with an EM limb regeneration intervention. The *directly found original radar article* cannot establish a different alleged DARPA biological programme.
- **SCENAR external file:** [original Dryad DOI 10.5061/dryad.63xsj3v2s](https://doi.org/10.5061/dryad.63xsj3v2s) remains **PAUSED—ORIGINAL XLSX REQUIRED**; no further identical 403/DNS download attempts.

**Next source-physical priority:** actual contemporaneous calibrated IF/baseband samples and receiver transfer curve (and, if available, surviving Soviet radar engineering acceptance files); a retarded dispersive ionospheric channel with independently measured losses and a source/receiver energy balance. No claim of bioelectric stimulation, Schumann resonance or historical mind-control physics.

**Attribution:** original Russian Babakin (1991), government JPRS translators, contemporary *Practical Wireless*/*Monitoring Times* writers and existing DASHI owners each retain original authorship. This is independent source-to-math work, not historical priority transfer.
