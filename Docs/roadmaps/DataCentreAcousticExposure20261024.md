# Data-centre acoustics, infrasound, EM fields and human-exposure programme

Date: 2026-10-24
Status: research support / empirical acquisition plan, NOT proof of clinical outcomes.
Formal owner: `DASHI/Environment/DataCentreAcousticExposureAttributionExact.agda`.
Numerical fixture: `scripts/datacentre_acoustic_identifiability_audit.py`.
Pre-existing owners, reused: `DASHI.Planning.DataCentreUrbanResourceConflictExact`, `DASHI.Biology.AvianMagnetoreceptionEMExposureTransportExact`, `DASHI.Physics.Foundations.RFArrayManifoldSourceAtlasExact`, `DASHI.Governance.InstitutionalAnomalousAlteredStateProgramAtlasExact`, and the Swanbank data-centre planning-pressure witness.

## Attribution: original object -> actual support -> not supported

| Root / date | Evidence kind | Paid scope | Not paid |
| --- | --- | --- | --- |
| @itsgingertheory [reel](https://www.instagram.com/reel/DbqY4jLxuhs/); user-supplied SRT and six screenshots, observed 2026-10-24 | Creator statement and screenshot provenance | Documents specific spoken assertions and on-screen sources: Talk About Martin, Elk River Data Center, Lyver/Tanner Way chart, Peaceful Peculiar, Sirav & Seyhan, Nittby et al., Davis et al., WaveBlock, Murray/Autoimmune Association, ANA data | On-screen juxtaposition is not a quantitative human outcome study, nor proof of individual cited papers' precise claims |
| [Benn Jordan, Datacenters Behaving Like Acoustic Weapons](https://www.youtube.com/watch?v=_bP80DEAbuo), 2026-02-18 | Field/creator documentary and exploratory intervention | xAI Colossus, MARA/Granbury, Permian Basin, site recordings, community testimony, 3-minute exposure experiment | Site-receptor absolute sound-pressure calibration; prespecified masked statistical design; published or independently replicated disease-risk estimates |
| [Jordan's response to Masley](https://www.bennjordan.com/blog/the-altruists-have-arrived), 2026-04-20 | Author reply | Instrument-response limits, airborne/structure coupling hypotheses, defence of cautious investigation; acknowledges visual sources sometimes do not directly support contemporaneous narration | Independent experimental replication; confirmed financial motive of any opposing author |
| [Andy Masley, Contra Benn Jordan](https://andymasley.com/writing/contra-benn-jordan-data-center-and/), 2026-04-19 | Detailed adversarial commentary | Raises calibration dBFS vs dB SPL, room shake and sham, selection, priming, unblinding and multiple comparison issues | Its categorical 'all subaudible harm is fake' position is not itself a meta-analysis or demonstrated universal negative |
| [Megan Rand Wheeler et al., 2026](https://doi.org/10.3390/cleantechnol8040126), 2026-08-07 | Peer-reviewed *narrative review* | A-weighting discounts LF; gap in calibrated infrasound + low-frequency data-centre measurements and epidemiology | No original verified infrasound site dataset or causal health demonstration |
| [Environmental Pressures and Modelled Health Pathways of Data Centers in the AI Era](https://doi.org/10.3390/environments13100568), 2026-10 | Systematic review/evidence map | 36 eligible studies, 112 estimates; 18 reach pressure only, 12 population exposure, six modelled health effects, zero observed human outcomes | Absence in review is NOT a proof of no health risk |
| [Jurado & Marquardt](https://www.nature.com/articles/s41598-026-50179-w), 2026-04-24 | Original perception experiment | Human infrasound perception mechanism at sufficient amplitude, cochlear electrical potentials | Chronic residential illness or an operational data-centre exposure dose |
| [Sirav & Seyhan, 2009](https://doi.org/10.1080/15368370802608738) and [Nittby et al., 2008](https://doi.org/10.1080/15368370802061995) | RF/ELF animal and review literature | Distinct electromagnetic biological research; research questions about blood-brain barrier | Does not identify acoustic infrasound effects or establish population risk from telecom towers |
| [Queensland Environmental Protection (Noise) Policy 2019](https://www.legislation.qld.gov.au/view/whole/html/2026-01-28/sl-2019-0154) and [Brisbane City noise assessment guide](https://www.brisbane.qld.gov.au/content/dam/brisbanecitycouncil/corpwebsite/building-and-planning/documents/guide-to-noise-impact-assessment-planning-scheme-policy.pdf) | Official policy and planning guidance | Environmental acoustic values, amenity/sleep objectives, low-frequency and vibration assessment categories | A site is not established noncompliant by existence of a low-frequency noise source; Brisbane-specific planning guide is NOT an Ipswich statutory instrument |

No double count of linked summaries, reprints and citations as independent root studies. Advocacy and community testimony are preserved as source objects; no invented study participants or exact hospital outcomes.

## A particularly revealing downstream genealogy

A 2026 Montgomery County Coalition to Protect Neighborhoods submission cites Benn Jordan's documentary explicitly as support for regulating subaudible noise. This shows a documentary-to-public-policy advocacy path (https://www.montgomerycountymd.gov/COUNCIL/Resources/Files/agenda/col/2026/20260224/testimony/item5-MontgomeryCountyCoalitiontoProtectNeighborhoods.pdf). It does not establish the physical risk claim merely because it appears in legislative testimony.

## Dimensional / physical model

Keep channels distinct. Their common dimension of temporal frequency does not imply they are the same force or exposure:

- Air pressure: p(t,x) in Pa; pressure spectrum S_pp(f) in Pa^2/Hz, absolute SPL referenced to 20 microPa, matched integration band, response/time window and calibration chain.
- Structural motion: acceleration a(t,x) in m/s^2 (and displacement/velocity if calibrated), contact coupling and transmission path. Not convertible to ambient acoustic SPL without calibrated transfer.
- EM: E field in V/m, B field in T, spectrum and spatial polarization; dielectric/thermal or other actually stated mechanism; reuse the existing avian EM exposure transport boundary. Carrier frequency alone does not determine deposited dose.
- Acoustic-E/M *engineering* coupling is possible, e.g., electrical transformers making mechanically generated hum, but requires a separately identified transducer; coincident MHz/GHz RF and 20–250 Hz acoustic labels prove nothing by themselves.
- Health: measured outcome with temporally linked receptor exposure, adequate comparator, repeated measures and adjustment for audible annoyance, sleep, temperature, diesel emissions, baseline morbidity, socioeconomic and expectation factors.

For a plane travelling far-field sound wave, intensity is approximately p_rms^2/(rho*c), but DO NOT apply this relation to near-field reactive sound, a vibration accelerometer or standing waves without a model.

Idealized dBA inverse non-identifiability: using the standard analog A weighting approximation, a pure 31.5 Hz tone at about 74.53 dB SPL and a pure 125 Hz tone at about 51.19 dB SPL both yield 35 dB(A). Difference 23.34 dB flat SPL; no particular biological risk follows. The Agda module additionally proves a simple finite weighted-power collision, not a full acoustic inverse theorem.

## Decibel interpretation audit: the 25,000% ambiguity

Masley's critique quotes Jordan's approximate "25,000% higher than ambient" comparison and translates it into about 48 dB. The conversion only yields ~47.99 dB if the percentage represents a **pressure-amplitude ratio** of 251. If it represents an **intensity or spectral-power ratio**, the difference is ~24.00 dB. If the underlying units are a normalised digital spectrum (dBFS) or a background-subtracted estimate, neither value demonstrates an absolute environmental SPL. The original plotted quantity, spectral estimator, calibration, noise floor and baseline must be recovered before promoting the comparison.

The Python fixture executes and asserts the distinct conversions. This clarification is not a claim that Jordan's field result was valid or invalid.

## Jordan experiment audit: steelman plus limitations

- The documentary reports more than 100 initial participants and 74 retained after exclusions, and describes an approximately three-minute stimulus with an intended control condition.
- Increased reported discomfort/dizziness under a physically active subwoofer is an exploratory *self-report association*, potentially interesting if raw assignment/response data support it.
- Outstanding: precisely calibrated waveform; field-site to room dose transport; low-frequency audible sidebands; floor vibration; equipment sham; individual blinding success; time and group allocation; exclusions by original assignment; prespecified primary endpoint; correction for multiple testing; participant selection and follow-up.
- The critique raises concrete threats to inference; Jordan's reply correctly notes that absence of proof is not proof of impossibility. Neither suffices to claim a data-centre-specific physiological causal effect.
- No raw participant-by-assignment data or full calibration chain retrieved here. Therefore do not recreate inferential statistics from percentages alone.

## Phase and deliverable ledger

| Phase | Status as of 2026-10-24 | Deliverable; objective pass criterion |
| --- | --- | --- |
| P0: root-source retrieval and attribution | Substantially PAID for cited web/screenshot objects | Versioned ledger; classify speaker quote vs study results vs advocacy vs official assessment |
| P1: dimensional separation and inverse-identifiability | FINITE WITNESS + numerical fixture paid; NOT an operational field solver | Check `python scripts/datacentre_acoustic_identifiability_audit.py`; verify pressure, structure and RF have different units and transports |
| P2: calibrated emissions and baseline | OPEN | Time-stamped flat/Z or appropriate G/C/A/third-octave and narrowband spectra with certified low-frequency response, calibration, noise floor, mic wind protection and meteorology; synchronize equipment operating state, repeated background controls |
| P3: causal facility-to-receptor identification | OPEN | On/off or operational-load natural experiment; spatial gradients indoors/outdoors; coherence and source modulation; reject road/rail/HVAC/wind/industrial confounders; quantify uncertainty |
| P4: health-response discrimination | OPEN | Preregistered masking and sham control; primary outcome defined in advance; sample-size power; independent respiratory/cardiovascular/sleep/vestibular measures; null results and attrition reported |
| P5: engineering mitigation and Queensland policy application | MODEL ROUTE READY / SITE-DEPENDENT | Compare fan speed/tonal shifts, isolation mounts, attenuators, cooling design, setbacks, operating controls and indoor acoustics; check actual applicable LGA/state permit and receptor objectives |
| P6: extraordinary targeted RF/mind-control claim | NO SOURCE-CONVERGENT MECHANISM | Requires a specific apparatus/emitters, waveforms, fields, receiver couplings, demonstrated objective biological effect and authentic historical-document-to-deployment join; otherwise no promotion |

## Pareto / max-cut selection

1. Acquire one primary calibrated time-series from an operating data centre plus matched off-site baseline and operation log. This simultaneously pays measurement, spectral/facility attribution, acoustic mitigation feasibility and regulatory receptor-comparison dependencies.
2. Audit any available Jordan dataset for intervention calibration, randomization, exclusions and blind success; absent original participant data, do not promote the reported percentage effects.
3. Replicate controlled low-frequency *audible* and sub-20 Hz stimuli at measured community-relevant sound-pressure levels, with independently masked acoustic and vibration-sham conditions.
4. If receptor exposures exist and exceed expected background, use existing environmental engineering interfaces to test source mitigation before advancing disease-specific conjectures.
5. Develop a separate RF dosimetry program only where there is an independently plausible emitted-field source; do not infer the existence of an engineered mind-control system from intelligence history.

**Physical implication:** standard linear acoustics + structural dynamics + measurement theory suffice for the next major advance; nothing so far requires new fundamental quantum, spacetime or exotic field theory. Computational fluid/thermal source modeling, wave propagation, FEM structure and uncertainty quantification can cross-pollinate existing DASHI physical infrastructure, but the model cannot be promoted to real-site exposure without real boundary conditions/calibration.

**Planning implication:** share only measured, auditable acoustic-impact inferences. Do not transfer Brisbane City Council local rules to the Swanbank/Ipswich case without an explicit jurisdiction-specific mapping. Site-level claims must reference actual planning documents, not national averages or commentary.
