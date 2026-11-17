# Infoton/P30 round 2: original-source and physical obligations (2026-11-15)

**Companion to** \`docs/research/InfotonP30WalkerMaxCut20261115.md\`. Keep both; do not overwrite the 7/19 original baseline. Status in **this** pass: **8/19 closed, 11 open**, where E1 is closed as a **negative adjudication** (universal claim refuted), *not* as a validated safety improvement. Existing Clay gates are entirely unrelated.

## Source acquisition receipts

| Original | Location | What the original actually establishes |
|---|---|---|
| January Walker's *NISTIR 6025 Information Physics Mapping* presentation, 34 pp | https://infoton.ai/infoton-p30 PDF linked; page 28 proposal, pp.29–32 screenshots | P30 proposal; 163 vs 167/171/116 byte mode counts; comparison is 12,264 operations including repeated ECC vs 163 one-time P30 ingress operations; 130kW→1.73kW **assumed** linear projection |
| JanuaryNWalker/Infoton public GitHub | https://github.com/JanuaryNWalker/Infoton, observed 2026-11-15 | One commit, public README and LICENSE only; no inspectable source of original encoder, decoder or verifier. **Absence from this repository is not proof that no code exists elsewhere** |
| Actual NISTIR 6025 (Carnahan et al., May 1997) | https://nvlpubs.nist.gov/nistpubs/Legacy/IR/nistir6025.pdf; https://www.nist.gov/publications/metrology-information-technology-it-0 | Discussion of measuring IT systems; **not** a compulsory IBM architecture instrument. Walker's presentation is her own document with title referencing NISTIR |
| NIST FIPS compliance guidance | https://www.nist.gov/standardsgov/compliance-faqs-federal-information-processing-standards-fips | FIPS standards are not all mandatory for federal agencies; private sector frequently voluntarily adopts standards. It does not establish a universal ban on other data structures |
| IEEE 754-2019 | https://standards.ieee.org/ieee/802.15.6/6210/ | Explicitly supports *binary and decimal* floating-point arithmetic, software or hardware implementations |
| US DOJ historical IBM records | https://www.justice.gov/atr/case-document/united-states-memorandum-1969-case | Dismissed 1969 lawsuit in 1982; a historical antitrust record, **not** an affirmative US law obliging the IBM byte |
| US NRC Circular 80-08 (18 Apr 1980) | https://www.nrc.gov/reading-rm/doc-collections/gen-comm/circulars/1980/cr80008 | Vermont Yankee *specified* 100ms from contact to relay, *verified actual* less than 50ms since original operation, GE BWR expected <50ms by design/test. This **refutes every-reactor-2s-blind as a universal statement**, without proving there are no problematic slow processes |
| IAEA *INSAG-7* (1992), Annex I §I-4.3.2, PDF page 66 / printed page 56 | https://pub.iaea.org/MTCD/publications/PDF/Pub913e_web.pdf | SKALA main calculations every ~5min, DREG sampled selected physical channels under 1s with outages and omissions. Long supervisory/recording cycles were real, **distinct** from a blanket delay of all safety protection |
| LBNL *2024 US Data Center Energy Usage Report* | https://escholarship.org/uc/item/32d6m0d1 | IT power, PUE and WUE are separately defined, site and source water differ; water cooling varies by cooling topology and weather; facility watts cannot be derived solely from generic logical operation counts |
| Walker, *The Quantum Heartbeat of Mitochondria* | https://zenodo.org/records/18373065 | proposes 36.26 THz by \`e Δψ_m/h\`; does **not**, in the published abstract, provide independent spectral observation of a mitochondrial oscillator at that frequency |
| Walker, *The Infoton: A Fundamental Particle of Information-Energy* | https://zenodo.org/records/18210355 | obtains \`k_B T ln(2)/c²\`; this is energy equivalent by definition, not an independent detection of a particle |

## Reproducible executable advance: B2/B3 comparison foundation

\`scripts/infoton_p30_ecc_maxcut.py\` and \`scripts/test_infoton_p30_ecc_maxcut.py\`, no third-party packages:

- A **real SECDED reference code**: 64 data bits, eight parity bits, odd-weight 8-bit parity-check columns; parity check matrix has eight weight-one columns, 56 weight-three and eight weight-five data columns; 72 unique odd columns. Syndrome decoding reproduces **all 72 single-bit corrections** and **all 2,556 double-bit detections** for a representative word. Tests additionally cover all-zero, all-one, three data words and 200 seeded random words. The reference's fault claims are proven for all data words by linear syndrome symmetry, though only the finite examples have been executed.
- An explicitly **NON-P30** residue-8 alphabet 3-position surrogate: losslessly represents each of 256 bytes in 3 coprime residues modulo 30, with a range check. Exactly **4,352 / 5,376 (=17/21)** possible single position substitutions by a *different* valid residue produce an undetected, wrong, still-byte-range representation. The other 1,024 produce out-of-range values. This is a falsifying model for **unit membership alone** as ECC, not proof that Walker's unprovided full verifier fails.
- With only source-supplied numbers, the 12,264→163 operation comparison is not matched-equivalent error correction: SECDED's repeated read checks are real work and cannot be set to zero on P30 unless identical detection and correction guarantees are demonstrated.

\`\`\`sh
python3 -m unittest discover -s scripts -p 'test_infoton_p30*.py' -v
python3 scripts/infoton_p30_ecc_maxcut.py
\`\`\`

## Physical power sensitivity: quantitative critical countermodel

The P30 slide assumes \`Pnew = 130 kW × 163/12264 = 1.7278 kW\`. **Even conditional on its 75.24× reduction applying to a well-defined portion of rack work**, total power actually follows
\`\`\`
Pnew = Pfixed + (130 kW − Pfixed) × 163/12264
\`\`\`
where \`Pfixed\` covers load unaffected by the proposed software algorithm (idle silicon, other computations, memory, networking, storage, cooling, UPS). At **25% fixed load**, \`Pnew = 33.7959 kW\`; at **50%**, \`65.8639 kW\`; the claimed **1.7278 kW** requires **zero** fixed load. These are **explicit illustrative sensitivity assumptions**, not measurements of actual rack fixed fraction or P30 performance.

No measured IT energy, per-rack distribution, verifier implementation, facility PUE, site WUE or wet/dry cooling topology has been provided. The claimed >43GW, water elimination and reactor-avoidance numbers therefore remain **unverified extrapolations**; no actual fleet energy savings are established.

## Physical hypotheses: exact non-implications

1. **D1 particle:** \`m(T)=k_B T ln(2)/c²\` varies continuously in \`T\`; this is a thermodynamic equivalent, **not evidence of a fixed new particle or spectral line**. At 310K it is 31/30 of its 300K value. An independent coupling, production/detection channel, predicted spectrum and control experiment are needed.
2. **D2 quark charge:** occupation \`f=1/(e^((E−μ)/kBT)+1)\` is 1/3 at offset \`ln2\` for a neutral and a charged fermion alike. Occupation probability alone has **no gauge-representation information**. Need a derivation of U(1) electric charge, coupling and observed charge assignments.
3. **D3 heartbeat:** a static membrane potential \`Δψ_m=150mV\` satisfies \`eΔψ_m/h≈36.27THz\` while its electrical time-series is a DC signal with *no oscillation at 36.27THz*. Need measured spectral peak, bandwidth, perturbation-response controls, background/phonon exclusion and independent replication.
4. **E1 reactors — CLOSED AS UNIVERSAL NEGATIVE:** NRC original contemporaneous 1980 record documents tested <50 ms BWR safety contact→relay, refuting an inherent common two-second delay. IAEA original shows real 5min SKALA calculation *separate* from short DREG capture and direct reactor protection, so the argument needs system boundaries.
5. **E2 legal:** NISTIR is not a binding architecture law; NIST's own FAQ explicitly says not all FIPS mandatory. Walker's exact purported *nine enactments and provisions* have not been supplied; global negative proof of no relevant law in any jurisdiction is NOT claimed.
6. **E3 water:** site water is \`WUE × IT kWh\`, heat/cooling is topology- and weather-dependent, and 130kW to 1.73kW is an unmetered sensitivity claim. No elimination of water follows from a number of abstract bit operations.

## Gate accounting

| Gate | Result after pass | Acceptance missing |
|---|---|---|
| A1–A7 | CLOSED original finite/evidence | Keep original source-provenance scope |
| B1 original encoder | OPEN, public repository checked | Actual P30 code, tests, content hash, framing |
| B2 original verifier | OPEN, ref ECC implementation landed | Original ECC algorithm, fault guarantees |
| B3 matched-equivalent benchmark | OPEN, fault comparer and countermodel landed | Same workloads, framing, total verification costs, original P30 code |
| B4 Agda kernel check | OPEN | Agda 2.8.0.2 + pinned stdlib type checking; no compiler in current environment |
| C1 hardware power | OPEN | Wattmeter/repeated loads on matched machines incl idle, board, network and IO |
| C2 FRACDASH same-object bridge | OPEN | Real P30 codec to transport and proof joining; may not be possible if codec withheld |
| D1 infoton particle | OPEN | experimentally distinct predicted particle properties and positive detections |
| D2 charge | OPEN | gauge representation and physical coupling evidence |
| D3 measured mitochondria oscillator | OPEN | genuine THz spectroscopy and controls |
| E1 universal reactor blindness | **CLOSED NEGATIVE** | Universal two-second claim contradicted by NRC original; individual failures still possible |
| E2 all-law mandate | OPEN / narrowed | Nine exact laws and sections, plus scope and temporal effect |
| E3 measured power/water/heat | OPEN / model failure found | Actual facility telemetry and physically grounded extrapolation |

**Count: 8/19 adjudicated; 11 original positive physical/technical obligations remain OPEN.** A negative adjudication is explicitly not a hardware or science breakthrough.

No test suite or symbolic algebra can produce unavailable reactor hardware measurements, Wattmeter readings or a P30 proprietary verifier. This audit must remain fail-closed.
