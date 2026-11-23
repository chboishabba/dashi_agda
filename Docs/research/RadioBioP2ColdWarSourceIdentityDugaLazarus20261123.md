# P2 — historical RF source identities: PANDORA/BIZARRE prior art, Duga and unverified "Lazarus"

**23 November 2026, Brisbane.** This is a *source-status and mechanism-discriminator addendum* to existing repository investigations, **not** a new intelligence history owner, allegation of modern targeting, biological transmission observation or clinical statement. Programme names and chronology do not establish common devices or causal transmission.

## Stop retrying the P1 SCENAR inaccessible workbook

**Original source:** [Marc Fischler, original SCENAR Dryad deposit, DOI 10.5061/dryad.63xsj3v2s](https://doi.org/10.5061/dryad.63xsj3v2s), [public dataset record](https://datadryad.org/dataset/doi:10.5061/dryad.63xsj3v2s). **Exact external resource:** `Scenar_-_Dryad_Corrigé.xlsx`, ~21.86 KB, [original file stream](https://datadryad.org/downloads/file_stream/915627), [alternate Dryad file API](https://datadryad.org/api/v2/files/915627/download). **Status:** web file request 403 and local DNS failure, original bytes 0, hash unknown. This task is **PAUSED—EXTERNAL FILE REQUIRED**, not "negative clinical data" or a successful participant replay. Do not repeat blocked API attempts without a changed access route. The [original published study](https://doi.org/10.3390/jcm10235570) separately reports 60 participants, 30/30, active versus sham p=0.22, while the data workbook remains unseen. [P1-E1/E4 source audit](RadioBioP1SCENAROriginalDryadTrialReplayGate20261123.md), [exact-code receipt](../../Artifacts/radiobio/radiobio_p1_e4_scenar_exact_blob_acceptance_20261123.json).

## Prior owner found — do not duplicate PANDORA

Existing authoritative repository work already contains original-source sequence and adverse/negative findings:
- [ColdWarBioelectronicLineagePareto20261025.md](../Investigations/ColdWarBioelectronicLineagePareto20261025.md) — PANDORA/TUMS/BIZARRE programme genealogy and original CIA/ARPA/RAND documents.
- [PandoraBizarreRFHistoricalEvidenceExact.agda](../../DASHI/Governance/PandoraBizarreRFHistoricalEvidenceExact.agda) — original attributed original objects, source type and authority constraints.
- [GingerTheoryFrequencyClaimsOriginalSourceCut20261025.md](../Investigations/GingerTheoryFrequencyClaimsOriginalSourceCut20261025.md) — existing claim-to-original lineages with attribution and retained controls.

**Original documentary anchors**, independently rechecked on the public archival pages: [Cesaro 1965 justification](https://nsarchive.gwu.edu/document/28787-document-3-arpa-richard-s-cesaro-memorandum-justification-memorandum-project-pandora), [Cesaro September 1967 BIZARRE memo](https://nsarchive.gwu.edu/document/28792-document-8-arpa-richard-s-cesaro-memorandum-project-bizarre-top-secret), [April 1969 PANDORA meeting](https://nsarchive.gwu.edu/document/28794-document-10-arpa-meeting-summaryminutes-summary-pandora-meeting-attached-detailed), [1977 Heilmeier oversight response](https://nsarchive.gwu.edu/document/28798-document-14-arpa-george-h-heilmeier-letter-chairman-house-committee-commerce-science). These establish original U.S. RF research / exposure inquiries and mixed/inconclusive preliminary primate claims. The later negative/critical review and termination are already included in the prior repo; **this does not verify remote human behavioural control, let alone a link to Duga**. First-owner attribution remains unchanged.

## P2-F1 — actual Duga / Soviet Woodpecker HF radar is a new *separate physical identity*

Credible retrospective technical sources: [ARRL, Remembering the Woodpecker](https://www.arrl.org/news/surfin-remembering-the-woodpecker), [Wireless Institute of Australia, Rewind—The Russian Woodpecker](https://www.wia.org.au/newsevents/news/2008/20081221-1/index.php), and the *Monitoring Times* 1980s contemporary-reception/engineering descriptions in [Radio History archive](https://www.worldradiohistory.com/Archive-Monitoring-TImes/1980s/Monitoring-Times-1988-12.pdf). The 1976 declassified **President's Daily Brief** mentioned in [secondary original-object locator](https://coldwar.tech/systems/duga-radar) is a valuable archival lead, **but the exact briefing page was not independently retrieved**, so do not present it as directly inspected primary evidence.

The "Woodpecker" was a **Soviet over-the-horizon radio radar** associated with anti-missile early warning. Historical monitoring gives *HF carrier* in the **approximately 7–19 MHz** range, **pulse-repetition/periodic modulation typically around 10 Hz** (reports also mention other pulse-rate settings), and wide shortwave reception/interference from 1976–1989. These are different physical quantities: radio carrier (MHz), repetition period (about 100 ms) and baseband repetition detected in receiver electronics. The audible 10 Hz rhythm when demodulated is **not equivalent to direct free-space 10 Hz radiation**, proof of Schumann coupling or a biologically targeted signal. The actual antenna/waveform, ionospheric backscatter, spectral leakage, near fields, source power and receptor field need their own measurements.

**New [SymPy discriminator](../../scripts/radiobio_p2_duga_pulse_carrier_sympy.py)** models a fixed carrier f0 with sinusoidal 10-Hz modulation. Exact identity:

    [1 + m cos(2π f_r t)] cos(2π f0 t)
      = cos(2π f0 t)
      + (m/2) cos(2π(f0+f_r)t)
      + (m/2) cos(2π(f0-f_r)t).

At an **illustrative** 10 MHz carrier and 10-Hz repetition, the three *RF* lines are 9,999,990, 10,000,000 and 10,000,010 Hz, not a transmitted standalone 10-Hz line in this idealized LTI/AM model. Ideal square-law **detection** creates 10-Hz and 20-Hz **baseband components at the receiver**. Pulsed radar has a more complex broadband/windowed RF spectrum than this simple sinusoidal fixture; the test is a **negative control** against frequency conflation, not a reconstruction of the Duga waveform or an absolute assertion that any antenna can never radiate LF currents. 10 Hz is also not 7.83 Hz Schumann resonance, even if spectral tails could overlap without measured data.

A local SymPy exact-identity test PASSED; the **committed script is not separately exact-blob locally executed** in this addendum. No original Duga instrument samples, receiver field measurements or health outcomes analysed.

## P2-F2 — alleged 1965 "Project/Operation Lazarus" source identity

The earlier [living RadioBio roadmap](../roadmaps/RadioBioHumanAlphaBetaBioelectricFieldCrossDomainRoadmap20261122.md) already classified a viral **1965 DARPA "Operation Lazarus" electromagnetic regeneration project** as **unverified**. Present searches did **not** find an original government project order, programme budget, dated contract, technical report, archived experiment or original dated scanned document tying the *specified name, 1965, and EM limb regeneration* into a common source. A later commentary [Arcanum "Operation Lazarus"](https://arcanum.thefeyseam.ca/topic/operation-lazarus-and-the-body-electric) likewise describes the legend's combination of independently real Becker bioelectric studies and later DARPA research but is a **secondary interpretation**, not proof of absence in every possible archive.

**Admission status: UNAUTHENTICATED-NAME / NO ORIGINAL OBJECT LOCATED.** Do not interpret lack of search results as proof of nonexistence or invent an archive record. Original Robert Becker 1972 [DOI 10.1038/235109a0](https://doi.org/10.1038/235109a0), the unrelated 1960s PANDORA original archive, and modern BioDome/BETR work have their own object identity and date. They cannot pay the missing Lazarus primary document merely by thematic overlap.

## P2 cross-domain source-identity table

| Source | Actual evidence type | Mechanism | Original primary object status | Cross-domain promotion |
|---|---|---|---|---|
| PANDORA/BIZARRE | Declassified original ARPA/CIA/RAND records | RF exposure/animal behavioural investigation | **Already owned in repo** | Historical RF study only; no proven human remote control |
| Duga | Contemporary monitoring + technical/historical retrospectives | MHz ionospheric OTH radar with ~10-Hz pulse rhythm | Radar existence documented; original Soviet circuit/radar data and cited 1976 PDB exact page still open | Frequency discriminator and propagation comparator, not biology |
| Alleged Project Lazarus (1965) | Viral/post-hoc narratives | Claimed EM DNA repair and human tissue regeneration | **No authenticated original order/record found** | No project-specific causal or administrative edge |

**Next independent sources:** original 1976 PDB page and Soviet radar engineering measurements, with dates and units; Lazarus only if a scan with accession can be produced. Move to source-grounded platform work instead of repeatedly attempting blocked Dryad URLs. All source and independent author priority obey [source-attribution policy](../SourceAttributionPolicy.md).
