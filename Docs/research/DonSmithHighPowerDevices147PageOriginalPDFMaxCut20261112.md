# Don Smith original 147-page PDF: source-selected diagram audit and max-cut (2026-11-12)

**New user-provided document:** Brendan J. Darrer (editor), *The high-power devices of Don Smith* (2022), 147 pages, explicitly drawn from Patrick J. Kelly's *Practical Guide to Free-Energy Devices*. Kelly's introduction (PDF pp.4–6) says most devices were **not personally built or tested** and cautions that content is hearsay or opinion. Source strata: original claims as quoted, Kelly's reconstructions, Darrer's editing, and Filsinger's independent reels. Attribution and physical admission cannot be merged.

## Primary diagrams, distinct identities
| PDF page | Figure / case | Actual subject | Scope |
| 10–16 | Figures 2–5, patent-like dipole plates | Driven HV coil, metal/plasma dipole and capacitor plate orthogonal to dipole | Claimed conversion, not device-tested field-energy transfer |
| 17–18 | Figure 6 tabletop board | Caption claims 8 kV×20 A out from 12 V×1 A in; editor notes major components and ground connections missing from photograph | 160 kW / 12 W = 13,333 CLAIMED ratio, no simultaneous calibrated power receipt |
| 28 | Figure 10 | 'Resonant electromagnetic power system', attributed to 1996 suitcase | Separate schematic identity |
| 29 | Figure 11 | 'Electrical energy generating system', same historical family | Not the same original diagram as Figure 10 |
| 61–65 | Figures 34–40 / editor-supplied later diagram | Reconstructed output loading, variants, frequency/reactance chart and later circuit | Editorial alternatives, not Filsinger's observed ZVS |
| 67–101 | Chapter 4 practical implementation | Kelly's proposed implementation | Explicitly described as **opinion, not tried-and-tested working technology** |
| 106–147 | Chapter 6 Russian/Sergei implementation | Additional variant | Separate physical claim with its own source/evidence identity |

## Source-supported strongest similarities
- Smith compilation's loaded dipole/capacitor/coil/electrical output idea correlates with Filsinger's stated 'Don Smith commercial device' lineage. The exact commercial artifact is NOT identified by a generic Smith name alone.
- Kelly's discussion says limiting resistors are used across transformer output, and Figure 34–40 material discusses varying resistance and reactance/frequency. Filsinger specifically narrates **1, 2, 4 MΩ** across capacitive banks with a **ZVS** driver. This is a meaningful design-idea continuity, NOT an electrically identical circuit.
- Two distinct Earth connections appear in the Smith compilation as grounding/voltage/transient controls (pp.24–26), while Filsinger proposes an earth-harvesting branch and separately a portable midpoint/antenna branch. Those are not same-source power certificates.
- Filsinger uses white 3.33uF capacitors, three user-identified blue capacitors, candidate green HV rectifiers, toroids and powered control boards. Smith diagrams do not substantiate assigning unverified wires, prices, voltage ratings or external feed paths to these components.

## Quantitative audit and correction
* 30kHz at 100nF (pp.61–65): |X_C|=53.05165Ω and matching L=0.2814477mH, consistent approximately with the document's ~51Ω/~0.28mH estimate. That reactance is **not** a 1MΩ high-voltage shunt.
* 3.33uF at 1500V: stored energy 3.74625 J. One 1MΩ shunt at 1500V dissipates 2.25W.
* Smith's formula (pp.31–32) of (0.5 C V²)*f for watts applies to net energy transfer per cycle only. Recycling resonant/reactive energy is not new power each cycle.
* Smith's 8kV × 20A output versus 12V × 1A input (Figure 6) is physically extraordinary and not validated by its caption or uncalibrated meter readings. It needs drive/load waveform real-power integration, precharged stores and all external ports.
* Distinguish observable **7.8kHz acoustic carrier ±few Hz** from measured electrical switching; direct parallel-RLC damping due to changing 1MΩ→2MΩ across 3.33uF gives a negligible direct frequency change; active ZVS feedback and thermomagnetic/load changes may pull frequency.
* Earth/EM/ionizing cosmic rays are distinct possible source types; mere terms 'Heaviside current', 'ambient' and 'cosmic' do not identify energy flux or violate energy conservation.

## Formal owner/verification
New `DASHI/Physics/Motors/DonSmithOriginalPDFDiagramBidiExact.agda` reuses canonical `Circuit36927ComponentGraphExact` and `MaxwellExteriorCalculusAdapter`, assigns separate figure identities, pages, forward observables and *reverse required* same-source pin/measurement admission. No device circuit topology, field solution or source receipt is falsely inhabited. Continue existing `DonSmithFilsingerClaimBidiExact`, source-separating Earth and portable Filsinger proposals.

Local Python user-attached-PDF audit: `/mnt/data/don_smith_review/source_maxcut.py` executed **20/20 tests PASS**, plus machine-readable 9-claim ledger `claim_ledger.json`. The separately executed local Python script is a test artifact and may be committed subsequently; no Agda kernel acceptance or CI run claimed.

### P0–P2 residual
P0: Figure-by-figure faithful pin-level transcription from the actual images, distinguishing source author/editor and unknown/off-camera parts. P0: original 'commercial device' identity; complete source-specific netlist, including Filsinger board and bridge variants. P0: Agda 2.9/Nix same-revision typecheck.
P1: Solve physical antenna Maxwell eigenmode (loaded golden rectangle, feed/counterpoise/material); fit ZVS nonlinear load-pull with calibrated f,V,I,R and thermal state; determine electrode chemistry, ambient fields and real Earth/EM/particle signed port powers.
P2: demonstrate matched frequency/phase and actual physical mode transfer to any proposed Schumann carrier rather than numerical coincidence alone.

No electrical assembly/probing instructions are implied by this research audit; the shown exposed kilovolt components are potentially lethal.
