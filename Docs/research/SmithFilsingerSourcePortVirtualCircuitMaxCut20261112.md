# Smith → Filsinger maximum cut: physical-port conjecture and virtual circuits (2026-11-12)

## Core correction
**ZVS is a driver implementation, not the canonical mathematical object.** Canonical device = an externally driven resonant electrical network with real power source(s), reactive storage, environmental electromagnetic/Earth/particle coupling, rectification, bleeders and a useful load. Any drive implementation (ZVS, flyback, neon-transformer supply, switched resonator) must preserve port identities and physical energy accounting.

## Original source, scope, and attribution
Primary user attachment: Brendan J. Darrer (ed., 2022), *The High-Power Devices of Don Smith*, 147 pages, derived from Patrick J. Kelly. Kelly explicitly says most designs were not independently built or tested and should be read as hearsay/opinion (PDF pp4–6). Preserve Kelly's/editor's additions separately from Smith's claims and Filsinger's reels.

PDF pp13–16 Figs 2–5: powered dipole / perpendicular capacitive plates. p17 Fig 6: photographed tabletop 8 kV × 20 A out versus 12 V × 1 A in *CLAIM*. p28 Fig 10 and p29 Fig 11: DISTINCT 1996 suitcase schematics. p65 Fig 40 is a later editor-supplied circuit, NOT the unique Smith commercial device. Ch4 pp67–101 is an explicitly unverified editorial implementation; Ch6 pp106–147 is a separate Russian variant. The attached original is not one canonical netlist.

The book's pp24–26 output limiting resistors and grounding details make Filsinger's variable-megohm shunts a meaningful *functional lineage*, but not source-identical hardware. Filsinger's Earth-ground reels and proposed midpoint/antenna design are distinct configurations/occasions. The narrated white capacitor hot-terminal to Earth-negative edge is retained; not independently probed. Three blue HV capacitors and green HV diode candidates remain separately identified inventory, not assumed series/parallel wires.

## Local Python virtual circuit and receipts
`/mnt/data/smith_filsinger_maxcut/model.py`: **16/16 tests PASS**; explicit parallel RLC state variables V(t), I_L(t) and real external current inputs for drive and optional environmental port. It enforces
`d[0.5CV²+0.5LI_L²]/dt=V I_drive+V I_env - V²/R_load - V²/R_shunt - V²/R_internal`.
Finite-time integration verifies source work, useful output, shunt/internal heat, and storage change; residual <6.5e-8 J in the illustrated no-environment run. A modelled extra environmental input can boost output, but by explicit additional work, not by oscillatory VAR counted as new power.

`/mnt/data/smith_filsinger_maxcut/results.json` and `resonant_work_ledger.png` use **illustrative, NOT source-measured** values: 100 nF, 4.163 mH, assumed electrical frequency 7800 Hz, 2500Ω useful load, 20kΩ effective internal loss, 1/2/4MΩ shunt, 12W sinusoidal source. R=1MΩ gives ~10.643W load, 1.330W internal heat, 0.0266W shunt and ~130.4 var circulating reactive exchange at resonance. The acoustic ~7.8 kHz is not proven to equal an electrical tank frequency. Distinct low-current illustrative shunt operating voltages must not be confused with Filsinger's reported 1500V HV cap banks.

`/mnt/data/smith_filsinger_maxcut/source_graph.py`: **8/8 source/topology assertions PASS**, catalogues **123 figure captions** in the 147 page attachment, and exports five distinct *functional* graph variants `candidate_graphs.json` and `pdf_figure_index.csv`. These are **not complete terminal-to-terminal schematics**: full image/pin transcription for each figure is OPEN. Neither 123 caption records nor 16 numerical tests prove every circuit in the book works.

## Physically decisive Smith claim
At *claimed* steady 8kV ×20A delivered as real output and *claimed* 12V×1A real input:
- useful output = 160000 W; source drive = 12 W; minimal unidentified real input OR rate of storage depletion = **159988 W**, before losses;
- if sustained 60 seconds, energy gap = 9,599,280 J;
- purely resistive 8kV/20A load = 400Ω and would dissipate 160kW. Voltmeter indication alone is not evidence of 20A through that load.
- `0.5*C*V²*f` equals delivered real power ONLY if that energy is genuinely transferred to an external load at frequency f; in a lossless LC tank reactive energy can circulate each cycle with no net supply of such real power.

The **central conjecture is where any surplus REAL energy enters**. If an external energetic environment is the hypothesis, it must enter as `W_earth + W_atmos + W_RF + W_particles` and be signed/time-integrated with independent field data. `W_env = ΔU + W_useful + W_losses - W_drive` gives only a **net residual**; without measuring other paths and losses, it does not identify its source.

## Reused canonical formal owners / BIDI
Retain PR #1482 Circuit36927 part/pin/wire types, PR #1487 source-specific diagram and claim BIDI, `MaxwellExteriorCalculusAdapter` (symbolic homogeneous differential identities) and `PerfectConductorMaxwellSpectrumBidiExact` (forward spectrum and reverse field-equation obligations). No new unearned theorem of physical Maxwell eigenmodes, Schumann coupling, or ambient gain. Driver technology is a parameter of the same resonant network rather than an absolute historical identity.

Forward: source-qualified actual netlist + port excitations + loss/geometry -> signed time traces, power, phase, acoustic-correlate hypotheses. Reverse: original source diagram + measured input/load/earth/antenna ports + actual electrical switching vs audio + loss/storage -> device/source admission. Model equivalence is not physical-device identity.

## Max-cut remaining, ordered
P0: faithful terminal-level digitisation of the particular original Smith figures (especially 10, 11, 40, and patent plates), maintaining variant identities; select which is Filsinger's commercial-device reference.
P0: verify all Filsinger part-to-node connections and meter terminal sense, distinguish distinct reel occasions and actual driver switching frequency from ~7800Hz audio.
P1: nonideal transformer/rectifier, coupled nonlinear ZVS or alternative driver load pulling, phase and current trajectories under 1/2/4MΩ resistive shunts.
P1: Maxwell boundary eigenproblem of actual loaded golden rectangle and source-calibrated Earth/atmospheric/RF/ionizing particle ports; independent source flux and realistic extraction/heat.
P1: a complete real-power experiment with measured external source port(s), including grounded-vs-antenna configuration.
P2: source-specific Schumann/ELF transfer only if field and frequency coherence independently measured.
Kernel: Agda 2.9 with inherited PR #1482 remains unverified. Local Python results are not a device experiment, nor do they close all 123 figure interpretations.

No physical exposed multi-kilovolt construction is proposed; this is an analytical circuit simulation.
