# Filsinger circuit adapter — max-cut integration, 2026-11-10

## Exact donor and ownership
- [Resonate369 #1482](https://github.com/chboishabba/dashi_agda/pull/1482) is the **canonical** shared circuit owner: `Circuit36927ComponentGraphExact` contains component kinds, dimension-tagged values, pin/node/wire graph and route composition; `Circuit36927SearchBridgeExact` consumes A* and phase refinements without claiming KCL/KVL; `Resonate369SchematicAdmissionExact` supplies selected-source admission and no-bypass/series gates.
- [Filsinger/Lyden #1486](https://github.com/chboishabba/dashi_agda/pull/1486) is the independent **conditional numerical audit** for capacitor energy, 7.8kHz hypothetical cycling and environmental collector-source underdetermination.
- [Tesla #1464](https://github.com/chboishabba/dashi_agda/pull/1464) remains the historical 6Hz/Schumann and receiver-physical-source owner.

## Delivered
`FilsingerLydenCircuit36927AdapterExact.agda` imports the exact shared circuit carrier instead of reimplementing electrical components or path search. It represents:
- 3.33uF **white** capacitor, 2-pin, nominal label verified by narration
- 2uF **blue** capacitor, **tentative** label only, actual circuit connection unknown
- 15V reported supply; true metered power and relation to other digital display unknown
- toroidal magnetic winding of unestablished inductance and role
- Earth-negative terminal
- the **single reported** source-side wire from the *white capacitor hot terminal* to *Earth-negative*, with pin 0 chosen as **model-only orientation**

A source-specified candidate circuit of five components and one narrated connection is *not* a full physical schematic. It cannot prove a wire exists in situ. Other paths were not guessed. Explicit selectable proof records require real connection admission, calibrated electrical clock, signed earth power and meter polarity, complete storage and losses.

## Numerical consequences (from companion #1486)
- `E(3.33uF,1500V)=3.74625 J`
- at ideal reported 6.7W input, zero-to-1500V fill time >=0.55914 s
- hypothetical full discharge-and-recharge at 7800 Hz dissipates 29220.75 W: ruled out if the only source is 6.7W. **Lossless/low-loss LC recirculation is not ruled out.**
- the 7.8kHz is acoustic, **NOT** an established electrical oscillator frequency
- a proposed antenna/elevated collector is a justified *hypothesis* from the Lyden comparator, but **neither an observed antenna nor a physical 15-metre height claim**

## Exact remaining proof/measurement seam
1. **A1** Kernel-check actual Agda import ancestry on the #1482 branch (not run by GitHub connector; no kernel PASS claimed).
2. **A2** Distinct evidence-bearing pins and manufacturer/inspector trace, identify diode bridges, meter terminals, blue bank and Earth electrode; only then strengthen the candidate graph.
3. **A3** Electrical `v(t),i(t)` input and ground-port traces together with switched waveform, not acoustic proxy.
4. **A4** Selected source/return separation and grounded/un-grounded matched controls; separate galvanic, atmospheric, RF and 7.8Hz ELF channels.
5. **A5** Integrate calibrated electrical constitutive laws, KCL/KVL and dynamic losses with the shared graph, rather than treating a graph route as a physical conducting pathway.
6. **A6** Measured physical Earth-ionosphere mode coupling before promoting Schumann interpretation.
7. **A7** Git-ancestry integration: this is a *stacked* adapter on #1482 and a *companion* to #1486, not a silent copy of either unmerged tree.

## Source provenance
Filsinger is the recording narrator; Lyden is the distinct patent inventor; Tesla the distinct historical source. No claimed energy gain, environmental charge transfer, 15m aerial, rectification path, diode identity, or digital controller has been elevated from hypothesis to observed measurement.
