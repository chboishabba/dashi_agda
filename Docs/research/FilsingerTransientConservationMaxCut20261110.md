# Filsinger time-dependent conservation max-cut — 10 November 2026

## Relationship to existing PRs
Continues #1487, stacked on #1482's circuit/pin/connection abstractions, and reuses #1486's energy accounting and #1464's Tesla/Schumann non-promotion boundaries. No new circuit ontology, no CI dependence. Local Python script `/mnt/data/filsinger_transient_budget_maxcut.py` executed **20/20 tests** on 2026-11-10. A compact standard-library version is committed here as `scripts/filsinger_conservation_transient_maxcut.py`; execution of that exact GitHub file is *not* independently claimed.

## Strongest new gate: startup time is not charging completion
Given narrated C=3.33uF, target V=1500V, and an explicitly **conditional** assumption of initially discharged capacitor, real available power `P=6.7 W`, 100% conversion, and *no other energy stores*:
- Stored energy 3.74625 J
- Voltage reachable at time t is at most `sqrt(2*P*t/C)`.
- At 0.1s: 634.35 V; 0.2s: 897.11 V; 0.3s: 1098.73 V; 0.5s: 1418.45 V.
- Minimum charge time to 1500V is 0.55914s at 100% or 1.11828s at 50% charging efficiency.
- If the capacitor really went from zero to 1500V in 0.3s, average **power into that capacitor** would have to be at least 12.4875W, exceeding the reported 6.7W by 5.7875W. Its energy gap is 1.73625J, but this gap cannot uniquely be attributed to Earth: initial precharge, a second external source, earlier stored magnetic energy, or a meter/source interpretation error are alternatives.

The recorded *single startup acoustic event* around 34.7–35.0s is not independently a measurement of `V_cap(t)`. Therefore **we cannot claim** an actually witnessed sub-0.559s full charge.

## Multiple banks
If, only hypothetically, the white 3.33uF and blue 2uF capacitors both start discharged and BOTH reach 1500V, combined storage is 5.99625J and minimum 6.7W fill time is 0.8949626866s. The blue capacitor value is a tentative image read; there is NO evidence both charged to the same voltage.

## Optimiser limitation and correction
The previous optimiser assumes conversion gain, Q and charging efficiency can be varied independently; unsurprisingly the fastest corner selects the most optimistic values. It is a **parameter feasibility scan, not a robust or physically certified optimum**. A valid physically constrained optimisation needs a measured converter efficiency map vs voltage/current/frequency, turn ratio and magnetic core limits, rectifier loss, thermal envelope, part ratings, capacitance/load dynamics, actual two-port source response and uncertainty/cost constraints. Ideal unavailable-port energy is not free energy. Do not promote a fixed `7.8kHz` audio tone to electrical resonance or connect it to Schumann's 7.83Hz without measured transfer.

## Polarity and source
Two existing toy counterworlds remain possible: the hot-to-Earth voltage crosses zero while differential capacitor polarity remains positive; or a genuine LC oscillation reverses differential capacitor polarity. Both are source-independent as mathematical models. Existence of charge collection from a biased conductor does not prove net positive environmental work.

## P0–P2 genuine remaining cut
P0: Actual electrical diagram and bridge return; 2 signed meter terminals; calibrated `V_cap(t)` synchronized to button, `P_input(t)` and other reservoirs; kernel-check Agda on inherited PR #1482 lineage.
P1: Measure loaded Q, switching waveform, converter losses and ground/antenna `v(t)i(t)` under controlled source configurations, including electrochemical and RF nulls; bound ambient energy with uncertainty.
P2: only after P1, test separately measured ELF source-to-Schumann-to-device transfer. Never attribute verified device efficacy to Lyden/Tesla merely from patent disclosures.

All numerical bounds are energy-conservation statements, not operating/build instructions for exposed lethal high-voltage equipment.
