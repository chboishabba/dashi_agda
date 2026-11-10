# Filsinger new Earth-ground reel × ZVS ±5 Hz frequency-pulling cut (2026-11-10)

## New primary source
User-supplied transcript and screenshots, Instagram reel `Dfi1D7CPzyM` (direct platform fetching not available). Narrator reports approximately **3.8 V**, **0.4 W**, **48 V across two capacitors**, shows three electrodes described as Earth grounds, and asserts ground potential supplies energy. Preserve exact observation vs attribution. Cannot infer whether 0.4 W is supplied, delivered, or displayed power, or whether 48 V is across the whole series pair, each capacitor, or a different wiring mode. Neither the identity/spacing nor material of electrodes is established. Galvanic electrode chemistry, common-mode and ground-return effects, external supply and stray pickup remain unexcluded. A third ground can provide a potential relative to another ground without being an independent unlimited energy source.

## User's correct frequency question
The prior acoustic peak was ~7.8 **kHz** with small **±5 Hz** variations around the carrier. User was NOT claiming a 7.8 Hz modulation. Fractional 5 Hz change at 7800 Hz is 0.000641 = **0.0641%**; for ideal LC `f = 1/(2π√LC)`, this corresponds to ~0.1282% change in LC product. Small active ZVS frequency pulling can in principle account for it.

## Fully specified direct parallel-RLC damping countermodel
Take a fixed L,C and an ideal parallel shunt R with damped natural frequency `fd(R) = f0 sqrt(1 - 1/(4*(2πf0RC)^2))`. Compare **R=1 MΩ vs 2 MΩ**, assume f0 = 7800 Hz ONLY conditionally (electrical frequency remains unverified).
- C=3.33 µF: shift **2.75e-8 Hz**, negligible.
- C=100 nF: **3.04e-5 Hz**.
- C=5 nF: **0.01218 Hz**.
- C=250 pF: **4.874 Hz**.
- Exactly 5 Hz requires effective C≈**246.825 pF** in that oversimplified branch and matching ideal L≈**1.687 H**, which is an implausibly large simple 7.8 kHz inductor; it is NOT an inferred physical capacitor or topology. The relevant branch may be a parasitic or feedback network, in which case this toy damping relation need not apply.

Thus a mere 1MΩ change across the narrator's **3.33 µF** does NOT directly explain ±5 Hz by ideal RLC damping. But ZVS load pull is an entirely different sensitivity mechanism: `Δ ln f / Δ ln R = (5/7800)/ln(2) ≈ 9.248e-4`. This is only ~0.0925% frequency response per e-fold of resistance, a modest possible sensitivity. Such a function can be posited mathematically, but actual driver circuit, switch/coil biases and load-dependent frequency must be measured to attribute causation. Cite general parallel RLC source, not a Filsinger-specific experiment.

## Shunt watts and second reel
At 1500V, changing 1MΩ to 2MΩ changes **one branch** dissipation 2.25W→1.125W (1.125W difference). Changing two identically charged shunts changes total loading by 2.25W. Such changes CAN pull the ZVS input/load even when direct RF tank admittance of a microfarad shunt is negligible.

At 48V, a true 1MΩ shunt dissipates **2.304 mW** (2MΩ: 1.152 mW), not 0.4W. Under hypothetical two independent 3.33µF capacitors each at 48V, their total energy = **7.672 mJ**. If they are instead two identical capacitors in series with 48V across the pair, total = **1.918 mJ**. If the quoted 0.4W and 3.8V are real power and corresponding terminal voltage on one device, current = **105 mA**, but simultaneous metering and connection are unverified. Do not infer generated output or sustained Earth harvesting.

## Executed local receipt
`/mnt/data/filsinger_zvs_frequency_ground_cut.py` ran **18/18 Python unittest PASS**; outputs `/mnt/data/filsinger_resistance_frequency_findings.json` and `/mnt/data/filsinger_resistance_frequency_scenarios.csv`. These are local artifacts, not GitHub checked-in files or CI results.

## Maximum physical proof cut
P0: identify the actual ZVS circuit/feedback and measure electrical f(t) simultaneous with acoustic f(t), resistor voltage/R(t), input source real power, and capacitor differential voltages. P0: identify Earth electrodes/materials, meter terminals, and whether 0.4W means source input or load output. P1: require synchronized source/earth port v(t)i(t) with electrochemical and RF null controls; all storage and loads included. P2: independent ELF/Schumann field coupling is still not shown. Preserve older PR #1482 generic graph, #1487 Filsinger netlist, #1486 energy accounting and #1464 historical Tesla gate.
