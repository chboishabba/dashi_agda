# Polarity maximum cut: two physically distinct countermodels

This tranche extends the inherited [component graph PR #1482](https://github.com/chboishabba/dashi_agda/pull/1482), this stacked [adapter PR #1487](https://github.com/chboishabba/dashi_agda/pull/1487), conditional [power comparison PR #1486](https://github.com/chboishabba/dashi_agda/pull/1486), and [Tesla/Schumann PR #1464](https://github.com/chboishabba/dashi_agda/pull/1464). No new generic circuit ontology is introduced.

## Source-bound physical observation
The original narrator identifies the white capacitor as 3.33 uF and refers to its *hot terminal* as going to the *Earth-negative side*. This is retained as the sole candidate connection, not a measured end-to-end trace. The claimed meter going negative could mean the meter reference changed or the capacitor itself reversed polarity; the video does not establish its terminals. A viewer's hypothetical elevated antenna is retained as an *assumption* only. A ~7.8kHz acoustic line does not itself calibrate the electrical oscillator.

## Completed executable countermodels

### M1: floating return
Define `V_hot = V_return + V_cap`. Hold `V_cap=+1500 V`. At first instant `V_return=-1000 V`, so `V_hot=+500 V`. At a later instant `V_return=-1600 V`, so `V_hot=-100 V`. A ground-referenced meter on the hot terminal changes sign even though the differential capacitor voltage has **not changed sign**. These numbers are fabricated *countermodel inputs*, not measured values.

### M2: true lossless LC sign reversal
With *hypothetical* `L=125 uH`, the reported `C=3.33 uF` gives ~7.8 kHz. For an ideal LC tank starting at `V_cap=+1500V` and zero inductor current, `V_cap(t)=1500 cos(t/sqrt(LC))`. At half a cycle, the capacitor measures `-1500V`, while stored capacitor energy is again 3.74625 J. This sign change needs no new energy input: stored energy circulates reactively.

**The two models are counterexamples to the inference `meter reads negative -> cosmic-ray/environmental energy`.** They are not deductions of the device's internal connectivity or demonstration of its actual operating LC parameters.

### M3: full dissipative recharge impossible using only reported power
If a fresh 3.74625 J had to be provided on **every** hypothetical 7800Hz cycle, the required average new energy input is 29,220.75 W. The reported 6.7W is insufficient for this model. By contrast, resonant recycling is compatible with much smaller real input. Never infer frequency of the electrical clock from microphone data.

### M4: source-power non-identifiability
Two illustrative budgets with `drive=6.7 W` and `load=2 W` but `ambient=0 W, loss=4.7 W` versus `ambient=1 W, loss=5.7 W` both conserve energy. Therefore visible supply, meter, and sound cannot determine ambient-port power.

## Execution / remaining gates
The standalone Python module `scripts/filsinger_polarity_countermodels.py` expresses all five assertions using exact fractions where possible, plus the analytic ideal-LC cosine. An equivalent independent local Python model ran five tests successfully on 10 Nov 2026; **the committed GitHub script has not been checked by CI**. Agda 2.9 kernel verification of the stacked component-graph adapter remains unperformed.

Next experimental discriminator: calibrated simultaneous signed differential voltage across the **white capacitor**, hot-to-Earth meter voltage, return potential against an independently isolated reference, and real drive/Earth-port power. Without both meter terminals and dynamic input currents, neither M1 nor M2 can be excluded.

No user should handle or probe an exposed multi-kilovolt assembly without qualified electrical laboratory safeguards.
