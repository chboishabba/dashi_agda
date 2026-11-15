# Filsinger new original reel: ZVS + parallel megohm shunts — 2026-11-10

## Attribution and evidence
Primary material: user's supplied transcript of Instagram reel https://www.instagram.com/reel/DfiqPnkPnP5/ and screenshot. Instagram was not directly fetched; transcript is the primary accessible narration. Narrator expressly calls the driver "ZVS", says the analogue meters are "one mega ohm resistor", places resistance across each capacitor, uses 3.3uF with nominal 1MΩ loading, and explores different 2uF capacitors with "two megaohm resistors" (AMBIGUOUS: two physical resistors or nominal 2MΩ each). Claims voltage-tuned frequency and resonance. This replaces prior guesses as to whether driver was ZVS, but does not establish Mazzilli versus other ZVS topology, physical netlist, actual electrical frequency or energy source.

## Exact correction to source mechanism
For simple shunt R||C, tau=RC, corner=1/(2πRC). These are not LC resonant frequency. Ideal parallel RLC has f0=1/(2π√(LC)), and R determines damping/Q/loading rather than fixing the LC frequency; in more complex networks, dissipative loading can affect observed peak frequency. The resistor CAN influence observed voltage peaks and driver operating point and is therefore potentially causally important.

3.33uF*1MΩ=>RC 3.33s, f_RC .047794Hz. 2uF*2MΩ=>RC 4.0s, f_RC .039789Hz. For 2uF*1MΩ=>RC 2.0s, f_RC .079577Hz. Those are not 7.8Hz or 7.8kHz. Do NOT interpret "1 megahertz" in narration as a stated oscillation frequency: he corrects to megaohm.

At F_AUDIO≈7800Hz, 3.33uF has |X_C|≈6.127Ω, so 1MΩ shunt would have a very small direct effect on ideal sinusoidal tank AC admittance (~163k ratio). That suggests the shunt influences low-frequency/DC bias, leakage, measurement burden, or complex controller/loading, rather than directly tuning a 7.8kHz LC tank by itself. If that full 3.33uF capacitor has 1500V *sinusoidal peak* at 7800Hz, it would require ≈245A peak reactive capacitor current; this isn't directly compatible with a casual 6.7W real input as a lossy full-charge cycle, but ideal reactive circulation is distinct from power consumption.

## Important bleed/shunt power constraint
For each actual 1MΩ resistor across DC 1500V, P=V²/R=2.25W, I=1.5mA; two banks at 1500V draw 4.5W. If **6.7W is total real electrical input**, at most 2.2W remains for converter losses/auxiliary/charging once both have reached 1500V (before other losses). At 4000V across one 1MΩ resistor, P=16W; thus the reported 4000V indicated on a meter cannot be assigned to that 1MΩ shunt under a 6.7W steady-source model without separately explaining power/storage. At 10kV, 2MΩ dissipates 50W *per resistor*. No 4000V/10kV figure was verified across any particular shunt.

## Exact constant-power ideal charging with bleed resistance
Assume n identical shunted C banks begin at zero, share constant available charging power P equally, and only loss is V²/R per bank. Then
d(0.5*n*C*V²)/dt = P - n*V²/R,
V²(t) = (P*R/n)*(1-exp(-2t/(R*C))).
Reaching target V requires P*R > n*V².
t = -(R*C/2)*ln(1-n*V²/(P*R)).
At P=6.7W, 3.33uF, 1MΩ, 1500V:
- one cap: 0.681324s ideal minimum with bleeder (vs 0.55914s absent bleeder);
- two caps: 1.85423s ideal minimum with bleeders (vs 1.11828s absent bleeders).
- two 2uF/2MΩ caps: 0.818407s ideal minimum to 1500V if these are the resistance and capacitance of two identical banks, not verified wiring.

These are conditional optimistic bounds; real conversion inefficiency, initial precharge, time-dependent input, independent sources, unequal branches, and device topology alter results. If supply source is not actually measured real input, even bounds do not apply to actual equipment.

## Meter discrepancy
Earlier visible 100uA meter movement with 0–10kV display would need ≈100MΩ *total equivalent resistance* for full-scale direct DC measurement (10kV /100uA). A 1MΩ resistor across 10kV would dissipate 100W and draw 10mA. Therefore narrator's "meters are one megaohm resistor" might describe an added parallel shunt rather than full-scale meter series resistance, a separate meter model, or an inaccurate statement. Need inspect specific meter terminals and manufacturer's scaling.

## Repo integration and residuals
Reuse original #1482 `Circuit36927ComponentGraphExact`, stacked #1487 source-bound netlist, #1486 energy model and #1464 historical Tesla/Schumann separation. Add nominal 1MΩ shunt resistors only as **speaker-asserted candidate** parts, not installed physical wires. Replace prior assumption of negligible load; rerun earlier 0.88s optimisation with explicit shunt power once both banks are known to be at HV. Do not claim Schumann coupling, environmental net power, or unique Mazzilli ZVS topology from narration.

P0 = inspected wiring for which resistor across which capacitor, exact resistor vs meter identity; calibrated capacitor-voltage time traces; ZVS driver transistor/topology and switching waveform; real input P(t).
P1 = realistic source/load/reflected impedance, thermal dissipation, capacitor charge control and ground/collector signed work.
P2 = independent ELF source measurement and receiver transfer, if pursued.

Source attribution: narrator's explanation is hypothesis/observation; canonical RLC derivations are established circuit physics (e.g. Simon Fraser University parallel-RLC notes; Clemson electronics laboratory documentation).
