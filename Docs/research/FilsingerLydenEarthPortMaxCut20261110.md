# Filsinger × Lyden × Tesla — environmental-port maximum cut (2026-11-10)

## Source and attribution
- **Original Filsinger recording:** narrator describes the **hot side of the white 3.33 µF capacitor** as connected toward **Earth-negative** and says only part of an unspecified bridge is in use. The narrator reports 15 V and about 6–7.3 W, a high-voltage output, and polarity changes. These are narration/display observations, **not independently calibrated power-port measurements**.
- **Audible source:** one subsecond activation transient, followed by narrow ~7.8 kHz acoustic tone. Actual electric switching frequency, digital controller, resonant tank, core saturation, and signed voltmeter reversal are **unverified**.
- **User hypothesis:** an elevated antenna or other environmental collector exists outside the camera's view. **Working assumption only**; no observed 15 m antenna. The 15 m example was hypothetical.
- **Robert M. Lyden:** [US11588421B1](https://patents.google.com/patent/US11588421B1/en) and [US12136824B2](https://patents.google.com/patent/US12136824B2/en) disclose switched antenna–Earth connection, capacitor/diode/coil/rectifier/resonant options. Figures 10–11 of the latter describe capacitor/DC-multiplier and inductor/amplifier branches. Patent disclosure **does not verify** physical efficacy or establish that Filsinger uses Lyden's topology.
- **Nikola Tesla:** [US787412A](https://patents.google.com/patent/US787412A/en); reuse existing [DASHI PR #1464](https://github.com/chboishabba/dashi_agda/pull/1464) for patent 6 Hz, measured Schumann ~7.83 Hz, finite spectral ledger and coupling non-identifiability. Do not attribute modern formal mathematics to Tesla.

## Partial device topology
```
reported DC operation (~15 V, ~6.7 W)
          |
    toroidal magnetic / switched power stage (candidate)
          |
     bridge / high-voltage distribution (incomplete)
          |
  white capacitor (3.33 µF)
          |    observed *narration*, not electrically traced continuity
  hot terminal -> Earth-negative contact
          |
    other HV nodes / separate blue HV capacitor (tentative ~2 µF, 10kV)

[elevated antenna / collector hypothesised] --[NOT VERIFIED]-- [environment]
```
The Earth connection could be a return, reference, counterpoise, transient capacitive path, or a **source**. Only signed real-power flow can distinguish them.

## Quantitative maximum cut — conditional calculation
Assume P=6.7 W is *measured* electrical input and hypothetical electrical clock f=7800 Hz (the latter is **only acoustic**, so conditional):
- White capacitor at 1500 V: `E=CV²/2=3.74625 J`, ideal 6.7 W initial fill `t>=0.55914 s`.
- Recharging it **fully from zero** every 7800 Hz cycle: `E*f=29220.75 W`, `C*V*f=38.961 A` mean one-way charge rate. Impossible from just 6.7 W if that energy is dissipated each cycle; **not** an argument against lossless/reactive LC energy exchange.
- If all 6.7 W charged from zero *each cycle*, maximum end voltage is `sqrt(2P/(Cf))=22.713 V`. If it starts at 1500 V each cycle, maximum incremental upward step is `sqrt(1500²+2P/(Cf))-1500=0.17196 V`. Neither is a bound on reactive oscillation voltage.
- Hypothetical environmental *collector* switched over a full 1500 V potential, `P<=0.5*C_env*(1500)²*f` **only under** full charge/reset, lossless transfer and independently replenished environmental potential. To sustain 6.7 W, `C_env >= 0.764 nF` at 7800 Hz, versus `C_env>=0.761 µF` at 7.83 Hz. Example `C_env=100 pF` -> `0.8775 W` ideal per-cycle expression at 7800 Hz; this is not an achieved harvest, nor a universal antenna bound.
- Audio-to-Schumann numerical ratio `7800/7.83=996.17`, not an exact 1000. No measured ELF phase lock.

## Identifiability counterexample
Two *illustrative* energy-conserving worlds share the same reported 6.7 W drive and hypothetical 2 W useful output:
- A: ambient 0 W, loss 4.7 W.
- B: ambient 1 W, loss 5.7 W.
Thus visible voltage/current/sound observations do not identify environmental power without actual loss, storage, load and signed Earth-port measurements. This reuses the style of PR #1464's same-height/distinct-coupling counterworlds without promoting a toy world into physical evidence.

## Exact measured closure contract
`W_env = ΔU_all + W_load + W_loss - W_drive - W_other_sources`
with simultaneous calibrated time integration of **v(t)i(t)** for AC/switched input and Earth ports, not multiplication of unrelated average readings. Include capacitor and inductor changes, electrode chemistry, power supply, atmospheric/RF sources and measurement effects. Meter polarity requires both terminal references and a genuinely signed instrument.

## Remaining highest-alpha gates
1. **P0** Verified device conductor netlist: preserve narrated white capacitor hot→Earth-negative edge; identify rest of bridge, both voltmeter terminals and grounds.
2. **P0** Actual electrical clock vs acoustic 7.8 kHz; measured real-power input and capacitors' complete synchronized voltage time series.
3. **P0** Signed ground and hypothesized elevated collector port energy (with appropriate environmental field/counterpoise controls).
4. **P1** RF vs ground electrochemistry vs time-varying geoelectric/atmospheric excitation, holding driven bias constant across matched conditions.
5. **P2** Independent ELF field and measured source-to-mode-to-receiver transfer before making a Schumann claim; reuse existing Tesla #1464.
6. **P0 verification** Agda formal proof owners are NOT added or kernel-claimed by this documentation-only tranche.

Do not infer energy source from patent grant, electrostatic field focusing, capacitor voltage, meter polarity or audio alone. High-voltage work is exclusively for qualified specialists.
