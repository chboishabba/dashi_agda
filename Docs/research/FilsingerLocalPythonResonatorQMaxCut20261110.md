# Local-Python maximum-cut validation (2026-11-10)

The local primary validation route is Python, not CI. This is a companion to the model and source-bounded netlist in PR #1487. The Python workspace program `filsinger_local_maxcut.py` executed **12/12 tests passed** (no Agda-kernel receipt). Original earlier local scripts separately passed 5/5 polarity tests and reproduced capacitor/collector arithmetic.

## New strongest conditional discriminator: Q / effective tank capacitor

For an *assumed electrical* resonance `f=7800 Hz`, peak voltage `V=1500 V`, oscillator storage `U>=0.5*C*V²`, and measured real input `P=6.7 W` available to cover ALL tank dissipation, `Q = (2*pi*f*U)/P_loss`.

If the whole white `C=3.33uF` capacitor swings as the RF tank, `U=3.74625 J`, and sustaining it with just 6.7 W requires **Q >= 27,403** (a lower bound; extra dissipation increases required Q). This is a stringent conditional requirement; not proof of impossibility.

Conversely for `Q=50`, maintaining 1500V peak at 7800Hz from 6.7W requires an effective tank capacitance **<= 6.076 nF**; for Q=100 **<= 12.15 nF**. This supports testing the alternative that the white 3.33uF capacitor is HV storage and a separate small tank capacitance controls the audible resonance. No actual electronic frequency, Q, tank connections or voltage amplitude is measured.

Other local receipts: 3.74625J white cap; ideal minimum zero-to-1500V fill 0.55914s at 6.7W; 29.22075 kW fully dissipative refill every 7800 electrical cycles; ideal LC inductance 125.03uH for 3.33uF and 7800Hz; full-reset 1500V collector needs 0.764nF at 7800Hz **if** independently replenished (or 0.761uF at 7.83Hz). These must not be interpreted as actual environmentally harvested power.

## Specific source boundary

- Original speaker: *white capacitor hot side* directed to Earth-negative; only half bridge used. Physical conductive continuity, return terminal and meter leads are unverified.
- Original 7.8kHz signal: **acoustic**. A laboratory switching waveform is required to identify the electrical `f`.
- Lyden Earth/atmosphere switched-ground patent supplies comparison, not identity.
- Tesla's 6Hz historical proposal and 7.83Hz Schumann mode do not provide a measured Filsinger mode coupling.
- At 1500V, a source-connected capacitor can show Earth-referenced negative terminal potential due to floating-reference movement without true reversal across its plates; an ideal LC tank can also reverse differential capacitor voltage. Neither demonstrates environmental input.

## Exact remaining P0 -> P1

P0: Agda kernel-check; determine selected port terminals and conductor trace, regulator metering meaning, tank C/L/Q, measured electrical clock and capacitor voltages. P1: signed Earth-port energy, atmospheric/ground chemistry/RF controls; source-loss-storage integration. P2: measured independent ELF field coupling. No CI dependence.
