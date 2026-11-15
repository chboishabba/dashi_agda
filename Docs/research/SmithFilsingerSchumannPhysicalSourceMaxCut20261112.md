# Smith/Filsinger physical environmental-source scale: Schumann Maxwell cut (2026-11-12)

## Source-physics result
The original Smith claim (compiled Fig. 6) is **8 kV × 20 A** output vs **12 V × 1 A** driven input: the reported output product is **160 kVA**, not verified 160 kW unless simultaneous same-load, correctly scaled RMS V/I/power-factor or equivalent DC measurements establish real power. CONDITIONAL net additional real power if 160 kW useful output and 12 W drive is **159,988 W + losses + storage accumulation**. No genuine Earth/Schumann/particle source inferred from voltage alone.

Earlier Filsinger **29.22075 kW** was computed from a 3.33µF capacitor at 1500 V being fully dissipatively recharged at an assumed electrical 7800Hz. This differs physically from Smith's **159.988 kW** claimed surplus. The 7800Hz acoustic carrier was not shown to be the electrical oscillator or a multiple of 7.83Hz with mode transfer.

## Maxwell physical field scale, explicitly conditional
Research measurements of the global Schumann resonance give approximate 7.8Hz fundamental, Q~5, E spectral amplitude ~0.3 mV/m/sqrt(Hz), B~1 pT (representative values, location/time dependent): https://doi.org/10.1088/0004-637X/750/1/85 . Schumann oscillations occupy Earth's lossy surface–ionosphere cavity and derive primarily from lightning; fields are partly standing, so **E²/Z0 is NOT a justified measured net forward Poynting flux**.

For an illustrative 1Hz measurement bandwidth, E_rms = 0.0003 V/m. Treating that field **solely as a hypothetical freely travelling plane wave** gives S_proxy=E_rms²/376.730313668≈2.389e-10 W/m²; to deliver 159988 W under ideal extraction needs *effective* aperture A=6.697e14 m², ~1.31 Earth surface areas (Earth surface ~5.101e14 m²). It is a benchmark for weakness of typical Schumann field, not a strict aperture or local harvest bound. By contrast E=1V/m hypothetical travelling RF field gives 6.027e7 m² (60.27 km²). Do not conflate global cavity total energy with collectable field power at one port.

Independent magnetic loop sanity: for B_rms=1pT, f=7.83Hz, N=100 turns and A=1m², open-circuit emf rms~2πfNAB≈4.92nV. Without measured coil impedance, resonance Q, field coherence, voltage/current phases, this cannot be translated to useful real power. For a hypothetical 1Ω matched series source load, max useful ~6.05e-18W, but source winding impedance of actual 100-turn 1m² coil is unmodelled and 1Ω assumption is purely illustrative.

## What physical source testing must actually solve
1. Extract measured local vector E(t),B(t) cross-spectrum at ELF and compare receiver vector effective height/area, admittance/impedance and electrical/acoustic transfer f(t).
2. Use actual Maxwell/Poynting flux boundary integrals with travelling and standing components separated, or calibrated Thevenin/Norton equivalent at the **measured receiver port**: `P_env = ∫ v_env(t) i_env(t) dt` with known signed reference and controls.
3. Keep Earth electrochemical/geoelectric, atmospheric fair-weather current, ambient RF and ionizing cosmic-ray particle deposition as distinct source hypotheses: a worldwide resonance is not automatically an available local 160kW supply.
4. For physically grounded energy claims, measure actual output *real* power (not kVA) and storage changes. Passive reciprocal multi-secondary simulations show reflected loading, but additional source can be represented once independently observed.
5. Against Don Smith's strong claim, infer the *required* source flux/coupling from power, then compare with observed flux; do not treat fitted source current as an independent demonstration.

## Implementation
Local standard-library script `/mnt/data/schumann_physical_source_audit.py` passed 8/8 tests and wrote `/mnt/data/schumann_physical_source_results.json`; original numerical scenarios remain illustrative, not device-calibrated Maxwell eigenmode solutions. No original instrument, Agda kernel or lab receipt claimed.
