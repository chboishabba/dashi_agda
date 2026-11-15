# Original-source Don Smith ↔ Filsinger reels: BIDI and steelman max-cut (2026-11-11)

## Status correction: earlier work did not finish original Don Smith formalisation
PR #1487 previously contained a **lineage markdown report**, finite circuit adapter and synthetic Lissajous / energy tests, but no source-claim BIDI for Smith or Smith-specific same-object netlist. This tranche creates `DASHI/Physics/Motors/DonSmithFilsingerClaimBidiExact.agda` and a locally checked claim ledger. It DOES NOT construct a verified full Smith hardware schematic or actual Maxwell-loaded antenna modes.

## Original source qualification
Donald Lee Smith is identified as inventor of [MXNL02000035A](https://patents.google.com/patent/MXNL02000035A/en), filed 2002-11-15 and published **2004-05-20**. Google Patents shows **Application Discontinuation** and abandonment/withdrawal, not an issued granted patent. Its abstract describes transforming electromagnetic energy using a potential generator and capacitor plates / coils. The precise "Don Smith commercial device" named by Filsinger is not identified by the patent abstract alone. The extra Don Smith 1996 suitcase and 2004 board designs mentioned in secondary compilations are distinct candidate implementations. A patent claim is not verified excess-power performance.

## Bidirectional seven-claim map (forward observables; reverse proof obligations)

| Owner/source claim | Strongest physically coherent steelman | Forward observable | What reverse identification requires |
| --- | --- | --- | --- |
| Smith: loaded dipole resonance produces useful electric energy | Driven electromagnetic dipole/transformer with resonant impedance and finite source-to-load transfer | Resonant coil/plate voltage and load power | Original complete Smith circuit, all input/output powers, field and loading losses |
| Filsinger: ZVS driver | Soft-switched resonant voltage conversion, possibly self-oscillating | Actual switching waveform and frequency-load map | Vds, drain current, switch timing and topology |
| Filsinger: 1/2/4 MΩ across capacitor branches | Bleeder/shunt changes voltage, input load, active oscillator pull, not simple RC=LC | Shunt V(t), P=V²/R, frequency-vs-voltage response | Exact terminals, resistor thermal/rating, simultaneous V and f |
| Filsinger: Earth potential supplies energy | Possible geoelectric, atmospheric displacement, RF return or soil galvanic port | Signed integrated Earth-port real work | Electrode metals, spacing, chemistry, drive and energy ledger |
| Filsinger: portable antenna common midpoint/opposite polarity | Two-port receiver with orthogonal modes and rectified opposed branches | Phase, vector rotation and delivered power | Maxwell PEC/finite-conductor boundary model, feed/counterpoise, actual spectral field, independent antenna efficiency |
| Filsinger: "cosmic radiation" | Must distinguish coherent RF, fair-weather ion current and ionising particles (different transducers) | Source-resolved energy deposition and conversion | Defined radiation species, flux, calibrated transducer and losses |
| Derived two-mode circular response | Split resonant modes from a **single coherent** incident wave may create quadrature | Lissajous signed polarisation and spatial field/curl | Same-object time harmonic Maxwell solution and current continuity |

## Existing Maxwell reuse / legal promotion boundary
- `DASHI.Promotion.MaxwellExteriorCalculusAdapter`: canonical symbolic `F=dA` and `dF=0`, but inhomogeneous current/Hodge/source closure explicitly pending. Reused as existing symbolic owner.
- `DASHI.Physics.Closure.MaxwellGaugeFieldEquationScope`: genuine physical source Maxwell equation obligations not automatically inhabited.
- `DASHI.Physics.QuantumVacuum.PerfectConductorMaxwellSpectrumBidiExact`: forward/reverse pattern for boundary modes. Its existing perfect parallel-plate spectrum is NOT an eigenmode proof for the user's proposed rectangular antenna.
- `DASHI.Physics.Motors.Circuit36927ComponentGraphExact`: actual canonical component/pin/wire owner.
- Source owner labels remain distinct. A source statement does not construct a physical circuit or solve Maxwell.

## Same-object non-identifiability
Two worlds have identical meter readings but different environmental-work classification, so the finite Agda theorem `meterDoesNotIdentifyEnvironmentalPower` rejects any universal inference from display to origin of energy. This says nothing about whether the actual Earth port generates positive real work. Reverse obligations require independently calibrated port energy integrations.

## Local Python validation
Locally executed `/mnt/data/filsinger_bidi/check_claims.py`: **12/12 tests passed**, and `/mnt/data/filsinger_bidi/claims.json` emits a machine-readable seven-claim ledger. Tests verify all source claims carry both forward predictions and reverse obligations, conditional shunt energy, finite environmental-source underdetermination, and source/experiment identity separation. These checks are not Agda kernel receipts, Maxwell field validation or real-world observations.

## Max cut remaining, sorted by physical consequence
P0: Source-backed actual Smith commercial device and original pin-level diagram versus *only* Mexican application; do not conflate these.
P0: Kernel-check the newly written BIDI Agda plus inherited Agda 2.9/Nix dependencies (not performed by GitHub connector).
P0: Original Filsinger reel evidence: meter terminal mapping, ZVS transistors/driver pinout, shunt endpoints and alternate Earth/portable branch netlists; preserve later reels as distinct operating occasions.
P1: Nonlinear source-driven ZVS load pulling and measured power ledger. Identify source of observed ±5 Hz around ~7.8kHz acoustics before calling it an electrical frequency.
P1: Full Maxwell boundary eigenmodes of an actual loaded golden rectangle and neighbouring aspect ratios; feed, finite conductivity, environment, mode completeness, usable output coupling and phase coherence.
P1: Explicit source-separated environmental power for soil/atmosphere/RF/ionizing particles, including null controls and uncertainties.
P2: Actual Schumann mode source-to-receiver transfer if independently measured; golden ratio is not itself a source, source power, or proof of phase quadrature.

The original speaker's 'cosmic radiation' phrasing must not silently be replaced with ionising cosmic rays or with ambient RF: both interpretations remain distinct alternatives.
