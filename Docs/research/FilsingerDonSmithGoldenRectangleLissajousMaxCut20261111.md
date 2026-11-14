# Don Smith lineage × loaded golden-rectangle modal maximum cut — 2026-11-11

## Primary-source lineage and non-promotion
The user-provided Filsinger transcript explicitly calls the earlier inspiration the **"Don Smith commercial device"**. Internet source research found a patent text attributed to **Donald Lee Smith**, *Transformer Generator Magnetic Resonance into Electric Energy* (2004; see https://www.energylight.cn/upload/images/import/Smith.pdf), describing a loaded dipole, capacitor plates and transformer, as well as two earth grounds. This is source lineage, NOT verified excess-power performance, commercial-device identity, nor proof of direct Filsinger copying. Distinguish source patent from Filsinger's described actual Earth-ground ZVS device and his proposed portable midpoint/antenna modification.

## Two distinct device graphs; no silent identity
- Actual claimed/narrated Earth configuration: 15V/ZVS driver, white capacitor hot -> Earth-negative, 1/2/4 MOhm shunts, three blue capacitors reported by user from frames, green HV rectifier candidates, toroidal components and unknown diode/bridge wiring; separate later occasion with ground electrodes, not necessarily same operating point.
- Portable hypothetical: remove selected earth nodes, create common midpoint, attach elevated golden-aspect antenna plate, split current into opposite capacitor polarity branches. This is a proposed **graph transformation with physical/source obligations**; replacing a low-impedance return with an antenna is not graph-isomorphic to the original source network. All other component IDs, power and metering relationship remain candidate/unverified.

## Local Python: Lissajous two-mode model
`/mnt/data/filsinger_lissajous_modal_test.py` executed **12/12 tests passed**. Its curve output `filsinger_lissajous_four_cases.png` and `filsinger_lissajous_results.json` are locally generated artifacts; not a device-specific numerical Maxwell simulation.

Use ideal, equally driven orthogonal modes with `H_j(f)=[1-(f/f_j)^2+i(f/(Q f_j))]^-1`, `J_x=Re(H_x exp(iωt))`, `J_y=Re(H_y exp(i(ωt+δ)))`. For a geometric golden rectangle with unmodified fundamental frequencies, `f_y/f_x=φ≈1.618`; if drive `f=f_x`, Q=50, then `|H_y/H_x|≈0.03235`, and the normalized signed current circularity is ≈0.06463. Hence golden geometry by itself does NOT support balanced orthogonal quadrature in this toy model.

To make the bare orthogonal fundamental resonances coincide with a fixed `f_x`, the y-mode frequency must decrease by factor φ, corresponding to increasing lumped effective `(LC)_y` by `φ²≈2.618` (only in the assumed independent lumped model). With equal-mode frequencies and a 90° feeding phase, the Lissajous is an ideal circle; with two *slightly detuned* resonances around the feed at `f0(1±1/(2Q))`, even a common-phase feed can produce nearly circular time-local current; with same-frequency/same-phase feed, it's a straight line. Real characteristic mode coupling, boundary conditions, radiation losses and material dispersion are separately required; antenna geometry 1:1.618 does not guarantee efficiency or vortex state.

## Spatial current versus Lissajous rotation
`/mnt/data/filsinger_spatial_loop_test.py` locally passed **6/6 tests** and saved `filsinger_spatial_circulation_example.png`. On the ellipse `x²/a²+y²/b²<=1` inscribed in an a:b=φ:1 rectangle, set `ψ=(1-x²/a²-y²/b²)²`, `J=(-∂ψ/∂y, ∂ψ/∂x)` (within ellipse). Then `∇·J=0`, `J·n=0` on boundary and `(∇×J)_z ≠0` inside; it is a mathematically admissible trapped closed-streamline **candidate field**. THIS IS NOT an electromagnetic eigenmode of the actual conductor, does not account for charge distribution, conductivity, driving fields, or demonstrate that an antenna supports stable loops or extracts power. Nonzero curl of J is not identical to Faraday curl of E.

## Engineering significance
A resonantly trapped circulation may increase local field storage / Q; it can also reduce coupling bandwidth or useful external extraction. A power harvester optimises transducer coupling **and** extraction/loss, not indefinite trapping alone. Matching internal to external damping (critical coupling under a simple one-port resonator model) is a meaningful next objective.

## Highest-value remaining maximum cut
1. Identify original Don Smith commercial-device document and exact diagram, if publicly available; do not assert this patent is the same device.
2. Measured Filsinger ZVS switching f(t) simultaneously with acoustic f(t), signed capacitor voltages, resistor values, source P(t), ground impedance and energy, for **each separate occasion**.
3. Real measured dimensions and feed/current geometry for golden rectangle; perform boundary-value/characteristic-mode Maxwell simulation with losses and port driving, and compare aspect ratio φ against nearby ratios.
4. Test true surface-current spatial circulation, radiation/collection efficiency and two-mode phases; distinguish rotating vector at a point from divergence-free closed spatial loops.
5. Measure external field and net environmental port P=∫v i dt; refuse cosmic/Schumann causal promotion absent sourced field and transfer function.
6. Agda kernel check of inherited #1482 and new adapters; local Python tests are NOT Agda proofs.

Attribution: the mathematics and synthetic models are our reconstruction, not a claim that Smith/Filsinger published these derivations.
