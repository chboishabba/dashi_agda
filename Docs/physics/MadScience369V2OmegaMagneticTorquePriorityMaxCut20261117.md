# V2 Ω — Magnetic torque first, recovery held fixed (17 November 2026)

## Steelman under test
Can nonlinear magnetic geometry and angular current placement **reduce generator shaft reaction for the same net useful electrical output**, without hiding the cost in losses or stored energy? This is an A×B×E×F experiment. It is **not** an original V2 measurement, and it does not infer the schematic or magnetic material from the reel. Only reported 2354 RPM is used as a scenario speed.

## Constructed nonlinear magnetic theorem
For dimensionless rotor angle x=kθ, define co-energy
W'(x,i)=1/2 (L0+a cos x+b cos 2x)i²−βi⁴/4.
Flux λ=(L0+a cos x+b cos 2x)i−βi³; field torque τ=−k(a sin x+2b sin 2x)i²/2; stored energy U=iλ−W'.
Admit only |i|≤Imax with L0−|a|−|b|−3β Imax²>0 (positive differential inductance).
Let i(x)²=J(1+u sin x+v sin 2x) with |u|+|v|≤r<1.

Mean RMS² is exactly J and copper loss is RJ. Fourier orthogonality (independently checked by SymPy) gives exact generator shaft work rate:
**Pshaft=−⟨τω⟩=(kωJ/4)(au+2bv).**

The lossless magnetic-energy bookkeeping is **vi=Ri²+dU/dt+τω**. A complete periodic cycle has ΔU=0, giving ideal terminal export Pshaft−RJ. For a fixed export fraction η, Pbus=η(Pshaft−RJ).

A separate exact restricted optimum is Pshaft≤(kωJr/4)max(|a|,2|b|), attained by selecting the stronger admissible harmonic. This is only a modulation-domain optimum. Finite voltage, actual material geometry, thermal response, PWM tracking, hysteresis, mutual coupling and global physical optimality remain OPEN.

## Matched-load comparison: 20 W bus, η=95% fixed
Illustrative values: L0=.040 H, a=.012 H, b=.008 H, β=.0001 H/A², R=1Ω, k=4, 2354 RPM, Imax=8 A, winding Vmax=320 V.

| Angular current profile (u,v) | Shaft input (W) | Copper heat (W) |
|---|---:|---:|
| First harmonic (.6,0) | 48.22 | 27.17 |
| Second harmonic (0,.6) | 36.46 | 15.41 |
| Cooperative (.3,.45) | 33.72 | 12.66 |
| Second-harmonic extreme (0,.75) | 31.80 | 10.75 |

All rows deliver **the same 20 W net electrical output** with the same export efficiency; shaft-input difference is **exactly** the copper-heat difference. The cooperative profile saves 14.50 W shaft and copper relative to first-harmonic placement, not 14.50 W of energy created. An illustrative motor loss map still requires increased motor electrical input under loading, so this result **does not** explain the original approximately unchanged motor display.

## Mathematical voltage scope
For smooth i=sqrt(Jg), g=1+u sin x+v sin 2x, the local acceptance code analytically differentiates i and λ and bounds |dV/dx| globally by B, with V=Ri+kω dλ/dx. On a uniform n-point phase grid, the **continuous-winding** upper bound is max_j |V(x_j)|+Bπ/n, not merely the sampled maximum. All listed matched-load profiles satisfy the constructed 320 V winding threshold under that bound. PWM switching spikes and a complete converter are not thereby certified.

Negative controls: reversing timing reverses mean torque; a=b=0 eliminates mean shaft conversion; excessive negative differential inductance is rejected; angle-independent saturation cannot invent torque; 3/4/6/7/9/11 ideal translated phase models are neutral in aggregate RMS and mean torque, absent explicitly modeled per-phase overhead.

## Acceptance and next cut
Standalone new magnetic producer: **28/28 Python tests PASS locally**. Combined with available original load-intervention / dual-storage / drift regressions: **136/136 PASS locally**. An independent SymPy Fourier integration passes. The standalone source, tests, acceptance runner and JSON receipts are provided in the companion six-file ZIP, **not committed here as executable code**; this GitHub file and the canonical roadmap record only the result. No connected-head CI or Agda kernel acceptance is claimed.

Priority now A×B (source-selected flux/torque and multiwinding geometry) → E×F (loaded/unloaded shaft backaction and copper/core/thermal losses) → G (hardware-bounded robust pulse geometry) → H×Ω (real V2 synchronized port and storage metrology). C×D recovery remains an independent *fixed* control until source evidence says it matters. **All 16 original strict P0–P4 physical/formal gates remain OPEN.**

