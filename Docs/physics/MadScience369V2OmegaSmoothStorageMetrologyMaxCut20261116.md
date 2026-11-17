# Ω tenth max-cut — finite-voltage winding, closed DC bus and source-identifiability

Status: **restricted mathematical/model certificate**, not original @madscience369 V2 hardware evidence. Date 16 November 2026. Original ~2354 RPM and narrated 285–287 W motor input/~45 W generator load are uncalibrated reel observations. All other parameters here are synthetic. Preserve separate Don Smith/Filsinger/Resonate369 source attribution.

## Model and continuous bounds

Let x=kθ, ω=2π RPM/60 and i(x)=I·max(sin(x+δ)−q,0)². Use reversible saturating coenergy W′=L₀i²/2+A Is² cos(x) logcosh(i/Is). Flux λ=∂ᵢW′, torque τ=k∂ₓW′, required voltage v=Ri+(∂ᵢλ)·di/dt+(∂ₓλ)·kω. This waveform is C¹ and exactly periodic. The physical signed cycle identity is ⟨vi⟩=P_Cu−P_shaft, where P_shaft=⟨−τω⟩.

A derivative majorant M for |dv/dx| yields sup |v|≤max_grid|v|+Mπ/n. Similar bounds hold for peak current and slew. The modeled four-quadrant converter is η_rev⟨(−vi)_+⟩−η_fwd⁻¹⟨(vi)_+⟩ minus declared losses; it is not a transistor-level device. A 0.01 F DC bus capacitor receives signed converter work and supplies the exact full-period mean to a hypothetical constant-power load. Analytic periodicity plus explicit numerical quadrature and intersample error bounds close and enclose its energy at the modeled level. Thermal stationarity and tracking stability remain open.

With an invented 45 W mechanical shaft input and 2354 RPM, ordinary η_rev=.95 gives 20.670 W synthetic bus output; enhanced η_rev=.99 and +0.4 W controller overhead gives 28.014 W. The two arms use **identical current and terminal voltage**, so the gain is ΔP=0.04⟨(−vi)_+⟩−0.4, with a Lipschitz numerical integration bound [7.136,7.552] W. Continuous sampled-plus-derivative terminal voltage upper ≈319.624 V versus 320 V limit. This is neither the original V2 nor a global physical optimum; do not combine wattages with earlier ideal rectangular or averaged-PWM models.

## Source-identifiability and flywheel exclusion

The loaded minus unloaded complete boundary gives ΔP_load−ΔP_motor=ΔP_aux−ΔP_loss−ΔE_dot−ΔP_other. For unknown [aux,loss,storage,other], the observation matrix [1,−1,−1,−1] has rank one and nullity three; two display readouts cannot identify the mechanism. Conditional on equal auxiliaries/other outputs/stationary stores and motor-input change ±2 W, the loss reduction required for 45 W added output is [43,47] W. Without those conditions even the sign is unidentifiable.

If rotor kinetic energy alone covers ΔP for time T and angular speed drops ≤ε, energy E_rot=Jω²/2 requires J≥2ΔPT/[ω²(1−(1−ε)²)]. For 45 W at 2354 RPM, ε=.01, J≥0.074425 kg m² for one second or ≥0.744251 kg m² for ten seconds. These are conditional lower bounds, not observations of V2 inertia.

## Acceptance

Local reconstructed-source runner: 135/135 Python tests (104 pre-existing A–H plus 31 new), no Agda compiler or connected GitHub CI execution. Seven-file full source/proof/numerical bundle available from this ChatGPT conversation. The strict original 16 P0–P4 gates remain OPEN. Finite switching waveforms, actual LC coupling, temperature/material calibration, all shaft/power ports, original topology, and randomised load intervention are outstanding. Do not interpret the constructed source as evidence of anomalous energy or as a V2 teardown.
