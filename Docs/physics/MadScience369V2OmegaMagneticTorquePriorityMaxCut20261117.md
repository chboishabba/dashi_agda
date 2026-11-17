# V2 Ω magnetic-torque priority maximum cut — 17 November 2026

## Motivation and scope

This deliberately reverses the earlier recovery-first priority. The primary
steelman is **load response of the full electromechanical conversion path**:
what changes in shaft torque, motor electrical input and winding/core losses
when pulsed currents are placed at different rotor positions? No original V2
flux map, machine topology, shaft torque, pulse trace, or winding data were
available for this constructed example. The only reported V2 datum reused is
2354 RPM as a numerical speed. The source does not claim a physical V2 gain.

## A × B: exact nonlinear magnetic-energy / torque / timing construction

Define dimensionless rotor angle `x = k θ`, and co-energy

`W'(x,i) = 1/2 [L₀+a cos(x)+b cos(2x)] i² − β i⁴/4`.

Then

`λ = ∂ᵢW' = L(x)i − βi³`,

`τ = ∂θW' = −(k/2)[a sin(x)+2b sin(2x)] i²`,

`U = iλ − W' = 1/2 L(x)i² − 3βi⁴/4`.

For `|i|≤Imax` and
`L₀−|a|−|b|−3β Imax²>0`, the differential inductance is strictly
positive; `i ↦ λ` is invertible throughout the admitted current range.

Use smooth, strictly positive angular-current profiles:

`i(x)² = J[1+u sin(x)+v sin(2x)]`, with `|u|+|v|≤r<1`.

This fixes mean RMS² `⟨i²⟩=J`, hence copper dissipation `R J`, for
all timing profiles at the same `J`. Fourier orthogonality yields the **exact**
mean generator shaft input:

`Pshaft = −⟨τ ω⟩ = (k ω J/4)(a u + 2 b v)`.

The winding identity is

`vi = R i² + dU/dt + τ ω`.

Over the complete periodic current/angle cycle, `ΔU=0`, so signed net
terminal export is `Pshaft − R J`. For fixed positive export efficiency `η`,
`Pbus = η(Pshaft−RJ)`. **Recovery η is fixed and never optimised**.

### Exact restricted optimum, not a hardware optimum

With only the L1 timing constraint `|u|+|v|≤r`,

`Pshaft ≤ (k ω J r/4) max(|a|,2|b|)`.

The bound is attained at the appropriate first/second harmonic extreme.
This is the dual-norm inequality for a 2-dimensional linear functional.
Finite voltage, temperature, torque ripple, and source hardware are NOT part
of that global statement. The program separately tests electrical envelopes.

### Voltage envelope, not a sampled-only claim

For `i = sqrt(Jg)`, `g=1+u sin(x)+v sin(2x)`, the code computes the exact
`di/dx`, `d²i/dx²`, `dλ/dx`, and a global upper bound `B` on `|dV/dx|`,
where `V=R i+kω(dλ/dx)`. For a uniform n-point angular grid,

`max_x |V(x)| ≤ max_j |V(x_j)| + Bπ/n`.

This certifies continuous **winding** voltage between grid points; it is not
an inverter-switch peak, cable-transient, or real-world isolation rating.
The separate current ceiling is checked. Coefficients are hypothetical.

## E × F: same electrical load, different shaft reaction

Synthetic model defaults: `L₀=.040 H`, `a=.012 H`, `b=.008 H`,
`β=.0001 H/A²`, `R=1 Ω`, `k=4`, `2354 RPM`, `η=.95`,
`target bus=20 W`, admissible peak current 8 A, 320 V winding threshold.
Motor load-dependent loss is separately illustrative: `Dm=12+100 τ²` W.

| Timing profile | Shaft input W | Copper W | Motor electrical increment W |
|---|---:|---:|---:|
| First harmonic, (u,v)=(0.6,0) | 48.22 | 27.17 | 52.05 |
| Second harmonic, (0,0.6) | 36.46 | 15.41 | 38.65 |
| Mixed, (0.3,0.45) | 33.72 | 12.66 | 35.59 |
| Second harmonic extreme, (0,0.75) | 31.80 | 10.75 | 33.47 |

Every listed operating point exports the **same net 20 W** and pays the
same fixed export fraction (0.95). Thus the change in required shaft work
is **exactly** the change in copper heat, not a disappearance of Lenz reaction:

`Pshaft,1−Pshaft,2 = R(J₁−J₂)`.

The first vs mixed profiles save **14.50 W of shaft input** while delivering
the same 20 W electric output. Motor input also falls in the assumed
motor-loss law, but **does not remain constant** across loading, and no source
physical motor map is claimed. The numerical figures are construction-specific,
not universal electromagnetic design benchmarks.

At fixed RMS/current rather than fixed bus output, current placement changes
shaft input and exported output together; they must never be mixed with the
matched-output comparison. This distinction is enforced in tests.

## Negative controls / non-identification

- Setting `a=b=0` removes mean electromagnetic shaft conversion even if
  current is modulated.
- Reversing the timing harmonic reverses the sign of mean torque. Incorrect
  timing can **drive the motor rather than generate**.
- Saturation changes flux and winding voltage but does not create torque from
  an angle-independent term; positivity of the differential inductance is
  checked before admission.
- With identical, translated, uncoupled phases sharing a fixed total RMS²,
  ideal mean torque and copper are invariant for phase counts 3, 4, 6, 7, 9, 11.
  Additional controller overhead is an *assumed* cost per phase; no 3/6/9
  preference is inferred.
- The source's 286 W loaded/unloaded display is not explained: the synthetic
  motor electrical increment is positive on loading and independent original
  motor input measurements do not exist.

## Roadmap and strict admission

1. **A — source-selected magnetics** OPEN: V2 reluctance/permeance and
   calibrated winding flux-linkage/torque maps, leakage, hysteresis and mutual
   phase coupling. The constructed algebra above is closed only for its
   polynomial family.
2. **B — timing with actual hardware** OPEN: waveform tracking, PWM switching,
   current/voltage transients, torque ripple and temperature margins.
3. **E × F — measured shaft backaction** OPEN: loaded/unloaded torque, motor
   efficiency and independently tracked energy stores in the original V2.
4. **G — robust physical geometry/Pareto** OPEN: source-derived material,
   copper, thermal, mechanical and controller constraints. The 2-dimensional
   L1 optimum is NOT this optimum.
5. **C × D — recovery** secondary control: hold fixed during magnetic test;
   measure it separately only once shaft/timing coupling is identified.
6. **H × Ω — original proof** OPEN: source schematic, synchronized true port
   powers, both stored-energy endpoints, randomized load interventions,
   bounded measurement error, and pinned Agda/CI verification.

The previously documented **16 original strict P0–P4 gates remain OPEN**.
All mathematical results here are conditional on the invented co-energy
and motor-loss models. Python tests are regression evidence, not Agda
kernel proofs or empirical verification.
