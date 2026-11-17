# V2 A×B×E×F — coupled magnetic torque maximum cut (17 Nov 2026)

**Scope:** reversible, constructed two-winding machine; not identified as the original @madscience369 V2. This round holds converter export at 95%, and does not optimize recovery. See the runnable producer and tests for the full assumptions and numerical receipts.

## Coenergy and shaft-work identity

For rotor phase x=kθ, let i(x)=c+u sin(x)+v cos(x), L(x)=L0+A cos(x)+B sin(x), with symmetric matrices. The magnetic coenergy is W' = iᵀL(x)i/2 − β Σ iⱼ⁴/4. Flux λ=L(x)i−βi³; electromagnetic torque τ=k iᵀL'(x)i/2. The exact full-cycle ledger is:

- Shaft input: Pshaft = kω cᵀ(Au−Bv)/2
- Copper loss: Pcopper = Σ Rⱼ[cⱼ²+(uⱼ²+vⱼ²)/2]
- Winding electrical terminal input: Pterminal = Pcopper−Pshaft

At fixed AC copper budget Q=Σ Rⱼ(uⱼ²+vⱼ²)/2, Cauchy–Schwarz gives the **global optimum within the sinusoidal coefficient ellipse**: Pshaft ≤ kω sqrt(2QS)/2, S=(Ac)ᵀR⁻¹Ac+(Bc)ᵀR⁻¹Bc. Equality uses u∝R⁻¹Ac and v∝−R⁻¹Bc. The theorem is *not* global optimality for arbitrary physical waveforms, material hysteresis or a transistor-level converter.

## Two distinct matched 20 W-export comparisons

| Constructed magnetic geometry | Required shaft W | Copper W | Export W |
|---|---:|---:|---:|
| Cooperative mutual coupling | 25.560 | 4.508 | 20 |
| Uncoupled harmonics | 26.277 | 5.224 | 20 |
| Opposing mutual coupling | 28.623 | 7.571 | 20 |

This 0.717 W improvement is a **different-geometry counterfactual**, not a switching/timing-only result. The opposing mutual case is a negative control.

A cleaner **same-geometry current-coordination** comparison gives 25.560 versus 25.591 W shaft input, a **0.0307 W** benefit. The latter isolates control timing for these coefficients; it is small. At equal electrical output and unchanged converter boundary, every modeled shaft saving is paid by lower copper loss. No anomalous energy or source-qualified V2 performance is claimed.

## Tests and gate ledger

19/19 dedicated local tests passed. They check exact versus integrated torque, electrical ledger, first-harmonic optimum, current/voltage sufficient bounds, zero rotor-angle coupling, phase reversal, adverse mutual geometry, matched-output controls, and saturated flux not creating free shaft work.

**A×B**: first-harmonic two-winding coefficient optimum closed at its restricted scope. Physical B-H/mutual flux, hysteretic material, cross-core losses, current/voltage/time constraints and full winding graph OPEN.

**A×E×F**: load, torque and copper-energy relationship closed in this reversible two-winding construction. Actual drivetrain backaction, motor efficiency map, core losses and synchronized loaded/unloaded operation OPEN.

**G**: continuous constrained hardware optimality OPEN.

**H/Ω**: source-specific winding geometry, magnetic map, real torque, all electrical ports and both storage endpoints missing. All original 16 strong P0–P4 gates OPEN. Agda kernel and connected-head CI NOT RUN.

The generator/electrical boundary is fixed, not tuned for recovery. This programme prioritizes magnetic transduction and reaction torque.
