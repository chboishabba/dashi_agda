# GR Vladimirov Frame Diagnostic

Status: suspended gravity frontier diagnostic, non-promoting.

Source of record:

```text
DASHI/Physics/Closure/GravityVladimirovFrameReceipt.agda
DASHI/Physics/Closure/GRVladimirovFrameDiagnosticReceipt.agda
scripts/gr_vladimirov_frame_diagnostic.py
scripts/data/outputs/gr_vladimirov_frame_diagnostic.{json,csv}
```

## Correct Status

The gravity lane is earlier than the Clay lanes.  Its trit status is:

| Layer | Result | Trit |
|---|---|---|
| Vladimirov `D^alpha` spectrum in `L2(Q_p)` | Known: Kozyrev wavelets are eigenfunctions with eigenvalues `p^{-alpha j}`. | `+1` |
| Archimedean image of `D^alpha` eigenfunctions | Binding: `D^alpha` weights cancel in normalized nesting, but the `L2(R^3)` gravity image has `p^(3d)` depth density and requires the stricter `sigma < 0.3025113508228815` taper. | `0` |
| Schwarzschild metric match | Blocked by radial valuation and W4 physical mass/stress-energy calibration. | `-1` |

So the lane trit is `0` suspended.  The finite script rows are diagnostics, not
a carrier-derived gravity prediction.

## Diagnostic Result

The current finite diagnostic records:

```text
Vladimirov D^alpha has Kozyrev eigenfunctions.
For 3D macroscopic gravity after the audit:
  atom density per depth: p^(3d), not p^d
  normalised nesting constants at p=3: 1D=0.5773502691896257, 3D=0.19245008972987526
  binding prime: p=3
  sigma_crit_3D(p=3): ~=0.3025113508228815
  sigma_digit: ~=0.2886751345948129
  3D PAWOTG series at sigma_digit: ~=0.7228939450291813
  sigma headroom: ~=0.0138
For the earlier 1D Gate3 condition:
  sigma_crit_1D(p=3): ~=0.505
  1D PAWOTG series at sigma_digit: ~=0.0803
Earlier finite diagnostic:
  p-adic Kozyrev Gram: A=1, B=1, mu=0
  Archimedean digit Haar/Kozyrev contrast Gram: A~=1, B~=1, mu~=0
  naive radial shell image: A~=0.284, B~=2.743, mu~=1/sqrt(3)
```

This separates the useful p-adic operator from the bad radial valuation:

- Kozyrev/Haar contrast modes are orthogonal in `L2(Q_p)`.
- Finite digit-image contrasts are diagnostic only, not the actual
  Archimedean gravity frame theorem.
- Naive radial shell indicators nest and are not a legal radial valuation.
- Vladimirov eigenvalue weighting does not improve the normalized frame
  constant.
- The 3D gravity frame condition is stronger than the 1D Gate3 condition.
- The digit-expansion baseline still passes, with narrow but real headroom
  of about `0.0138` in sigma.

## Meaning

This is the gravity analogue of the Gate3 nesting/taper clarification, but the
3D geometry reverses the earlier ordering. If the physical SSP embedding
satisfies the gravity condition `sigma < 0.3025113508228815`, then the 1D Gate3
`sigma < 0.505` condition follows with headroom. Gravity is therefore the
binding Archimedean taper target, not a Gate3 corollary. W4 mass calibration
and Ricci convergence come after that.

## Still Blocked

This diagnostic does not derive a physical gravity prediction.  These blockers
remain:

- W4 mass/stress-energy calibration.
- Carrier radial valuation.
- Weak-field Newtonian potential.
- Schwarzschild metric match.
- Discrete-to-smooth Ricci/Einstein convergence.
- Carrier-derived higher-curvature coefficients.

The weak-field numbers in `GRWeakFieldPredictionReceipt` remain external GR
baselines.  `gravityPredictionPromoted = false`.
