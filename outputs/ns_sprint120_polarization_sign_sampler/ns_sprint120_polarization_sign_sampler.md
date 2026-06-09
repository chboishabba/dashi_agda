# ns_sprint120_polarization_sign_sampler

Deterministic sampler for the corrected linear strain sign algebra.

Formula surface:

- k = (cos theta, sin theta)
- n = (-sin theta, cos theta)
- e = diag(-C, +C)
- q = n.e.n
- flux_proxy = q
- amplification_proxy = -q
- flux_proxy * amplification_proxy = -q^2 <= 0

Summary:

- anticorrelation_all_rows: true
- positive_flux_rows_have_negative_amplification: true
- constant_linear_strain_route_obstructed: true
- clay: false

| theta | q = n.e.n | flux proxy | amplification proxy | product | product <= 0 |
| --- | --- | --- | --- | --- | --- |
| 0 | 1 | 1 | -1 | -1 | true |
| pi/8 | 0.707106781187 | 0.707106781187 | -0.707106781187 | -0.5 | true |
| pi/4 | 0 | 0 | 0 | 0 | true |
| 3pi/8 | -0.707106781187 | -0.707106781187 | 0.707106781187 | -0.5 | true |
| pi/2 | -1 | -1 | 1 | -1 | true |
| 5pi/8 | -0.707106781187 | -0.707106781187 | 0.707106781187 | -0.5 | true |
| 3pi/4 | 0 | 0 | 0 | 0 | true |
| 7pi/8 | 0.707106781187 | 0.707106781187 | -0.707106781187 | -0.5 | true |
| pi | 1 | 1 | -1 | -1 | true |
