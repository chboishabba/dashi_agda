# TODO

## Masked Orthogonal Split (empirical gate: PASS)
Layer: 3D closure embedding (`v_pnorm, v_dnorm, v_arrow`).
Quadratic: `G = diag([-1, 0.2034, -1])` (mask-based).
Projector: `P = G-orthogonal projector onto shape coords [0,1]` (`arrow=coord 2`).
Results (n=156 steps, dim=3):

- `||PᵀG − GP||_F = 0.0`
- `max |⟨PΔs, (I−P)Δs⟩_G| = 2.396e−16`
- `max |Q(Δs) − Q(PΔs) − Q((I−P)Δs)| = 6.661e−16`

Interpretation: Case A achieved in cone layer — exact G-self-adjoint projection, vanishing cross-term, Pythagorean quadratic split holds to machine precision.
