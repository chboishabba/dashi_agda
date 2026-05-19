# MDL Lorentz Closure Template

Use this as the fast scoring sheet for the closure milestone.

## Score Rule

`L = L_data + L_model`

- `L_data`: residual or misfit score on the same dataset.
- `L_model`: parameter count plus explicit penalties for frame-picking or anisotropic repair terms.

## Table

| Model | Principal Symbol | Forcing Class | Preferred Frame? | Free Params | Symmetry-Break Penalty | Residual / Misfit | Total Heuristic MDL |
| --- | --- | --- | --- | --- | --- | --- | --- |
| A | Lorentzian | unconstrained quadratic | no |  | 0 |  |  |
| B | Euclidean surrogate | unconstrained quadratic | yes |  |  |  |  |
| C | Lorentzian | energy-subcritical quadratic | no |  | 0 |  |  |

## Interpretation

- If A and B fit similarly, B should lose unless the extra preferred-frame terms pay for themselves in lower residual.
- If C matches A on fit while shrinking the admissible forcing class, C is the cleanest closure candidate.
- Treat any nonzero preferred-frame or anisotropy correction as a real code-length penalty, not free notation.
