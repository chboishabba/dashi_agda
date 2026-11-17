# Smith/Filsinger F13/D1 — Agda two-variable Cayley midpoint max-cut (17 Nov 2026)

PR #1524 continues the existing original solver/proof owners, not another Green theory.

## Formal implementation
New `DASHI/Physics/Motors/SmithFilsingerLocalCayleyMidpointExact.agda` imports the original `CertifiedCayley`, `sameCayleyFirst`, `sameCayleySecond` from `SmithFilsingerLocalCayleyZeroWeldExact` and the existing rational ring solver. `CertifiedHalfStep` certifies `p+p=h*a`, `r+r=h*b`, and `p*r=quarter*h²ab`, while the same original Cayley record certifies `q*(1-quarter*h²ab)=1` (its inverse law is stated in the other multiplication order).

The normalized exact outputs are `u=q*((1+p*r)*x+(p+p)*y)`, `v=q*((r+r)*x+(1+p*r)*y)`. `sameFirstIsReduced` and `sameSecondIsReduced` rewrite these into the original unchanged output functions. `halfStepInverseLaw` uses the *existing* inverse certificate, and the ring solver authors the two polynomial factorizations
- `u-p*v=((1-p*r)*q)*(x+p*y)`
- `v-r*u=((1-p*r)*q)*(y+r*x)`.

The new source-level theorems `sameCayleyFirstMidpoint` and `sameCayleySecondMidpoint` consequently state both complete implicit midpoint equations for the same original source-owned update: `u-p*v=x+p*y`, `v-r*u=y+r*x`. It does not stipulate either equation as a premise. The prior Agda module had used `refl` without importing it; that import is corrected.

## Independent mathematical acceptance
New `scripts/test_smith_filsinger_cayley_midpoint_sympy.py` adds **10 exact cases** against the *existing* heterogeneous Maxwell/Lorentz `cayley_edge_step` and `edge_updates`: sizes n=1 through 5, signed rational matrices, both midpoint equations, half-step consistency, and singular-denominator refusal.

**164/164 tests PASS locally** (prior 154 + 10 new) with the full ten-file source-equivalent exact SymPy suite. New source is listed in both pinned Agda 2.9 checker target lists. New Agda proof names and test file are in the standalone fail-closed SymPy gate; tests are also in the consolidated Python runner.

## Remaining strict gates
**D1 actual Agda kernel OPEN**: no `agda` or `nix` installed here; no completed pinned 2.9 acceptance result observed on this PR head. Source authored and independent exact arithmetic pass do not certify coverage/termination/elaboration/imports. Run the pinned checker and repair any first compiler failure.

**F13 physical OPEN**: exact rational two-coordinate midpoint and graph reachability are not a calibrated 3D Maxwell retarded dyadic/light-cone theorem with real soil/air/ionosphere interfaces and original terminal/return current.

**F15 real original work OPEN**: no independently measured replenished source, same-original receiver/controller/material and all-state-restored work receipt.

Next max-cut: Agda kernel acceptance; then typed attachment of a real certified half-step to each heterogeneous cell/face edge and the original open-boundary Poynting owner. No edits to ESD; original Smith/Filsinger attribution preserved.
