# KSW668 F8 maximum cut VI — exact original moving Neumann forced wall flux, radial FV energy, and the remaining true stability weld

**Date:** 2026-11-15. **Owner:** PR #1512, original flat-FRW \(a(t)=t\) five-dimensional Poincaré AdS5 moving brane. **Source law:** the physical linear TT Israel unit-normal condition \(n\cdot\partial H=-6\pi^{TT}\) is represented in wall-fitted characteristic coordinates \(q_\pm=H_T\pm H_z\) by \((1+v)q_++(v-1)q_-=2G\), with \(G=-6\pi^{TT}\sqrt{1-v^2}/b\). This is NOT a Robin boundary or stationary RS2 wave equation.

## Exact wall energy input, not an assumed approximate contraction

On the original \(1\le t\le2\) strip, wall velocity
\[
v=b'(T)=-1/\sqrt{1+t^2}<0,\qquad
\beta=(1+v)/(1-v)\in(0,1).
\]
The actual incoming characteristic is \(q_-=\beta q_+-2G/(1-v)\). Define the normalized positive characteristic energy flux INTO the physical \(y\ge0\) domain,
\[
\mathcal F_{\rm char}:=(1-v)|q_-|^2-(1+v)|q_+|^2.
\]
For any real tensor component, expand this expression and complete the square **exactly**:
\[
\boxed{\mathcal F_{\rm char}
=2v\beta\,|q_+-G/v|^2-\frac{2}{v}|G|^2.}
\]
The coefficient \(2v\beta<0\), so the square term is nonpositive. Since \(-2/v=2\sqrt{1+t^2}\le2\sqrt5\),
\[
\boxed{\mathcal F_{\rm char}(T,\mathbf x)\le 2\sqrt5\,|G(T,\mathbf x)|^2}
\quad\text{for all original }1\le t\le2.
\]
Sum over independent real TT components to obtain the vector/tensor version. Multiply by the appropriate positive \(b^{-3}\) and normalization factor when incorporating into the full AdS5 bulk stress-energy balance; this module proves the **characteristic flux algebra**, not that full coupled moving-metric energy balance.

At \(t=4/3\), exact original rational data \(v=-3/5,\beta=1/4\) yield
\[
\boxed{\mathcal F_{\rm char}=
-\frac3{10}\left(q_++\frac53G\right)^2+\frac{10}3G^2.}
\]
For the previously fixed rational sample \(q_+=1/8,G=1/12,q_-=-7/96\), one has \(\mathcal F_{\rm char}=13/5760\). The source-only Agda \`KSW668AdS5MovingNeumannFluxRationalExact.agda\` imports the original moving characteristic owner and states/proves this exact constant rational identity; the full real-square-root and numerical/continuum PDE theorem are not kernel-accepted. The source-equivalent SymPy + numerical producer \`scripts/ksw668_f8_moving_neumann_flux_square.py\` derives the general algebra and checks nonzero forcing, zero-force dissipativity, source-vector norms and the sharp vertex \(q_+=G/v\) with 12 negative/positive controls.

## Why this is a genuine mathematical improvement

This removes a previously independent ambiguity: the retarded sourced Neumann boundary **cannot inject an uncontrolled positive characteristic energy flux** without the prescribed \(L^2\)-size of its actual TT boundary source \(G\). The bound does **not** require a high-positive-Laplace frozen-wall resolvent, a geometric Neumann-series contraction or a stationary outgoing contour.

Combining it with the newly proved radial shell finite-volume Green identity
\[
\sum_jV_j U_j L_{d,h} U_j
=-\sum_j(A_{j+1/2}/\Delta r)(U_{j+1}-U_j)^2\le0
\]
for effective \(d=3,7,11\) supplies two **separately exact** positive-energy structural ingredients for the next full time-dependent semidiscrete stability theorem.

**The hard remaining proof is NOT automatic:** the mixed \(T,y,r\) wave system includes moving \(b(T)\), variable \(v(T)\), radial stress cross terms, bulk radial horizon/outer boundary and discrete/SSPRK3 coupling. A complete discrete energy inequality would need precisely the boundary contribution of the symmetrizer together with the face cancellations and a timestep restriction for all modes, plus consistency/error estimates. A positive boundary/source energy estimate alone does not establish nonzero curvature at a selected receiver or bounded curvature-trace error; two Weyl derivatives magnify unresolved wavefront errors.

## Exact remaining acceptance ledger after this cut

| Gate | Status and exact next deliverable |
|---|---|
| \`ads5OriginalMovingNeumannTTForcedWallFluxCompletedSquareExact\` | **MATH CLOSED**, uniform original \(2\sqrt5\) bound, componentwise; rational Agda source only, pinned kernel OPEN |
| \`ads5OriginalTTThreeMultipoleExactShellVolumeRadialFV\` | **MATH CLOSED**, correct finite-volume polynomial and negative Green identity; Agda first-cell rational source only |
| \`ads5OriginalTTCompactSourceL0L2MomentCancellation\` / \`ads5OriginalTTCompactSourceL4PositiveMomentExact\` | **MATH CLOSED**, global source-cell runtime guard; full source-to-observer UV/IR transfer OPEN |
| \`ads5OriginalMovingTTManufacturedPolynomialInteriorIsrael\` | **SEMIDISCRETE MATHEMATICAL/NUMERICAL CONTRACT PASS**, exact actual moving bulk/wall operator on interior |
| \`ads5OriginalTTSourceCellFluxConservationFullDiscreteEnergy\` | **PARTIAL**, combine the new wall completed square and radial Green identity with moving normal \(y\), SSPRK3 CFL and outer boundary |
| \`ads5OriginalMovingTTThreeMultipoleThreeObservableConvergence\` | **OPEN**, 3-grid early field drift 21.8%, intrinsic Weyl 90.3%, projected Weyl 82.7%, plus beyond-bulk-front leakage |
| \`ads5OriginalMovingWeylSobolevBoundaryTraceAndError\` | **OPEN**, actual retarded tensor-to-both-Weyl boundary trace, finite-band spatial/temporal derivative error |
| \`ads5OriginalT2NeumannToWeylEllipticFIOComposition\` / \`ads5OriginalT2ActualCompactTTNonzeroEarlyBothWeyl\` | External-paper FIO theorem-application **candidate, independently reviewed continuum acceptance OPEN** |
| F9 brane matter generating action, all-mode stability/backreaction and separate cylinder | **OPEN** |
| F10 physical scales/attenuation/calibrated clock and detector | **OPEN** |
| F11 pinned Agda 2.9 differential and analytic kernel + semantic weld | **OPEN** |
| D1 independent physical graviton early-arrival observation | **OPEN** |

**Verification:** 12 new exact wall-energy tests PASS, added to the 172 prior committed test cases = **184 committed-source-equivalent F8 cases**. A broader 197-case local superset, which additionally includes 13 exploratory uncommitted prepotential tests, passed. The current full compact 3D numerical acceptance remains fail-closed. Exact connected GitHub head, pinned Agda kernel, physically generated matter source, and D1 observation are independently unverified.
