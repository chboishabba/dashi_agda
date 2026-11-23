# YM P0 — original SU(2) Wilson to nonconstant discrete wave seam (23 November 2026)

## Exact evidence and source attribution

Reused original owners: DASHI/Physics/YangMills/YMClaySUNVariablePeriodicGibbsGaugeExact.agda (periodic SU(N) Wilson six-plane action), YMClayNativeSideFourTwoLinkPairSameObjectExact.agda (physical blocked pairs), YMClaySUNOriginal64Pair896MarkedEffectiveSourceExact.agda (full F19 source), YMClayOriginalWilsonTwoPlaquetteMarkedSourceExact.agda (original two global marks), BalabanPeriodicDifferenceSymbols.agda (difference/curl/Fourier interface), and finite wave/symbolic donors WaveAlgorithmLift, ShiftDiscreteWaveStep, ShiftWaveRefinementSeam, ShiftWaveScalingInterface, Base369WaveContinuousSymbolicCodingExact.

The new local **SymPy 1.14.0 executable** is [check_ym_sun_nonconstant_linear_wave_20261123.py](../../scripts/check_ym_sun_nonconstant_linear_wave_20261123.py). It independently reconstructs original periodic **site/positive-link/six-positive-plane** orientation and performs exact symbolic checks. The non-Abelian Q8 group is an SU(2) subgroup **for finite word regression only**; it is not the physical continuous Haar integration.

## A. Nonconstant SU(2) Cartan Wilson Hessian

Choose the SU(2) Cartan one-parameter link field

\[
U_\mu(x;\epsilon)=\exp(i\epsilon A_\mu(x)\sigma_3).
\]

For its original oriented plaquette, \(P_{\mu\nu}=\exp(i\epsilon F_{\mu\nu}\sigma_3)\), with \(F_{\mu\nu}=\Delta_\mu A_\nu-\Delta_\nu A_\mu\). Hence the original normalized Wilson trace deficit is \(J_{\mu\nu}=1-\frac12\operatorname{ReTr}P=1-\cos(\epsilon F_{\mu\nu})\) and \(J''_{\mu\nu}(0)=F_{\mu\nu}^2\). This derives the six-curl quadratic Hessian in the **commuting Cartan small-field chart**, not a full non-Abelian gauge-fixed one-loop Hessian.

For Fourier \(d_\mu(p)=e^{ip_\mu}-1\), \(H(p)=\sum_\alpha |d_\alpha|^2 I-d(p)d(p)^\dagger\). At \(p=(0,2\pi/L,0,0)\),

\[
H(p)=\operatorname{diag}(\lambda_L,0,\lambda_L,\lambda_L),
\qquad \lambda_L=4\sin^2(\pi/L).
\]

The exact eigenvalues at L=4,8,16 are 2, \(2-\sqrt2\), \(2-\sqrt{2+\sqrt2}\). The longitudinal \(d(p)\) is the zero gauge direction and three transverse directions are strictly positive at this nonzero momentum. At unit physical volume with lattice spacing a=1/L, the selected scaled symbol \(4L^2\sin^2(\pi/L)\) has checked values 32, 37.4903320081, 38.9736793542, 39.3517457342 for L=4,8,16,32, approaching \(4\pi^2\). This is a selected periodic free-mode calculation, **not** a uniform interacting or infinite-volume spectral estimate.

## B. An inhabited nonconstant exact discrete travelling-wave fixture

For \(A_2(x,\tau)=\cos[2\pi(x_1-\tau)/L]\), the exact second difference in integer time equals the second difference in the x1 direction for all sampled sites/times. SymPy proves the zero residual exactly, at all L squared samples for each L=4,8,16. The linearized curvature \(F_{12}=\Delta_1 A_2\) is nonconstant and invariant under \(A\mapsto A+\Delta\phi\), since the forward differences commute. Unlike ConstantZeroModeContinuumTheorem, the mode is not stationary or constant.

No claim: this particular massless **linearized** wave update is NOT the discrete integer-pair ShiftDiscreteWaveStep operation, a nonlinear covariant YM equation, a cutoff-consistent interacting continuum field, an OS Hamiltonian semigroup, or a Clay positive mass-gap theorem. Its exact samples alone do not establish continuum operator convergence.

## C. Original source coordinates and distinct y-z global marks

Independently check all 1024 positive link labels and all 1536 ordered plaquettes of the **original side-four 4D Wilson torus**. A Q8-valued SU(2)-subgroup background has \(U_z=i\) on the slice y=1,z=0, \(U_z=-1\) on y=1,z=2, identity elsewhere. Under a nonconstant local Q8 gauge field, every original plaquette satisfies \(P'_{\mu\nu}(x)=g(x)^{-1}P_{\mu\nu}(x)g(x)\) and invariant real trace; all 1536 exact comparisons pass.

The native Wilson trace deficit totals **96** in that deterministic fixture. At the original disjoint y-z marked plaquettes based at (0,0,0,0) and (0,0,0,2), the normalized marks are F=1 and G=2. The **globally unique** 1/F/G/FG integrand is
\[
e^{-96\beta}(1+sF)(1+tG)=e^{-96\beta}(1+s+2t+2st).
\]
The source four-column polynomial and gauge-transformed marks are exact. This is **at the original deterministic Wilson integrand**, not at the Haar-normalized partition, F19 fibre integrated measure, CMP119 differentiated density, or a connected W3 cluster sum. Never apply global affine marks independently at each polymer.

## Source-specific next junctions — do not duplicate existing compilers

- **Original W0:** inhabit existing CMP119Equation218FactorizedFunctionalData, BetaDrivenCompleteDensityInputs and BetaDrivenLocalizedEffectiveActionFamily with the **same** original SU(N) Wilson/F19 normalized 1/F/G/FG source, *actual* physical weak-running beta(a), E/R/B/V, gauge/background/FP/ghost/Haar change, domain/step/index/residual sources. Reuse existing YMClayCMP119122116SelectedProducerWeldExact; the source fields are not inferred from record declarations.
- **W1/W3:** transport unique global marks through true CMP119 T steps, then obtain a source-derived **absolute**, cutoff/volume-uniform marked connecting-shell charge and positive physical SI rate, not a signed telescoping, one-step small-beta q bound, or bare coarse Wilson action.
- **Wave-to-OS:** only after a changing-cutoff gauge-equivariant **nonlinear** dynamics has source-derived energy/norm stability and nonconstant generator convergence should one attempt positive-time OS representation, spectral faithfulness, E1/D1/D2/N1/G1.
- **TOE:** keep #1291 H05 8 vertices, 12 maps, six commuting faces and 27 signed/neutral states for provenance and loss-aware correspondence, not a physical gauge/OS/energy identification.

**Verification:** locally executed SymPy 1.14.0; exact zero wave residuals, Fourier Hessian and all 1536 non-Abelian gauge checks PASSED. No Agda kernel, GitHub CI, continuous compact-group Haar integration or new physical continuum theorem. Wilson/Haar/Bałaban and existing DASHI proof/wave owners retain attribution.
