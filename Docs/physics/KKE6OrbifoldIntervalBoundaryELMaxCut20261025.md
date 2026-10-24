# KK/E6 correction: zero-mode Higgs Hessian is NOT a 5D interval solution; nonconstant Robin-source repair
Date 2026-10-25. Canonical [KK physical PR #1241](https://github.com/chboishabba/dashi_agda/pull/1241). Source donor [original E6/trinification PR #1106](https://github.com/chboishabba/dashi_agda/pull/1106). **Executable owner:** \`scripts/check_kk_e6_orbifold_interval_higgs_bvp.py\`.

## Scientific/source-attribution reconciliation

The full E6/first-Tits source ALREADY EXISTS in the original #1106 and is not recreated:
- \`DASHI/Physics/Closure/Ternary27TrinificationE6SameActionExact.agda\`: norm-preserving literal SL3^3 action on first-Tits 27 and E6 root recovery; conditional physicality.
- \`Ternary27TrinificationInvariantTwoVEVPotentialExact.agda\`: a source-specific, six-invariant two-complex-bifundamental V6, not a full 27 scalar potential.
- \`Ternary27TrinificationTwoVEVLocalStabilityExact.agda\`: source numerical 36-real Hessian at original E32/E33 vacuum, not a quantum/experimental mass theorem.
- Downstream \`KKE6OrbifoldBoundaryHiggsConsumerExact.agda\` and \`check_kk_e6_orbifold_boundary_higgs_hessian.py\`: orbifold-even constant zero-mode 18×18 Hessian and 36-real integrated gradient.

**Crucial correction to preceding research:** The previous source's phrase "full 36-real-coordinate stationary classical vacuum" referred to the ZERO-MODE-TRUNCATED integrated effective four-dimensional potential \`V6+V_boundary\` with a CONSTANT scalar profile. It was **NOT a solution of the genuine five-dimensional bulk equations plus boundary conditions**. Do not use its 7 Goldstones/11 positive Hessian as an actual 5D local minimum or as a complete scalar spectrum. This repair does NOT negate the earlier 18-real finite Hessian calculation *in its declared homogeneous restricted problem*.

Original external theory: the orbifold/interval bulk boundary-value problem and importance of brane Higgs boundary conditions are well known. R. Leng, G. Moreau, F. Nortier, *Rigorous treatment of the orbifold model with brane-Higgs couplings*, Phys Rev D 103 (2021) 075010, DOI **10.1103/PhysRevD.103.075010**; R. Barceló, S. Mitra, G. Moreau, *On a boundary-localized Higgs boson in 5D theories*, Eur Phys J C 75 (2015) 527, DOI **10.1140/epjc/s10052-015-3756-3**; E6 27 Slansky Phys Rep 79 (1981), original orbifold fixed-plane anomalies Arkani-Hamed/Cohen/Georgi 2001 and von Gersdorff/Quirós 2003. The current script is a new selected *numerical toy/source consistency test* rather than discovery of boundary variations.

## Actual five-dimensional variational condition

Write the selected parity-even scalar ansatz (Eij are 3×3 matrix units):
\[
\Phi(y)=a(y)E_{32},\qquad
\Chi(y)=b(y)E_{33}+t(y)E_{21}.
\]
The literal original six-invariant V6 restricted to these amplitudes is
\[
V_6(a,b,t)=a^4+a^2t^2-2a^2+b^4+4b^2t^2-2b^2+t^4-2t^2+2 .
\]
Choose explicitly for a **DIMENSIONLESS COMPARISON MODEL** interval \([0,1]\), canonical real scalar kinetic coefficients \(\tfrac12(a'^2+b'^2+t'^2)\), and symmetric fixed-plane energy
\[
W(t)=-\frac{\mu^2}{2}t^2+\frac{\lambda}{2}t^4,\qquad
E[a,b,t]=\int_0^1\left[\frac12(a'^2+b'^2+t'^2)+V_6(a,b,t)\right]dy+W(t(0))+W(t(1)).
\]
This is a newly declared **tree-level scalar-only interval action** (source group orbifold parity compatible), NOT the physical dimensionful L=πb0 and 5D gauge-gravity quantum action. Keeping the old t=.0246, λ=4, μ²=3.00090774 numbers is a **replay fixture only**.

Interior Euler–Lagrange:
\[
\begin{aligned}
a''&=4a^3+2at^2-4a,\\
b''&=4b^3+8bt^2-4b,\\
t''&=2a^2t+8b^2t+4t^3-4t.
\end{aligned}
\]
Actual natural boundary conditions (for both endpoints):
\[
\begin{aligned}
a'(0)=a'(1)&=0,\quad b'(0)=b'(1)=0,\\
t'(0)&=W'(t(0))=-\mu^2t(0)+2\lambda t(0)^3,\\
t'(1)&=-W'(t(1))=\mu^2t(1)-2\lambda t(1)^3.
\end{aligned}
\]
These are NOT interchangeable with a vanishing derivative of \(V_6+2W\) at constant fields.

## Exact negative control: previous constant profile is not a 5D field solution

The old integrated zero-mode stationary parametrization is
\[
a^2=1-\tfrac12t^2,\quad b^2=1-2t^2,\quad
\mu^2=3+(2\lambda-\tfrac{13}{2})t^2.
\]
At any nonzero \(t\) near the original trial, the **bulk** force is
\[
\left.\frac{\partial V_6}{\partial t}\right|_{\rm old}
=t(6-13t^2)\neq0.
\]
At \(t=.0246\) this is \(+0.147406469832\). The summed two-endpoint force is
\[
2W'(t)=-2\mu^2t+4\lambda t^3=-t(6-13t^2),
\]
canceling only in the INTEGRATED homogeneous truncation. In the actual interior \(\partial_y t=0\) gives \(t''=0\), which contradicts \(\partial_tV_6\neq0\). Independently, the nonzero \(W'(t)\) violates Robin BC for a constant field. Therefore the previously reported constant-profile field was **not a 5D Euler–Lagrange vacuum**, regardless of the homogeneous 18-real Hessian signs.

## Constructive nonconstant interval repair, with its domain of validity

\`scripts/check_kk_e6_orbifold_interval_higgs_bvp.py\` uses SciPy \`solve_bvp\` at dimensionless interval L=1, \(\lambda=4,\mu^2=3.00090774\), and a NONCONSTANT smooth symmetric ansatz. Its numerical solution:
- Boundary \(a(0)=a(1)\approx0.97776063,\ b(0)=b(1)\approx0.90869439,\ t(0)=t(1)\approx0.38844156\);
- Midpoint \(a(1/2)\approx0.98085326,\ b(1/2)\approx0.92047817,\ t(1/2)\approx0.23107359\);
- Both endpoint Neumann/Robin boundary residuals at machine precision, and dense bulk ODE residual tested against differentiable solver interpolation.
- The actual original **full 36-real source V6** gradients evaluated with independent PyTorch autodiff at several interval points have zero off-ansatz components and agree with the RHS of the three-field bulk equations. All 16 possible L/R gauge-current components along the y profile vanish numerically at selected interior points when \(A_y=0\). Thus this is a consistent restricted **classical scalar/gauge-current** solution of the declared comparison action—not merely a three-coordinate extremum of an integrated potential.
- Its source energy \(E\approx-0.06997758137\), below the unbroken-t zero-reference \(E=0\) within this dimensionless action. **This is not a cosmological constant or 4D Minkowski claim**.
- Independently a 3-real-field piecewise-linear interval FEM Hessian with 80 segments including endpoint \(W''\), tested as a generalized eigenproblem against the FEM mass matrix, gives the lowest three positive eigenvalues ≈ \(2.48955,\ 7.60654,\ 10.95093\). This establishes numerical local positivity **within this three-amplitude ansatz** only—not the full 18 real even scalar fields or the 5D gauge/ghost/matter spectrum.

This is a much stronger actual SOURCE REPAIR. **However:** the comparison interval length L=1 and kinetic normalization were DECLARED, not derived from the previous b0=10^-24m circle or source 5D M5/g5/v/brane-tension dimensional action. Converting to the physical tiny L=πb0 can radically alter boundary forcing and mode profiles, and must be done through explicit normalizations—not by relabeling the dimensionless solution. The full 18-even-field functional second variation along the spatially VARYING background, even/odd gauge KK modes, brane Higgs one-loop renormalization, anomaly-free Green–Schwarz axion and chiral matter masses remain OPEN.

## Critical physical consequences / follow-on steelman

1. Source-first interval model **requires** separate bulk differential EOM and localized Robin boundary conditions. A zero-mode gradient/Hessian is an effective/truncated consumer, not a substitute.
2. The full consistent 5D *Einstein* source also requires **boundary stress/junction conditions**, not only smooth bulk \(T_{55}\). Brane scalar potential and localized tensions cannot be slipped into the Minkowski×S1 pressure condition unchanged. Existing GR/Minkowski and same-metric Casimir transport owners remain valuable when the physical source is supplied.
3. The massless photon is algebraically the same \(Q=T3_L+Y\) if the orbifold/parity VEV directions remain, but background profiles, physically derived g5 and kinetic mixings/normalization must be supplied to confirm a **normalisable zero mode** and measured electric couplings.
4. The 27-derived chiral zero-mode content and factorized UV \(F_L-F_R\) anomaly are distinct SOURCE CONSUMERS; this scalar BVP does not cancel the local/global anomaly. Prior Chi33 half-phase quantisation/Green–Schwarz action remains the highest-risk model eligibility gate.
5. Honest top outcome: an actual anomaly-safe dimensionful 5D SU3³ orbifold with consistently solved bulk+brane Higgs/fermion/gauge equations and one photon; then a regulated interval metric-varying effective action, global radion/holonomy vacuum, and discriminating PPN/LARES null/positive result. Formal 27 roots, numeric agreement, and the present classical toy alone do NOT constitute full E6 gauging, SM, gravity anomaly or TOE.

**Status:** Exact algebraic bulk+boundary incompatibility of old uniform vacuum reproduced independently in SymPy; scipy comparison interval solution and FEM positivity reproduced independently; GitHub source uploaded, verify its exact head separately. Agda/Lean kernel, actual dimensionful full 5D EFT, real GS/CS quantum anomaly consistency, full nontruncated stability and observational evidence remain UNVERIFIED/OPEN.


## Physical-radius scale separation makes the old approximation useful, not exact

The source reference (b_0=10^{-24})m corresponds to inverse radius (1/b_0=1.973269804	imes10^8) GeV using (hbar c=0.1973269804	imes10^{-15}) GeV·m. For a *hypothetical* normalized (v=10)TeV scalar source on physical interval (L=pi b_0), the dimensionless derivative parameter is (epsilon=vLapprox1.59207456	imes10^{-4}), (epsilon^2approx2.5347014	imes10^{-8}). If the bulk and endpoint coefficients are chosen with matching source action normalisation so that the zero-mode effective stationarity relation holds, then in (u=y/Lin[0,1]), the scalar E-L equation has form (f_{uu}=epsilon^2partial_fV_6) and the Robin derivative is likewise (epsilon^2partial_f W). Its leading symmetric t-profile around the old homogeneous source is (t(u)=t_0+rac12epsilon^2 partial_tV_6(t_0)(u-rac12)^2+O(epsilon^4)) **up to a constant of order (epsilon^2)** determined by higher-order solvability. The leading end-minus-midpoint shift in the t field is (epsilon^2partial_tV_6/8approx4.6703923	imes10^{-10}), so a homogeneous source might be an *excellent approximation* in that restricted weakly coupled/short-interval regime while NEVER an exact bulk field solution. Source `scripts/check_kk_e6_orbifold_small_interval_scale.py` checks this dimensionful-reference expansion but does not derive physical five-dimensional couplings from E6.

For orbifold-ODD Dirichlet scalar modes with a uniform background and canonical kinetic source, the Poincaré gap is (m_{KK,1}=1/b_0approx1.97	imes10^8)GeV; any selected potential Hessian bounded below by (-10v^2) still leaves (m_{1}^2ge b_0^{-2}-10v^2>0). This is a **conditional** gap criterion, not a proof of the source's spatially varying full 5D Hessian or other brane/ghost/gauge sectors. The physical boundary potential and odd gradient-energy scaling must be fixed BEFORE a full stability/quantum/stress promotion. In particular, the hypothetical dimensionless length-one BVP above cannot be identified with the physical microscopic source by relabeling y.
