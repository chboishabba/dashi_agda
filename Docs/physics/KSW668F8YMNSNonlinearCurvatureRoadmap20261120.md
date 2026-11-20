# F8 gravitational path — YM/NS weld and nonlinear curvature cut, 2026-11-20

Predecessor: ProgrammeAttribution369GeometricReuseContract20261120.md at 39f17d211d3d91a948b12cf37b8db9ba4e74df75.
Original F8 order-3 model: PR #1527 at 123eff9204d91e2b1967e9e72d3d68771f27287f, scripts/ksw668_f8_tt_multipole.py; #1520 coupled weighted SBP. Retain original source, Caldwell–Langlois/Thorne/SBP and DASHI contributor provenance. Source donors at master 116cd7de01b8a0da03703b3bb8db79c67fd15b50: SU2Bracket369OrientationBridgeExact, OrientedBracketEMYMNS369Regression, NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact, NSCriticalConeResidualFibre369CrossPollinationExact. The previous optical crosswalk is not a new discovery of the covariance identity.

## Executable receipts
- scripts/check_f8_ym_ns_weld.py: prior local test-grid receipt (267 active radial nodes, 71 normal nodes, 904 steps, 801 eigenmodes; final t=12). Relative history errors 3.98e-12, 6.83e-12, 1.49e-12; two finite-difference Weyl readouts -6.81609907e-5 and -3.13104776e-6. Native here means reconstructed order-3 stencil, not byte-identical production solver invocation. Prior receipt not re-executed this turn.
- Temporal FFT bin 3 diagonal 7.53149e-4, coherent 3.72949e-8, signed covariance 0.8130583241135367 vs 0.8130583241135584. These are receiver interference, not nonlinear spectral energy transfer, and the centering rates are radial eigenvalues, not physical decay rates.
- scripts/check_f8_perturbed_curvature.py: locally executed SymPy PASS this turn: 5 metric compatibility, 10 torsion-free, 10 background/linear/quadratic curvature and 10 coordinate/frame transport checks, exact Ricci residual. Metric L²/z² diag(-1,1,exp(2h),exp(-2h),1), h(T,x,z); polarized plane sector only, not the full F8 TT tensor. E=Ric+4g/L² has base block -2 dh ⊗ dh, fiber entries -exp(2h) wave(h), +exp(-2h) wave(h), wave=-h_TT+h_xx+h_zz-3h_z/z. A nonconstant linear TT solution generally fails vacuum Einstein on this restricted metric. This is a derivation/check of standard GR, not a new physical theory. Nonlinear metric correction and moving Israel boundary remain open.

## Ordered acceptance ledger
- P0.1–2 prior weighted radial separation exact/single-step numerical pass; P0.3/5 full-duration test-grid forward and both finite-difference Weyl parity partial; P0.4 full-duration adjoint OPEN; P0.6 production grid and checkpoint/resume OPEN.
- P1.1–2 signed coherent receiver work/Gram test-grid pass; P1.3 physical derivative and energy exchange ledger OPEN. No evidence of nonlinear cascade.
- P2.1–3 SU2 spatial map, Lorentz sign and background connection test pass; actual perturbed polarized spin connection pass, full F8 tensor weld OPEN.
- G2/G3 and G5 fully coupled stability and independent convergence OPEN. Retain original unequal d=3,7,11 and SAT boundary; no physical C3 permutation.
- P4 source electron–Maxwell dynamics, P5 conserved matter/bulk/brane stress, P6 full second-order Einstein tensor source and constraints including brane junction, P7 actual resonant transfer vs forcing/numerics, P8 calibration all OPEN.
- Next mathematical cut: solve second-order metric correction with same gauge and boundary from E(gbar+epsilon h1+epsilon² h2)=0; enforce constraints, not just TT projection. The polarized residual is a negative control and source check, not a substitute for the original F8 tensor. Production forward/adjoint, checkpoint and both-Weyl refinement remain on critical path.

Agda kernel not run. No continuum, experimental or gravity turbulence closure asserted. No changes to ESD or silent imports from unmerged branches.
