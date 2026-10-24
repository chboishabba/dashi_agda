# KK Earth bridge: source sectors, Higgs and EM as fifth dimension (2026-10-24)

## Literature bridge ownership
The 5D vacuum Kaluza–Klein circle reduction gives a 4D Einstein–Maxwell–dilaton system with specific dilaton–Maxwell coupling a=sqrt(3), not arbitrary Einstein–Maxwell, Higgs, or every stabilised compactification. Rotating black-hole representatives include Rasheed (Nucl Phys B 454 (1995), 379–401, DOI 10.1016/0550-3213(95)00396-A), and the 2026 EMD review by Herdeiro/Radu/dos Santos Costa Filho DOI 10.1088/1475-7516/2026/04/005. Existing PRs #1238/#1239/#1241 own the curvature, 5D null waves, boosted Kerr metric, and first-order orbital calculations.

Eingorn, Fakhr and Zhuk, CQG 30 (2013) 115004, DOI 10.1088/0264-9381/30/11/115004, specifically give multicomponent stabilised spherical-compactification examples with one tension-free source (Omega=0). This is evidence that source tension is model-dependent, **not** a theorem that a 5D circle vacuum model has the same matter action or field equations as that spherical compactification. Distinguish internal S^1 from S^d, background fields, potential, and physical matter frame. See Eingorn/Zhuk Phys Lett B 716 (2012), 176–178, DOI 10.1016/j.physletb.2012.08.031 on tension and effective external pressure.

## Algebraic source-sector test
For exact 5D product g5=g4+dw² with phi=1 and F_mu nu(KK)=0, Einstein equations imply T55=1/2 g4^mu nu T_mu nu (up to consistent 5D normalization). The script checks necessary-sector compatibility:
- dust p~0 with zero internal pressure fails by rho/2;
- four-dimensional traceless radiation with T55=0 passes;
- a 5D Maxwell field having only F_mu nu components has 4D trace zero but T55=-F_mu nu F^mu nu/4, so generically fails, except null field invariant F²=0 or compensating sources;
- a 5D scalar depending on 4D coordinates, with canonical L=-1/2(∂Phi)²-V(Phi), gives 4D trace -K-4V, T55=-K/2-V, hence residual V. Kinetic part itself satisfies the necessary identity; nonzero scalar potential alone does not.

These are necessary algebraic compatibility tests, NOT full field equations, matching, perturbative stability or demonstrations that EM/nuclear/Higgs provide an Earth source. Strong/nuclear forces involve stress and binding energy, but do not automatically generate a particular fifth-direction tension. Geometry-derived U(1) gauge potential A_mu=g_mu5/g55 is not the Higgs: radius phi=sqrt(g55) is a neutral radion scalar; an electroweak Higgs doublet needs nonabelian group representation / e.g. gauge-Higgs unification A5 for a larger gauge group. The radion potential can be produced in a specified extended theory by flux, quantum/Casimir terms, bulk scalar/Higgs sector etc; introducing these changes pure 5D vacuum Einstein model and must be documented.

## Physical source bridge requirements
Fix ONE 5D action and circle topology; derive complete 4D EMD/radion action with matter; specify 5D stress-energy including compact direction; prove regular interior, exterior, junction and asymptotic conditions, charge/flux conservation and physically selected 4D metric; then solve slow-rotation frame dragging and satellite motion. Coupling choices must not be patched between unrelated papers. No direct KK/LARES parameter bound follows. User's SensibLaw SLR, PNF, W3 are not dependencies.

## Acceptance
python3 scripts/check_kk_earth_source_sector_compatibility.py
Local symbolic arithmetic test passed. Agda kernel, exact-head run, Earth solution and empirical fit unverified.
