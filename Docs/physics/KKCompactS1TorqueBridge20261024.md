# Compact S1, torque and KK source bridge (2026-10-24)

The classic Klein hypothesis is a small compact fifth spatial circle S1, not the extra dimension being destroyed or physically curled by a torque. Write y~y+2pi R and metric ds5²=g4+phi²(dy+kappa A)² in a local chart. A fixed circle topology does NOT fix radion size: phi(x) may vary, physical circumference is 2pi R phi(x) in this coordinate convention. In a nontrivial principal U1 bundle there need not be a single global y; local coordinates are related by gauge transitions; circle-fibre topology is still present.

Standard Fourier eigenmodes e^(in y/R) yield squared extra-dimensional wavenumbers n²/R², with model-dependent physical 4D masses and interactions. Zero mode n=0 is the y-independent truncation, not a proof higher modes vanish. Gauge shifts y' = y - kappa chi, A' = A+dchi preserve dy+kappa A. See Bailin and Love (1987) Rep Prog Phys 50 1087 DOI 10.1088/0034-4885/50/9/001 and standard KK reviews.

Repo donors:
- PR #1164 torque / SO3 ordered-axis angular momentum, right-hand-rule and C3 parity
- master DASHI/Physics/Foundations/ContinuousSO3Torque369BridgeExact.agda
- PR #1239 DASHI/Physics/Electromagnetism/KaluzaKleinGaugeShiftExact.agda and the exact S1 5D metric fixture
- PR #1235 HopfU1 principal bundle, overlap/cocycle candidate
- PR #1241 radion interior/exterior sourced linear effective model

Critical distinction: SO3 spatial rotation/angular momentum is a different group/action from fibre U1 translation and KK quantized momentum. Connections can be built through a representation/realizing map, but 3/6/9 or torque orientation alone is no witness that circle winding is physical rotational torque. Curled topology is not a radion-stabilization equation or a source stress tensor.

Next physical proof: single five-dimensional action, S1 period, matter field boundary/twisted periodicity, 4D effective action with radion potential and actual KK mode masses, then matched Earth-sourcing and slow-rotation g_tphi. The 5D vacuum Einstein-Hilbert term alone need not stabilise the size of its circle. Do not identify Higgs and radion by name only. No W3/PNF/SensibLaw dependency.

Acceptance: python3 scripts/check_kk_compact_circle_torque_bridge.py. Only elementary symbolic fixture, not Agda kernel or physical Earth solution.
