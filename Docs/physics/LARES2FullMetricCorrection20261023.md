# LARES-2 × KK full reduced-metric correction — 2026-10-23
This is the follow-up to PR #1241's initial boosted Kerr frame-dragging proxy. The earlier g_(t phi) metric-factor ratio H^-1/2 **must not** be called the physical local frame-dragging rate: the azimuthal component g_(phi phi) also changes.

Define q=sinh²(alpha), H=1+2Mq/r in the linear-spin equatorial far-field limit, J=Ma cosh(alpha). In the Einstein-frame reduced metric:
- g_tt=-(1-2M/r)/sqrt(H)
- g_phiphi=r² sqrt(H)
- g_tphi=-2J/(r sqrt(H))
- Omega_drag = -g_tphi/g_phiphi = 2J/(r³ H), exact for the linear-spin metric components.
- Equatorial circular frequency at zero spin follows Omega_circ² = -partial_r(g_tt)/partial_r(g_phiphi), an exact static quotient identity; it differs from a Kepler circular frequency at fixed ADM M4=M(1+q/2).

A **selected orbit-averaged local frame-dragging proxy** over an unperturbed Kepler ellipse is R=<r^-3 H^-1>/<r^-3>=1-2Mq/a_orb (1+e²/2)/(1-e²)+O((Mq/a_orb)²). For alpha=1 representative 12,270km orbit its delta is ~-9.98434e-10, about twice the earlier component-only proxy.

This remains **not** a full satellite nodal precession: consistent orbital plane perturbation must use full stationary-axisymmetric geodesics or Lagrange planetary equations, including radial and polar metric terms; gravitational parameters must be calibrated to measured Earth, and the boosted Kerr charge/radion/interior must be physically justified. No experimental bound on KK alpha, no observational validation, no Agda kernel receipt. Symbolic and quadrature fixture: scripts/check_boosted_kerr_full_metric.py. The prior check_boosted_kerr_nodal_proxy.py remains a labelled *component proxy*, not a reliable nodal observable.

Exact zero boost reproduces GR local shift; leading 1/r spin term at fixed physical J is universal. The relevant comparison must identify the satellite matter frame and coupling before using any frame-dragging constraint.
