# Boosted KK: fixed-physical-input comparison (2026-10-24)

No SensibLaw/SLR repo, PNF, or W3 dependency. In the physics context SLR is satellite laser ranging, a measurement technique, not user software.

For q=sinh²(alpha), seed geometric mass M and asymptotic Einstein-frame ADM mass M4=M(1+q/2), with fixed physical J, the linear-spin equatorial quotient has H=1+2Mq/r, g_tphi=-2J/(r sqrt(H)), g_phiphi=r²sqrt(H). Set circumferential radius R=sqrt(g_phiphi)=r H^(1/4). Local dragging angular velocity is omega=-g_tphi/g_phiphi=2J/(r³H). Compare to GR 2J/R³ at the **same physical R,J,M4**: exact ratio (linear-spin equator) is H^(-1/4), using M=M4/(1+q/2) and the implicit radius map R=r H^(1/4). Previous fixed-coordinate-r H^-1 comparison is not an invariant physical-radius comparison.

Script: `python3 scripts/check_kk_areal_radius_comparison.py`. Illustrative alpha=1: delta=-2.3166280e-10 at R=7820km; delta=-1.47644896e-10 at R=12270km. This is a **local frame-dragging comparison**, not a nodal precession of a full orbit or a physical Earth constraint. It uses a charged/dilatonic boosted Kerr vacuum exterior, not Earth's interior and exterior matching, and assumes the Einstein-frame metric governs neutral matter. This comparison does not establish any experimental KK parameter bound.

Highest-priority remaining physical task: specify admissible Earth matter with boundary/junction conditions and KK scalar/gauge charges; calibrate physical mass/spin, integrate full perturbed 4D trajectories, and compare coordinate-independent orbital observables before interpreting satellite laser ranging data. Existing ThreeBody abstractions can host a step/energy interface but do not substitute for those physics. No formal Agda kernel receipt.
