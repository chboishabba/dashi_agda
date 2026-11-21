# OCT369 P0.34 — Original Field Loom coil → Pt-centred magnetic force → source reaction → physical endpoints

Date: 2026-11-22. PR #1534, branch agent/oct369-gravity-schumann-20261121.

## The endpoint-first source cut
P0.33 used locally harmonic polynomial scalar magnetic potentials, leaving their current generator unspecified. P0.34 replaces those ideal potentials with the already **original-repository-owned** explicit two finite circular current-filament sources in \`scripts/psychotronics_field_loom_coils.py\`; its existing independent \`scripts/test_psychotronics_field_loom_biot_savart_reuse.py\` compares the original numerical Biot–Savart field against an elliptic-integral field. \`DASHI/Physics/Closure/FieldLoomExistingBiotSavartReuseExact.agda\` is the prior owner explicitly preventing another invention of the Biot–Savart law, and already distinguishes numerical finite-filament source from Fourier inverse-curl Agda theorems. P0.27 owns the **Pt-origin inversion six-site** selected finite magnetic trial, P0.33 owns the typed lift/metric/fifth-force/stability endpoints. Do not conflate with P0.25's three site × two magnetic-domain labels.

## Same original Maxwell source, not a prescribed field
Two zero-thickness circular turns of radius R on the [111] axis, centered at z=+h and z=-h, current turns=n and currents I_+, I_-:
\[
B_z(z)={\mu_0 n R^2\over2}\left[
{I_+\over(R^2+(z-h)^2)^{3/2}}+
{I_-\over(R^2+(z+h)^2)^{3/2}}
\right].
\]
These are ordinary Biot–Savart fields of a *spatially bounded but mathematically thin* source current. The off-axis field is evaluated via the original numerical loop kernel AND an independent standard elliptic-integral form. In the current-free aperture Maxwell gives \(\nabla\cdot B=0\), \(\nabla\times B=0\), and the regular cylindrical expansion \(B_\rho=-\rho B_z'/2+\rho^3B_z'''/16+\cdots\). \(\mu_0=4\pi10^{-7}\) is the original Field Loom historical synthetic baseline, not an exactly defined post-2019 SI value; for actual metrology use current CODATA and uncertainty.
For exactly the same fixed Pt-origin six-site 120° trial geometry, site magnetic energy \(\mathcal E=-\sum_a {\bf m}_a\cdot{\bf B}({\bf R}+{\bf r}_a)\), the small \(a/R\) asymptote gives
\[
\mathcal E(R_z)\simeq {N\mu a^2\over\sqrt2} B_z''(R_z),\quad
F_z\simeq-{N\mu a^2\over\sqrt2} B_z'''(0),\quad
K_z\simeq{N\mu a^2\over\sqrt2} B_z''''(0).
\]
The two exact circular-loop source coefficients are \(g_3=\partial_z^3[R^2/(2(R^2+(z-h)^2)^{3/2})]_{z=0}\) and \(g_4\) similarly for order 4. Odd and even parity decouple: \(B'''=\mu_0 n g_3(I_+-I_-)\), \(B''''=\mu_0 n g_4(I_++I_-)\). The inverse targets are
\[
I_{\rm diff}=-{F_\star\sqrt2\over N\mu a^2\mu_0 n g_3},\quad
I_{\rm sum}={K_\star\sqrt2\over N\mu a^2\mu_0 n g_4},\quad
I_\pm=(I_{\rm sum}\pm I_{\rm diff})/2.
\]
At h=R/2 the quadratic on-axis derivative is zero, while third and fourth derivatives are nonzero. Full force derivatives and finite magnetic-site reaction must still be evaluated beyond the small-motif expansion. This particular axisymmetric ring mode is NOT equivalent to the full anisotropic P0.33 quartic/quintic spherical harmonics, though its selected vertical force and stiffness can be matched.

## Independent, source-reaction numerical validation
Local detailed \`check_oct369_p034_field_loom_coil_source_bidi.py\`: **63/63** exact/numeric local checks, source SHA c356c352e29c2e1406716af4c2ace026e4ef0b84. Existing original Field Loom source Git SHA 342bf32aadda4d29b671f3b263d6afc7ea29b57e; locally imported file had identical Git hash. Source field vs elliptic max relative error 2.90e-14; vacuum div/curl finite difference; Pt-site trial zero net dipole. A clearly *mesoscopic algebraic analog* (a=4mm, moments 0.03 A m², R=5cm, h=2.5cm, n=100, upper=+10A, lower=-8A) gives F_z(body)=+3.372648026e-4 N, independent Lorentz \(\sum_{\rm coils} n I\oint d\ell\times B_{\rm six\ dipoles}\) F_z(source)=-3.372649989e-4 N (relative mismatch ~5.82e-7). The leading multipole force 3.375163347e-4 N differs by only 0.0746% for that mesoscopic a/R=.08. The entire 3D stiffness Hessian is approximately diagonal (0.00134025,0.00134025,-0.00268029) N/m, with zero trace to the stated finite-difference tolerance. This source with those particular currents has **negative vertical stiffness**, not stable levitation.

## Rigorous limitation: no passive fixed-moment 3D stable equilibrium
In the source-free aperture each Cartesian component of B is harmonic, so the rigid fixed-site energy has \(\nabla_{\bf R}^2\mathcal E=0\). With C3 symmetry, \(K_{\perp1}=K_{\perp2}=-K_z/2\); even if current sum is reversed to make \(K_z>0\), the transverse eigenvalues are negative. A physically independent active controller, mechanical constraint or real diamagnetic/superconductor constitutive source must supply the stability and its stresses. The earlier P0.33 condition \(K_{\rm controller,\perp}>K_z/2\) is a **conditional linearized bound**, not a complete feedback loop design or a safety certificate.

## End-to-start force feasibility for the selected microscopic assumptions
Illustrative NON-MATERIAL-CALIBRATED \(\mu=3\mu_B\), \(a=0.4nm\), one 1mm³ active region with optimistic N=L³/(2a³)=7.8125e18 independent six-site pairs, 100 turns at R=.05m,h=.025m: force transfer \(\simeq1.359e{-21}\,\mathrm{N/A}\) for current difference. To balance 70kg, F*=686.4655N, \(I_{\rm diff}\approx5.053e23\) A; to simultaneously demand Kz=100 N/m, \(I_{\rm sum}\approx-1.0223e21\) A. That nominal inverse would produce central field ~-9.19e17 T and field magnitude ~5.53e18 T at a selected 1mm location in the same ideal model, massively outside material validity and realizable sources. Thus the selected source/material/packing combination is not a feasible human-lift design. No universal no-go follows for conventional superconducting levitation or other devices. The 1mm³ active region is not a 70kg body, and the constitutive domain/current/thermal limits were never fitted.

## Separate gravitational endpoint / stress ledger
For an illustrative uniform 10 T field in 1mm³, local ordinary EM magnetic energy \(B²V/(2\mu_0)\approx0.03979\) J, positive mass-equivalent \(\approx4.43e{-19}\) kg, attractive monopole acceleration magnitude only \(\approx2.95e{-29}\) m/s² at 1m. This is **not total coil energy or total apparatus gravitational mass**; a zero-thickness filament has divergent self-energy without finite wire radius, and the physical coil/cryostat/support stress tensor remains uncomputed. This positive local EM energy does NOT produce P0.33's outward gravitational monopole target. Genuine nonminimal metric theory and a fifth force retain their own source, equations, clock/freefall/test-body and independent measurement gates. No anomalous gravity or human levitation is observed or predicted by the demonstrated source.

## Exact provenance and next source payment
Standard original physics: Biot–Savart, Maxwell, Lorentz reciprocity, circular-loop elliptic integrals, Earnshaw and Einstein/Newton gravitational stress (not DASHI discoveries). Educational verification: OpenStax, University Physics 2, §12.4 https://openstax.org/books/university-physics-volume-2/pages/12-4-magnetic-field-of-a-current-loop . Earlier original DASHI: Field Loom \`psychotronics_field_loom_coils.py\`, \`test_psychotronics_field_loom_biot_savart_reuse.py\`, \`FieldLoomExistingBiotSavartReuseExact.agda\`, P0.27 and P0.33; prior BIDI endpoints \`AntigravityMaterialBidiCrossPollinationExact\` and \`CMP119AntigravityTraceVsActiveStressFirewallExact\`. Original PtMn3 experimental OTT/TMR remains Kang et al Nature 2026 DOI 10.1038/s41586-026-11172-5; Sato/Hayami and Ōiké/Peters/Shinada retain periodic octupole/thermodynamic theory priority. **New DASHI P0.34 only**: reuse/source-consistent finite ring + exact angular reaction + inverse-target compatibility certificate.
Next: finite **nonzero-radius** conductor, coil cooling and power with measured B(x,t), sample dimensions/real film domains, actual material response with Maxwell/London/SC boundary and controller/suspension power, complete \(\int T_{\mu\nu}\) and exterior metric; then P0.25's distinct load/freefall/testmass/clock/impulse observations. Agda not compiled. The full 63-check local source is a conversation artifact; the **26-check compact consumer is committed**. The P0.33 66-check full source and its original receipt are also being committed, resolving that prior archival gap.
