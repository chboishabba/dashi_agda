# OCT369 P0.33 — Steelman bidirectional endpoint / source / geometry targets
**Date:** 2026-11-22 (Australia/Brisbane). **Branch:** agent/oct369-gravity-schumann-20261121. **PR:** #1534.

## Governing rule
This is **not** evidence of antigravity, PtMn3 levitation or gravity modification. Start from a declared measurable endpoint, choose a fully specified physical mechanism, backsolve **material, geometry, source, controller, reaction, and measurement** requirements, then forward-reconstruct the endpoint. Do not conflate ordinary electromagnetic traction, an extra fifth-force coupling, and metric curvature.

Reuse original native owners: \`DASHI/Physics/ExoticGravity/AntigravityMaterialBidiCrossPollinationExact.agda\` (six distinct claims/discriminators), \`EngineeredInertialGravitationalBidiExact.agda\` (mechanism competing families and independent observables), \`CMP119AntigravityTraceVsActiveStressFirewallExact.agda\` (trace != active), \`GRFirstOrderGravityScope.agda\` and OCT369 P0.24/P0.25–28/P0.32. The original experimental work by Kang et al., Nature (2026), DOI 10.1038/s41586-026-11172-5 concerns PtMn3 octupole torque and tunnel magnetoresistance, **not gravitational engineering**. Sato and Hayami's 2026 DOI 10.1038/s41535-026-00865-9, Ōiké/Peters/Shinada's 2025 work, and standard crystallography/Bloch/Wannier theory retain their scientific authorship. Maxwell, Earnshaw, Newton, Einstein, Yukawa and Tolman–Laue are established original physics, not new DASHI discoveries.

## Endpoint 1: mechanically support 70 kg with octupole-conditioned external field
P0.26–28 own the selected **finite** Pt-centred six-site inversion pair and the source-free local harmonic quartic magnetic potential:
- in an orthonormal [111] frame (u,v,w), f3(v,w)=v³−3vw²;
- Φ4=κ4 u f3, B4=−∇Φ4, where ∇²Φ4=0;
- fixed site-dipole energy E4=3μa²κ4 u per pair, giving F_up=−3Nμa²κ4 for N identical pair equivalents;
- inversion of the 70 kg load: **κ4=−mg/(3Nμa²)**, with equal-and-opposite reaction at the field source.
The same-source P0.33 extension adds a *different*, fifth-degree harmonic Maxwell scalar potential Φ5=κ5 [u²−(v²+w²)/8] f3, also Laplacian-zero; its fixed-pair energy, ignoring a constant, is E5=3μa²κ5[u²−(v²+w²)/2]. The combined translating-body source stiffness is

  K_magnetic=diag(6,−3,−3) N μ a² κ5    in (u,v,w).

Thus κ5=K_z/(6Nμa²) produces desired **positive vertical stiffness K_z**, but simultaneously **negative transverse stiffness −K_z/2 in both lateral directions**. Φ4 by itself produces force but exactly zero stiffness. A separate stabilizer must supply K_controller,lateral > K_z/2 in each transverse axis *in this particular symmetric fixture*. This is an Earnshaw-type no-go for **fixed magnetic moments, unconstrained translation, and a locally current-free field**. A superconducting/diamagnetic/feedback controller, tilt dynamics and actual 6DOF stability may escape the fixed-moment assumptions but need their own calibrated action, energy and force reaction. No assertion the 70 kg person is safe or such a device exists.
**Type boundary:** the six physical Pt-inversion points here are not the P0.25 six (Mn-sublattice × opposite magnetic-domain) signed ternary addresses. The trial spin texture and moment μ, length a and N have no actual measured PtMn3 film calibration. The polynomial source is Maxwell-compatible only in the modeled source-free region; source coil, power, field aperture, surface sample and support are not generated.

## Endpoint 2: an actual remote metric acceleration change
Use a *distinct* test mass/clock, not solely a load cell. Under ordinary Newtonian/weak-field **isolated point-monopole** exterior gravity, ΔΦ=−GΔM_active/r, Δa_r=−GΔM_active/r², and a distant-reference weak-field clock target Δν/ν≈ΔΦ/c². Therefore an OUTWARD perturbation Δa_r=f g at r requires

  ΔM_active=−f g r²/G ;  ΔE=ΔM_active c² ;  Δν/ν≈ f g r/c² .

At r=1 metre:
- 100% g: −1.469315134e11 kg active mass-equivalent, −1.320554586e28 J equivalent, positive clock fractional shift ≈1.091136967e−16.
- 1% g: −1.469315134e9 kg, −1.320554586e26 J, clock shift ≈1.091136967e−18.

These are **not universal no-go bounds** for additional fields, nonminimal curvature coupling, extended geometry or any nonstandard gravitational action. In particular they do not prove that a negative ADM mass source exists. The original CMP119 active-stress owner must not be skipped: trace(T)=−ρ+Σp and local active(T)=ρ+Σp. In an ideal **static, spatially isolated, conserved** total stress including all source coils/controller/shells, the integrated spatial stresses vanish under the Laue boundary hypotheses. Negative local ρ+Σp can be compensated by other apparatus stress; it does not give a negative exterior monopole on its own. Our symbolic two-sector algebra illustrates this NECESSARY condition; it does not construct a physically stable sourced GR solution.
For the P0.19 original *hypothetical* nonminimal F(O,B)R lane, the time-even quadratic |O|² is insensitive to O→−O, while O·B changes sign if only O changes at fixed B. Require real source field, F>0, full covariant tensor definition, true metric variation, energy positivity and measured coupling ξ/η before any metric claim.

## Endpoint 3: optional screened scalar-mediated rival, NOT automatically a metric
To **steelman an explicit additional force** rather than silently asserting negative mass, test a Yukawa potential V_extra=−G M_s m_t α_Y exp(−r/ℓ)/r. Then Δa_r=−G M_s α_Y exp(−r/ℓ)(1+r/ℓ)/r², and

  α_Y,required = −f g r² exp(r/ℓ) / [ G M_s (1+r/ℓ) ].

For a hypothetical M_s=70 kg, r=ℓ=1 m, α_Y≈−2.852866e9 for f=1, ≈−2.852866e7 for f=.01. In this convention, universal like-sign canonical scalar coupling α_Y≥0 gives attraction, not the required repulsion; a negative effective source×target charge or other nonstandard coupling must be derived and tested. This is an inverse target, not a physically healthy model found in PtMn3.
A *candidate* original-order-to-source weld is J_φ(x)=λ(O·B)(x), with separate positive-kinetic scalar φ and externally generated B, giving integrated Q_φ=λ I_OB where I_OB=∫_sample O·B d³x. For test charge/mass ratio α_t, acceleration aφ=−α_t Qφ exp(−r/ℓ)(1+r/ℓ)/(4πr²). Thus λ_required=−4π f g r² exp(r/ℓ)/[α_t I_OB(1+r/ℓ)]. Here **O is a chosen T1g axial cluster-order field, not identical to Sato–Hayami's full 18D bulk M_ijk**; I_OB and α_t are uncalibrated. At fixed B, reversing O flips charge; simultaneous T-reversal of O and B preserves O·B. A fifth force by itself is not a Riemann-curvature measurement.

## BIDI discriminators / identifiability
P0.25's original 3×3 load/gravimeter/pickup matrix is invertible only if exactly those **three** unknown effects are admitted. With both a metric effect and nonmetric fifth force, define x=(F_EM,a_metric,a_fifth,p_pickup). Under the stated hypothetical point-monopole/clock model, observables (load, remote, clock, pickup) use

  [[1,−m,−m,1],
   [0, 1, 1,k],
   [0,r/c²,0,0],
   [0,0,0,1]].

Determinant=−r/c²≠0. Without clock the 3×4 matrix has rank 3 with null direction (0,−1,+1,0): **metric vs fifth force indistinguishable**, even with a pickup monitor. The conditional fourth clock channel resolves this *linear* ambiguity, provided cross-sensitivities, clock references, EM/thermal shifts, finite source geometry and uncertainties are calibrated. Other unmodeled effects can restore degeneracy. Direct freefall of composition-different probes, source-reversal and inertial/momentum/phase tests remain separately required under the original six typed claims.

## Executable acceptance & actual status
A **full locally run, standalone, source-Pt-site energy and force** diagnostic passed **66/66 SymPy assertions** and emitted the locally supplied full receipt; source SHA-256=7f45c35085d171c03cba89f67478b259117c126ec1830c2deda23e8c0eff4025, Git source-blob hash 19a89ee235e6952e8aea702a21b4cd5b3507bde6. The full source is supplied as a conversation artifact, not yet committed as this PR's source blob. The GitHub **compact** same-target consumer \`scripts/check_oct369_p033_bidi_targets.py\` independently ran **23/23 exact SymPy checks**, committed exact source blob 94805b5bd4a05fee49d3913e60f0aa25dfac70cf. Do **not** misreport 66/66 as a run of the compact committed source. Agda/CI not used.
**Open physically:** actual PtMn3 source material and unit-calibrated 18D octupole, finite sample and realistic Maxwell field from coils/SC current, 6DOF stabilization and source reaction, full same-action T_munu with boundary stress, healthy scalar/metric action plus independent gravity, freefall and clock evidence. Neither lift nor altered gravity is demonstrated.


### Archival correction after P0.34 (2026-11-22)
The full P0.33 66-check diagnostic is now committed in PR #1534 as \`scripts/check_oct369_p033_steelman_lift_metric_bidi.py\`, Git blob 19a89ee235e6952e8aea702a21b4cd5b3507bde6, and original full acceptance receipt as \`Artifacts/oct369/p033_full_steelman_lift_metric_bidi_20261122.json\`, Git blob f58f5dda05073d33fbfa9205cad20f568c141ad6. This corrects the earlier statement above that it was not yet included. Independently replayed locally 66/66. This source is separate from the compact original P0.33 23-check consumer. P0.34's original Field Loom current-source simulation is a downstream, still-conditional physical-source extension, not an antigravity result.
