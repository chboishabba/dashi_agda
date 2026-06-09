# ns_sprint135_hou_luo_blowup_gate_classifier

- route: `HouLuoAxisymmetricNSRoute`
- route_status: `open_live_candidate`
- gate_count: `21`
- blowup_path_closed: `False`
- regularity_path_closed: `False`
- full_clay_ns_solved: `False`
- clay_navier_stokes_promoted: `False`

## Corrected Sprint 134 Assumptions

- `u1_pure_diffusion_retracted`: `True`
- `gamma_is_maximum_principle_variable`: `True`
- `uniform_no_log_biot_savart_false`: `True`
- `hou_luo_axisymmetric_ns_route_open_live_candidate`: `True`

## Gates

| gate | path | status | objective | missing evidence |
|---|---|---|---|---|
| LogLossSourceLowerBound | blowup | open | Turn the corrected logarithmic Biot-Savart loss from a loose upper-growth risk into a PDE lower bound for source growth. | lower-bound sign control; localized kernel positivity or monotone compression estimate; non-cancellation of log-enhanced source |
| SourceVorticityMaxAlignment | blowup | open | Show the positive source maximum and the omega1 maximum remain sufficiently co-located along the candidate singular trajectory. | maximum-point tracking lemma; source-vorticity phase-locking estimate; control of adverse axial sign changes |
| AnnularGammaToU1Persistence | blowup | open | Construct or prove persistence of a boundary-annulus swirl profile whose u1 amplitude does not collapse before the candidate blowup time. | lower persistence, not merely upper boundedness; annular support confinement; control of Gamma transport away from the boundary layer |
| ViscousDampingNonDominance | blowup | open | Show viscosity does not dominate the corrected source before BKM divergence in the live Hou-Luo geometry. | signed viscous/source comparison; profile curvature control; localized lower inequality robust under diffusion |
| SelfSimilarScalingClosure | blowup | open | Close a finite-dimensional or PDE self-similar scaling system whose exponents and profiles satisfy the corrected equations. | consistent exponent/log-modulation algebra; profile compactness or stability; boundary compatibility |
| SmoothFiniteEnergyInitialDataConstruction | blowup | open | Construct initial data that enters the closed Hou-Luo amplification regime while satisfying all regularity, boundary, symmetry, and energy constraints. | compatible divergence-free reconstruction; finite-energy annular profile realization; bootstrap-entry proof |
| BKMIntegralDivergenceVerification | blowup | open | Convert the closed source/scaling/data bootstrap into integral divergence of ||omega(t)||_infty before or at T*. | sharp lower growth rate for Omega; continuation-to-singularity argument; exclusion of norm inflation without BKM divergence |
| LogLossSourceUpperControl | regularity_alternative | open | Prove a non-circular upper control showing the log-loss Gronwall hazard cannot be saturated by smooth finite-energy axisymmetric-with-swirl solutions. | energy-to-source continuation estimate; non-saturation of logarithmic Biot-Savart bound |
| SourceVorticityMaxDecorrelation | regularity_alternative | open | Show source peaks and vorticity maxima cannot remain aligned strongly enough to force BKM divergence. | axisymmetric maximum-principle geometry for omega1; source sign cancellation estimate |
| AnnularGammaLeakageOrDiffusiveDecay | regularity_alternative | open | Prove that active annular u1 amplitude either leaks away from the Hou-Luo source region or decays under diffusion/transport. | lower-amplitude decay mechanism; annular transport leakage estimate |
| ViscousDampingEventualDominance | regularity_alternative | open | Recover an eventual viscous dominance theorem under corrected source-gradient and log Biot-Savart accounting. | log-aware localized parabolic comparison; large-Re transient exclusion |
| SelfSimilarScalingExclusion | regularity_alternative | open | Prove no corrected Hou-Luo scaling profile satisfies the axisymmetric PDE, boundary compatibility, energy, Gamma, and BKM constraints. | profile Liouville theorem; corrected exponent feasibility audit |
| AxisymmetricContinuationCriterionFromCorrectedVariables | regularity_alternative | open | Assemble a continuation criterion for axisymmetric NS with swirl that follows from corrected-variable estimates rather than assuming Serrin/BKM control. | non-circular continuation norm; axisymmetric class exhaustion after corrected equations |
| corrected_axisymmetric_equations | taxonomy | open | Corrected axisymmetric equations are the baseline gate for every post-retraction Hou-Luo argument. | concrete PDE estimate; closed bootstrap or exclusion argument |
| swirl_circulation_maximum_principle | taxonomy | open | Gamma, not u1, supplies the corrected maximum-principle control. | concrete PDE estimate; closed bootstrap or exclusion argument |
| boundary_annulus_u1_bound | taxonomy | open | Gamma control must be converted to u1 only on r >= r0 annuli. | concrete PDE estimate; closed bootstrap or exclusion argument |
| log_biot_savart_growth | taxonomy | open | The restored logarithmic Biot-Savart loss is the live source-growth hazard. | concrete PDE estimate; closed bootstrap or exclusion argument |
| source_vs_viscosity_model | taxonomy | open | The source/viscosity phase map separates polynomial and log-Gronwall regimes. | concrete PDE estimate; closed bootstrap or exclusion argument |
| large_re_transient_control | taxonomy | open | Large-Re transient growth remains an open Hou-Luo gate. | concrete PDE estimate; closed bootstrap or exclusion argument |
| marginal_beta_zero_case | taxonomy | open | The beta=0 boundary case remains separate from beta>0 concentration. | concrete PDE estimate; closed bootstrap or exclusion argument |
| bkm_blowup_alignment | taxonomy | open | A Clay-relevant blowup proof still needs source alignment and BKM divergence. | concrete PDE estimate; closed bootstrap or exclusion argument |
