# Engineered gravity — whole-programme geometry-first closure campaign
**29 November 2026. Controlling recut; supplements and supersedes serial-only TOV priorities.**

## Executive outcome
**Nothing here establishes a physical antigravity device or a general stability theorem.** This roadmap resolves the campaign into finite, independently checkable *source-identical* proof edges. A construction of the desired inverse target by adjustable coefficients is NOT proof that any material/device realizes those coefficients. Symbolic source, physical source, full PDE, and native execution are separately payable obligations.

### Evidence authority and audited sources
Current checked PR heads at audit:
- [#1547](https://github.com/chboishabba/dashi_agda/pull/1547) head `277eb9f9cab0875f85361897002134ad8a9b3c9a` before this cut. Master comparison: master `c67d5d0e51f98d6171e77f440ddacc717a3201d8`, common ancestor `c36aa4a423091063bb3741cc74044726279b47c4`, 701 commits ahead and 65 behind, 300 returned filenames. This is **not** an exhaustive master signature audit or a recommendation to rebase a live branch.
- [#1554](https://github.com/chboishabba/dashi_agda/pull/1554) `d4f0f47b4180029a6c067ce6f0d5076666ecc0f8`: BR230/232/233 original G4 primitive/evolution, BR260/262 metric-jet correction, BR263/267 boundary/SBP/incoming, BR268/273 curved-frame stress and exterior-square inversion, BR273/276 Maxwell ADM and marked cube. Actual source bodies checked. The restricted or incoming full-grid traces **do not** constitute an independent physical causal exterior.
- [#1537](https://github.com/chboishabba/dashi_agda/pull/1537) `e5658091ce9a70ded26207ec15459482f3617388`: original field/source boundary and conservation owner; metadata, not a fresh exhaustive source replay this cut.
- [#1555](https://github.com/chboishabba/dashi_agda/pull/1555) `be212eec07c0475117c8985f08fdd7a21e4907e7`: original MHD source owner; do not fabricate full Maxwell stress or calibration.
- [#1527](https://github.com/chboishabba/dashi_agda/pull/1527) `d19a9525968ec2fee92a6e3f73027df05396d497`: F8 full nonlinear source donor; not identical to TOV or G3.
- [#1291](https://github.com/chboishabba/dashi_agda/pull/1291) `c68b44f37c89b54d9ba0b5ef18ab4753c7dd5f04`: indexed composition and non-promotion. Very large changed-file inventory can be capped; do not claim absence from capped lists.
- Master literal bodies checked: `check_kk_same_action_stress.py` blob `edeaa4fe11313ad0611cb741883366f0ffa902c3` (actual action, Ward and switching work); `check_kk_casimir_bidi_consumer.py` `d997847e2206f1f84a4be522369c8ff8f49e4897` (conditional stabilized radion + graviphoton/Maxwell distinction); `check_oct369_p024_dynamic_controller_ward.py` `c83dfb76bb5b3a2bb791c34ea87875ffa00d2e63` (dynamical controller exchange).
- #1547 selected bodies checked: original TOV second shape and two-face canonical momentum, original nonlinear reciprocal shell, G3 harmonic receiver, F8 quadratic Einstein and original same-clock sidecar. Full native artifacts are not locally present.

## Shared terminal contract and proof objects
**S0 source:** original single action, admitted state, stress and exchange Ward, geometry, unit scale, attribution and source identity. No independently fitted `T_{ab}` and receiver map.
**S1 constraints:** Hamiltonian/momentum/Gauss plus gauge/embedding; compatible initial and interface jets; York/Schur solve with the *same* action.
**S2 boundary:** actual normals, two-sided induced metric, full Israel/GHY/corner, supported controller and exterior resolvent or causal boundary data. Trace must be controlled in the **correct graph domain**, not an unavailable bulk form norm.
**S3 evolution:** regularity, subsidiary constraints, positivity or actual counterexample, nonzero source, signed energy/entropy, stability/continuation, causal support, dynamic interface.
**S4 receiver:** identified same-event congruence/clock; proper support acceleration vs neutral free-fall vs tidal/clock shift and pickup; use signed observer data, including what remains unchanged.
**S5 acceptance:** original native history, source hashes, independent continuum/interval/no-go witnesses, empirical source and calibration where necessary. A source file without a run is not a receipt; a finite run is not a continuum theorem.

Each candidate is a row of an **inverse/forward commuting square**:
`physical source -> field/evolution -> (source-ID, receiver-ID, signed observation)` versus `desired observation -> admissible inverse -> physical source`. Require both paths return the same source object, boundary/clock, units and signed output. If image of forward map excludes target, emit a left-null or energy witness; do NOT change target or invent a gain.

## Executable dependency ledger
- `Artifacts/engineered-gravity/engineered_gravity_dependency_manifest_20261129.json` enumerates twelve lanes, original local owners, **36 named unpaid obligations**, stage lists, and overlapping owner interfaces. External PR donors are separate and must not be misreported as present on #1547.
- `scripts/check_engineered_gravity_proof_dag.py` validates paths/lanes/stages and emits source hashes or `MISSING` with a nonzero exit; `--execute --repo REPO --owner scripts/owner.py` performs one explicitly selected **original** checker with a 90s cap, retaining exit and source/output hashes.
- `scripts/test_engineered_gravity_proof_dag.py` provides exact manifest admission and missing-source/non-promotion negative controls.
- Default `python scripts/check_engineered_gravity_proof_dag.py` is inventory-only; success means valid bookkeeping, **not lane proof**. Reproducible local source-equivalent Python executed 12/12 lane schema and 4/4 malformed-claim controls. Full repo owner replay outstanding.

## Cross-lane geometric welds to reuse rather than re-derive

| Weld | Actual constructor | Consumers and exact unpaid step |
|---|---|---|
| Covariant source Ward | master `check_kk_same_action_stress.py`; OCT369 P024 | A/C/E/F/I: replace abstract (J,K) with original microscopic measured source/drive/support and actual metric variation |
| Reciprocal static transfer | `check_engineered_gravity_reciprocal_action_shell.py`; compliant nonlinear shell | A/I: same-action physical susceptibility, exterior Earth source, branch enclosure, tensor gravitational leakage |
| Admissible radion stabilization | master `check_kk_casimir_bidi_consumer.py`; `check_kk_radion_spherical_match.py` | C: full quantum source/earth boundary/stress, not merely example one-loop vacuum |
| Matter/Einstein local Hessian | `check_tov_covariant_matter_hessian.py`, `check_tov_einstein_harmonic_jets.py` | D/G/J: full constrained polar free metric, weighted moving surface and EH+GHY/corners, not two-parameter positive Ritz |
| Global York, ADM inverse | `check_tov_global_york_axial_shear.py`, `check_tov_conformal_monopole_inverse.py` | D/G4: compatible full nonlinear source and free conformal metric, generated monopole and dynamical boundary |
| Two-face action/current | `check_tov_two_face_canonical_second.py`, `check_f8_two_level_israel_trace_closure.py` | D/G/J: actual coupled second order boundary jets and correct energy normal |
| Curved/incoming energy | #1554 BR263/267, BR273 Maxwell ADM | B/G/J/G3/G4: source-identical physical boundary plus interface geometry; no surrogate zero-extension |
| Original F8 native same-clock | `run_f8_p0_integrated_local.py`, `check_f8_p0_original_same_clock_state.py` | J: original checkpoint with instrumented t12 sidecar and 96 signed outputs; do not relabel terminal lookahead |
| G3 invariant observer | `check_engineered_gravity_g3_harmonic_receiver.py` | B/G3: compatible original harmonic constraints and same-event physical causal domain |
| G4 material primitive | #1554 BR230/233 and BR269 | G4: physical York data and fully coupled Einstein–RMHD, not just fixed-metric primitive parity |

## Concrete exact remaining lemmas/welds by lane
**A:** A1 true matter Hamiltonian -> gauge-covariant (J^mu,T_{mu
u}), A2 physical scalar/tensor interface with Earth incident mode and neutral body, A3 calibrated same-apparatus signed 1g inverse and energy/viability. Existing reciprocal transfer and scalar-only 25% conditional ceiling remain scoped, not universal.
**B:** B1 original time-dependent same-event KK/base cone comparison and closed fibre winding, B2 actual source/retarded geodesic with exterior physical boundary, B3 receiver proper-time and finite-aperture/energy convergence. Frozen G3 path cannot be paid as evolved causal shortcut.
**C:** C1 consistent radion EFT source and stabilization, C2 finite Earth/material profile and tensor+scalar Einstein response, C3 fifth-force bounds, source mass/energy and independent clock/tide.
**D:** D1 original full polar/axial constrained free metric and material Hessian in physical weighted graph domain, D2 actual second-order Einstein bulk/interface solution with original surface source and GHY/corner, D3 nonlinear branch/energy sign + independently reconstructed receiver. A positive selected Ritz is not a spectral gap.
**E:** E1 microscopic OCT/SC Hamiltonian same state/stress/EM current, E2 actual controller+Maxwell+metric signed work, E3 reaction and independent gravimetric null calibrated to external source.
**F:** F1 original Maxwell/MHD apparatus work and full (T), F2 retarded second-order Einstein metric static/radiative projection, F3 independent neutral receiver with same drive.
**G:** G1 physical moving Israel boundary source and metric-compatible chart, G2 curved differentiated incoming boundary energy and corner, G3 globally matched stress + invariant receiver and viability.
**H:** H1 complete apparatus force/reaction/support and heat, H2 independent neutral free-fall/clock/tide, H3 uncertainty/force vs gravity rejection.
**I:** I1 same controller/orientation physical action, I2 coercive nonlinear source branch with independently enclosed error, I3 actual Einstein response/support stress and signed total work.
**J:** J1 original hash-pinned native A0/A1/C0/C1 same-clock history, J2 original quadratic Einstein scalar/vector/TT and moving Israel, J3 receiver 96 signed outputs, causal-null and independent continuum. No generic positive socket.
**G3:** G3.1 constraints and physical outer domain, G3.2 harmonic reduced->full Einstein subsidiary propagation, G3.3 invariant same-event receiver/independent convergence.
**G4:** G4.1 actual matter/metric constraint-compatible York initial slice, G4.2 nonlinear coupled Einstein-RMHD flux/entropy/subsidiary evolution, G4.3 invariant receiver and certified convergence.

## New original TOV second-order boundary Cauchy inverse (direct implementation)
`scripts/check_tov_second_order_junction_inverse.py` uses original
(f=1-lambda(2+lambda)(r^2/3-r^4/5)),
(F=1-2M/r), (M=lambda(lambda+2)/15),
(n=rlambda P/f), (n_{mathrm{ext}}=M/(r^2F)).
For either (D=f-F) or (D=n-n_{mathrm{ext}}), background (D(1)=D'(1)=0), (D''(1)\ne0).
Writing physical metric first and second **jump functions** as (a(r),b(r)), the common moved radius (r_b=1+arepsilonphi+arepsilon^2psi/2) gives
[
 [q]^{(1)}=a(1),\quad [q]^{(2)}=b(1)+2phi a'(1)+phi^2 D''(1).
]
For the radial derivative,
[
 [q_r]^{(1)}=a'(1)+phi D''(1),\quad
 [q_r]^{(2)}=b'(1)+2phi a''(1)+phi^2D'''(1)+psi D''(1).
]
Consequently first value and normal matching require (a(1)=0), (a'(1)=-phi D''(1)). **Second value matching then REQUIRES** (b(1)=+phi^2D''(1)); second normal matching REQUIRES
(b'(1)=-2phi a''(1)-phi^2D'''(1)-psi D''(1)).
These are *genuinely forced boundary Cauchy data* in the selected common-coordinate radial derivative model, not solved bulk fields or automatic Israel matching. For `f`, (D''(1)=2lambda(lambda+2)), (D'''(1)=4lambda(lambda+2)). For (n), the actual rational original expressions are evaluated exactly.
Local SymPy execution of equivalent implementation passed. **Do not misidentify common-coordinate radial derivatives with the full physical second fundamental form**; finish the normal/embedding transformation, source mass and stress constraints, GHY/corners. No direct proof of existence.

### Coarse-to-fine roadmapped implementation order
**Cut W0 (this commit):** exact audit / named lane dependency DAG and necessary original TOV second Cauchy data, local symbolic gates + negative controls.
**Cut W1 (joint):** source-identity boundary ABI: compile E0 original (T,J,gamma,K) from each owner, verify 2-face action and Ward with changed boundary; prove/obstruct original free-metric and support terms; attach #1554 BR266/267 only in matching geometry.
**Cut W2 (joint):** source-admissible constrained York initial data for D/J/G3/G4 and A/I scalar–tensor physical shell; include independent metric & material variations, physical source equations.
**Cut W3 (joint):** nonzero coupled evolution (G3/G4/F8 + scalar shell), constrained boundary energy and receiver signatures with same clock/normal, certified residual & provenance.
**Cut W4 (joint):** reverse target 1g/shielding/shortcut/repulsion against feasible source states and real finite budgets; emit theorem or exact no-go, not imposed target. Independent physical measurements and bounds are not replaceable by SymPy.

## Execution / acceptance
Run locally on a full literal checkout, no CI:
`python scripts/test_engineered_gravity_proof_dag.py`;
`python scripts/check_engineered_gravity_proof_dag.py --repo . --output .local-engineered-gravity/proof-dag.json`;
`python scripts/check_tov_second_order_junction_inverse.py`;
`python scripts/run_engineered_gravity_endpoint_local.py --timeout 90 --resume`.
Original F8 native run remains separately hash-pinned and must use actual instrumented same-time sidecar. The manifest's `INVENTORY_ONLY` is **not PASS of the 12 lanes**. Missing source returns BLOCKED. Local repository clone unavailable here (DNS), so literal committed-source replay and aggregate/native acceptance remain OPEN. No source/boundary assertion promoted by unexecuted code.


## W1 partial implementation — Einstein mass constraint pays the wall source (same cut)
New `scripts/check_tov_moving_mass_constraint_weld.py` (original covariant source, no fabricated interior matter): for (m'(r)=4\pi r^2\rho(r)), original (\rho=(2+\lambda)\lambda(1-r^2)/(8\pi)), (m_0(1)=M), (m_0'(1)=0), (m_0''(1)=-\lambda(\lambda+2)). The moving material level-set density (\rho(1+\varepsilon\phi+\varepsilon^2\psi/2;\varepsilon)=0) requires
[
\rho_1(1)=\frac{\lambda(\lambda+2)}{4\pi}\phi,\quad
\rho_2(1)=-2\phi\rho_1'(1)+\frac{\lambda(\lambda+2)}{4\pi}(\phi^2+\psi).
]
Hence the **actual first Einstein mass constraint** pays (m_1'(1)=\lambda(\lambda+2)\phi=-\phi m_0''(1)), not a free junction assumption. Exact same moved-face mass continuity then forces
[
m_1(1)=0,\qquad m_2(1)=-\lambda(\lambda+2)\phi^2.
]
For (f=1-2m/r), (f_2(1)=2\lambda(\lambda+2)\phi^2), precisely the necessary metric second-value correction found in `check_tov_second_order_junction_inverse.py`. This is an **actual spherical Einstein source-to-geometric-junction weld**, not simply a prescribed surface metric. The second derivative of the density and the second Einstein mass constraint are retained; physical second lapse derivative, dynamic metric and material evolution, full nonspherical polar/axial extension, common embedding/normal and GHY/corner remain OPEN. Source-equivalent local SymPy execution exited zero under 90s, then file committed as `4ae76b832e07d4240c4f12eb7dcc881820c61423`, integrated runner `44b392e44a26afb8478913661bafc1aa664b8c1c`. Literal committed source replay remains unexecuted. This narrows **D S1/S2** but does not close the physical D receiver or the other 11 lanes.

**Mass-jump scope clarification:** Here \(m_1,m_2\) are the *interior-minus-exterior* perturbation jets. A common exterior ADM mass perturbation is permitted; only its radial derivative vanishes in vacuum. The derived wall constraints pay the **jump**, not the unknown total ADM mass or bulk evolution. Do not set the entire exterior ADM perturbation to zero by this ledger.\n

## W1 integrated action-to-boundary ABI (29 Nov, second construction cut)

**Source reconciliation:** #1547 started this cut at `3a87af1f5113321b8a73985447094538abc41157`; #1554 `8fa26fe7790b8e70712f7b7433874a26bd76517c`; #1537 `95f30beee111e076f224a0be3043913e6682b883`; #1555 `be212eec07c0475117c8985f08fdd7a21e4907e7`. This is current PR metadata, not new exhaustive source-body audits of those donors. Reused existing original action: `check_engineered_gravity_tov_material.py`, `check_tov_moving_mass_constraint_weld.py`, `check_tov_second_israel_shape.py`, `check_engineered_gravity_reciprocal_action_shell.py`, master `check_kk_same_action_stress.py`, original `check_f8_current_israel_reciprocal_weld.py`, `check_engineered_gravity_g3_harmonic_receiver.py` and #1554 BR268/273 curved G4 primitive source. **No substitution of a 5D theorem for 4D Einstein boundary data.**

### W1-TOV: mass and traction already suffice for spherical Israel matching
The genuinely original spherical static/polar-areal Einstein constraint and constitutive surface give
\[
f=1-2m/r,\qquad
\nu'=(m+4\pi r^3p_r)/(r^2 f).
\]
At the same radius on the two faces, if the mass agrees and the interior radial traction is zero, the lapse gradient agrees **identically**, not merely to second order. Consequently `K^theta_theta=sqrt(f)/r` and `K^tau_tau=sqrt(f)nu'` agree. Conversely, on timelike nondegenerate static charts, equality of these eigenvalues forces the mass and radial traction conditions. Thus the spherical lapse-gradient/Israel *value* is not an independent datum; the bulk mass constraint and material traction pay it. New `scripts/check_tov_spherical_source_israel_abi.py`, committed `e12943f41008bfe1b174f767d02764530f28d707` and tested as source-equivalent local SymPy PASS. Separate dynamic wall velocities, normal acceleration, source evolution, moving induced-metric and full nonspherical Israel/GHY/corner remain.

Second moving-wall traction obstruction: with original `p_r=-p(1-r²)²`, `p_r(1)=p_r'(1)=0`, `p_r''(1)=-8p`. Expanding a wall `R=1+epsilon phi+epsilon² psi/2` and a genuinely varying source `p_r=p_{r0}+epsilon p_{r1}+epsilon²p_{r2}/2`, traction-free level set requires `p_{r1}(1)=0` and `p_{r2}(1)=-2phi p_{r1}'(1)+8p phi²`. This is **new second-order source boundary Cauchy data**, not an independent prescribed Israel source. Together with original Einstein mass-jump equation it closes the spherical static boundary *algebra*, not the physical second-order bulk.

### W1-reciprocal controller: no free reaction term
Reusing the **original** reciprocal two-channel `G(X)=[[1,-X],[-X,1+X²]]`, `det G=1`, static radial source flux (q=r²G(X)u') is conserved on shell interiors. The complete action-derived radial stress/traction is
\[
T_{rr}=\tfrac12u'^T G u'=\frac{q_1^2+(q_2+Xq_1)^2}{2r^4}.
\]
With (F_X=\frac12u'^T G_Xu'), exact signed exchange identity:
\[
T_{rr}'+\frac4r T_{rr}+F_X X'=0,\qquad F_X=-\frac{q_1(q_2+Xq_1)}{r^4}.
\]
Hence `-F_X X'` is the actual controller reaction/work in this radial geometry; it cannot be omitted while promising reciprocal field transfer. `scripts/check_engineered_gravity_reciprocal_controller_ward.py` committed `6c4b07ec75a2bf99cb36f3bb213aa258298f3040`, corrected fixed-flux-versus-fixed-gradient sign `6d51f3e459ed35db665f514dd6c7334cd39ebb03`; source-equivalent local SymPy exit0. Nonzero reaction negative control tested. This **does not** provide physical material G(X), controlled rest profile, self-gravity or a neutral receiving experiment. Pays exact static mathematical exchange for A/I, not viability.

### W1-Maxwell source work and two-face sign
One-polarization exact Maxwell pair `E_t=-B_x-J`, `B_t=-E_x` obeys
\[
\partial_t\tfrac12(E^2+B^2)+\partial_x(EB)=-JE.
\]
The source work term is unavoidable. `scripts/check_engineered_gravity_maxwell_source_work_abi.py` committed `3e4e52b03b109b03b00f8e34d68accd384d1ae14`; symbolic independent worldtube integration was not computable for uninterpreted functions by SymPy and replaced by an exact polynomial boundary fixture at `21e911c16a584368067d7a4177163f3998812971`, retaining the **general local differential identity**. Source-equivalent local SymPy exit0 with omitted-work negative control. This applies to an independent Maxwell source-work contract, not yet to any specific F8/MHD/scalar controller device. Uses E/F/H/G4 as consumers of a reusable *interface*, not asserted common physical source.

### Existing donors retained: no reinvention, no source identification by analogy
F8 original current/Israel identity: `check_f8_current_israel_reciprocal_weld.py` and original full pair source; stage J still needs actual same-clock native receiver and second-order moving trace. G3 harmonic receiver: `check_engineered_gravity_g3_harmonic_receiver.py` requires subsidiary constraints/causal boundary. G4 curved-frame primitive from #1554 `check_hopf369_br268_273_endpoint.py` is **external**; do not run it through #1547 without fetching exact donor and dependencies. KK/dynamical scalar Ward donors on master prove effective model exchange only and require physical action admission. These three contracts are manifest entries with physical_paid=false.

### W1 checked dependency interface
Added six explicit entries in `Artifacts/engineered-gravity/engineered_gravity_dependency_manifest_20261129.json`: TOV mass/traction->Israel (D), reciprocal static controller (A/I), Maxwell sourced work (E/F/H/G4), F8 Israel flux (J), G3 harmonic receiver (B/G3), curved-frame primitive (G4 external donor). Each names original source_owner, mathematical checker, consumer lane(s), scope, and remains `physical_paid=false`. `scripts/check_engineered_gravity_proof_dag.py` now validates W1 source and checker owner paths, lane membership, provenance and refuses any unearned physical promotion. A repo-backed audit is BLOCKED if an owner/checker is missing; explicit external PR checkers are not claimed present. `scripts/test_engineered_gravity_proof_dag.py` now rejects six malformed/promotion controls (prior four, plus fake physical paid and unknown W1 consumer). The 36 earlier physical unpaid obligations remain 36: these are **separate mathematical identities**, not payments for the full stage.

The native checkpointed `scripts/run_engineered_gravity_endpoint_local.py` now includes all three W1 mathematical checkers and existing W0 mass/junction + DAG gate. Use `--only check_tov_spherical_source_israel_abi.py --only check_engineered_gravity_reciprocal_controller_ward.py --only check_engineered_gravity_maxwell_source_work_abi.py` for fast targeted replay, or full 90s checkpointed run.

### Actual W1 execution and remaining proof cuts
Source-equivalent local Python/SymPy executions: **3/3 mathematical checkers exit0**, each within 90 seconds. Reciprocal first draft's expected (F_X) sign failed and was **corrected**; Maxwell arbitrary-function definite integral was **replaced by an exact polynomial endpoint fixture**. No receipt of literal committed-source replay or complete W1 ledger test asserted; all new files committed and fetched SHA checked at end. No CI, native F8 or physical result.

W2 **coarse whole-system**: produce lane-identical `BoundaryJet{source,metric,normal,clock,traction,work}` witnesses for A/I, C/E/F, D/G/J, G3/G4, with actual original owner provenance and *commuting source and boundary* maps. Where material/current data are unavailable, construct explicit incompatibility/source-admissibility theorem rather than a guessed field. For D, calculate real moving wall acceleration and metric second variation from the coupled Einstein equations, attach GHY/corners and graph-domain trace; for A/I, solve finite material controller and support reaction from same action; for F/G4, use original full 3+1 Maxwell/RMHD source and physical boundary with BR273 donor. W3: source-driven actual coupled evolution, same-event independent receivers and original native certificates; W4: physically calibrated 1g and energy viability or exact no-go witness. None of these has been paid by W1 alone.


### W1 acceptance/custody reconciliation
Final source ownership correction: W1 Maxwell mathematical J is an **independently specified** current, not the 5D/KK scalar source, original F8 triad source or actual G4 MHD apparatus. In the manifest w1_source_boundary_welds.maxwell_source_work, source_owner now refers to its actual Maxwell Ward fixture, and physical_source_owner=null remains **unpaid** (commit 78d3a8a50bbbc634418e7aef673610c14b2e1e9c). Consumers E/F/H/G4 can reuse the Ward identity without identifying distinct physical sources.

W1 local acceptance receipt: Artifacts/engineered-gravity/w1_source_boundary_local_receipt_20261129.json committed, including SHA256 of source-equivalent local implementations and stdout, correction provenance, 12-lane inventory, 36 unclosed obligations and six rejected malformed/promotion controls. Three sourced mathematical contracts PASS; locally adapted W1 manifest negative controls PASS. This is **not** literal GitHub committed-source replay. No native F8 receipt, no original apparatus/current calibration and no continuum/full causal geometry proof. Checkpointed runner registered all W1 checkers.

**W2 immediate integration priorities (shared):** (i) replace abstract mathematical Maxwell J and reciprocal G(X) with exact original physical matter/current action or return source-admissibility NO-GO; (ii) construct one common spherical TOV boundary packet of mass, radial traction, induced metric, normal and canonical momentum plus moving acceleration and GHY/corners; (iii) compile equivalent typed packets from F8, G3 and G4 owners without identifying their distinct geometries; (iv) reverse-solve every packet into same-event neutral/support/tidal receiver; (v) independent physical/native acceptance. These are coordinated multi-lane cuts, not another serial search of selected positive polar Ritz eigenvalues.
