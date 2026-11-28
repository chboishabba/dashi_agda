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


### W1 exact source-custody acceptance addendum
The six source-to-boundary welds now pin BOTH mathematical owner and checker by their **actual Git blob SHA-1**; the external Hopf G4 checker also pins its donor PR HEAD. The DAG verifier computes `SHA1('blob '+decimal-byte-count+NUL+raw-source-bytes)` and blocks absent, substituted or outdated source files in repo-backed mode; external donor checks are explicitly not treated as present. The W1 negative-control suite now has seven rejection fixtures, including false physical promotion, unknown consumer, malformed SHA and source substitution. Source-equivalent local tests PASS and a separate Git blob NUL hashing check matched `git hash-object`. The receipt `Artifacts/engineered-gravity/w1_source_boundary_local_receipt_20261129.json` was updated accordingly. **No literal committed-source or aggregate runner replay** was available in this environment, no CI and no native F8. Updating a source requires an explicit audited manifest repin; pin agreement does not establish a physical theorem.


## W2 action-derived reciprocal material-interface traction / admission (29 Nov)
The original reciprocal two-channel action G(X) was reopened. This cut uses the SAME conserved radial flux Q=r² G(X)u' and its exact scalar stress, not a new support-field invention. The radial traction is Trr(X)=[q1²+(q2+X q1)²]/(2 r⁴), so the two-face jump is EXACTLY

`[Trr] = q1*(X_plus-X_minus)*(2*q2+q1*(X_plus+X_minus))/(2*r**4)`.

A static thin interface requires an opposing controller/sheet traction `- [Trr]` (or an explicitly provided additional source). If the interface is moving at speed v, the corresponding signed normal power has factor v; physical elasticity and work are still unpaid. The **no-support obstruction is conditional**, not universal: the jump vanishes if q1=0, X_plus=X_minus, or 2q2+q1(X_plus+X_minus)=0. In particular X_minus=-X_plus and q2=0 is a balanced sign-reversal exception, whereas pure channel-one q2=0 with X_minus=0 and nonzero q1 forces X_plus=0 for zero support. These exceptions must be preserved under steelman/bidirectional source solving.

New `scripts/check_engineered_gravity_reciprocal_interface_traction.py` commit `08f997f59a89eaf7a9d076f7debd8188da456607`, source-equivalent local SymPy timeout90 PASS including reciprocal flux matching, exact jump, nonzero force sample and all balanced exceptions. Registered in checkpointed runner at `cc8d35703877eb91e1a90f88e65c07908d06e2e0`, pinned in W1/W2 mathematical ABI as seventh weld in manifest at `5858a3cafd11e156c2d53e72dd2d61358e2eefcf`. Source SHA custody verifies only a mathematical original G(X) constructor. The physical support material, nonlinear controller evolution, self-gravity and neutral receiver remain OPEN. This pays a specific A/I **S2 necessary source/support relation**, not whole A/I S2 or physical 1g success.

**Next coordinated W2 bridge:** apply the same two-face packet to the TOV physical moving normal/GHY Einstein junction and to the original Maxwell/MHD apparatus work, retaining distinct geometries; use the shared negative-control framework to reject unsupported free-wall or no-recoil stories. Original F8/G3/G4 native producer histories and source-verified causal same-event outputs are still unpaid. Existing 36 primary physical obligations unchanged.


**W1 signed-domain correction:** The TOV source/Israel checker now treats radial pressure p_r as REAL, including the original negative radial tension, rather than assuming p_r>0. Exact SymPy source-equivalent replay still PASS. The manifest checker Git blob is deliberately re-pinned at `5f577ec1fc071edc37b1195c91a49ad09954d755`, commit `d9004d64d9c880359ec49a8ea2ce7ec15a1bd312`. The time-independent spherical mass/traction identity is valid algebraically for either pressure sign in its nondegenerate domain. No unsupported energy-condition claim was introduced.


## W2 source-to-boundary normal and reverse observable cut — 29 November

### Reconciled actual heads and owners
At this cut #1547 started at 207f7e5f0f6e5675f80c26cb2bfe4a57dd9b736a; #1554 donor 151a121e6c79cb838c9869101772ea3ba7fb1f0b; #1537 d9f568df8bffbb848e085186c416a881d6748433; #1555 be212eec07c0475117c8985f08fdd7a21e4907e7. TOV original pressure/source/mass, reciprocal G(X) and independent Maxwell work source were reopened on #1547. No exhaustive latest master / remote donor compilation claimed.

### New exact moving **timelike** normal and Israel weld: source to geometry
Committed \`scripts/check_tov_moving_timelike_israel_abi.py\` at 2f189c073678457a0af76beaa23dfbfde378005d. In each **static polar-areal** geometry \`ds²=-N(r)²dt²+dr²/f(r)+r²dΩ²\`, with the same radius \`r=R(τ)\`, wall proper velocity \`v=dR/dτ\` and acceleration \`a=d²R/dτ²\`, future timelike shell:
\[
U^t = {\sqrt{f+v^2}\over N\sqrt f},\quad
n_t=-Nv/\sqrt f,\quad n_r=\sqrt{f+v^2}/f.
\]
Directly derived (rather than prescribed) the exact principal curvatures for the same oriented unit normal:
\[
K^\theta{}_\theta = {\sqrt{f+v^2}\over R},\qquad
K^\tau{}_\tau =
{a+(f+v^2)(N'/N)-(f'/2f)v^2\over\sqrt{f+v^2}}.
\]
The original spherical Einstein source identities are \`f=1-2m/r\`, \`f'=2m/r²-8πrρ\`, \`N'/N=(m+4πr³ p_r)/(r²f)\`; the exterior is Schwarzschild with the **same enclosed mass at the wall** and vacuum \`ρ=p_r=0\`. Their temporal Israel jump reduces *exactly* to
\[
\boxed{
[K^\tau{}_\tau] =
{4\pi R\big[(f+v^2)p_r+v^2\rho\big]\over
 f\sqrt{f+v^2}}.}
\]
The angular jump is zero when the same wall mass and proper velocity are used. **Reverse solve:** zero surface stress/Israel temporal jump requires
\[
\boxed{p_r=-{v^2\over f+v^2}\rho.}
\]
For the original TOV level surface \`R=1\`, both \`ρ(1)=0\` and \`p_r(1)=0\`; hence the moving wall has zero jump for any common \`v,a\` when comparing the original static field continuations evaluated there. Off the matter level set, pressure or density alone generally leaves a nonzero jump; this is now an independently executed negative control. No proof of an actual dynamical Einstein–matter spacetime, no \`g_tr\`/time-jet terms, no full GHY/corner, no nonlinear free-boundary existence, and no physical nonzero-v trajectory is asserted. The earlier stationary source/traction construction is strictly subsumed only within this static-background moving-worldtube geometry.

Local exact Python/SymPy exit0 under 90s; locally executed Git blob \`16ce2ab9c3f903974a9bf4bdff181a04bacc484c\` independently verified against committed GitHub blob of same SHA. Thus this W2 script **was** literally executed byte-for-byte, unlike the older W0/W1 claims. This does **not** imply a full aggregate/native run.

### Three separate source-specific forward/reverse boundary packets and rank obstructions
Committed \`scripts/check_engineered_gravity_boundary_packet_w2.py\` at 905f25de5fd2c83799234d3e7f624870e999080a; local Git blob \`ffc4b7dc9d5ee0b21f763b4aff816180342bef4c\` equals committed blob, local Python/SymPy exit0 under 90s. The immutable typed boundary records explicitly distinguish **original Einstein TOV** (4D polar-areal, wall proper clock), **original static reciprocal comparator** (4D flat radial and signed material sheet), and **mathematical Maxwell J** (1+1 dynamic sector in 4D Minkowski, coordinate clock). Never conflate their metrics, normal types, sources or receivers.

1. **TOV two-way mass and stress observer:** knowing the moving angular extrinsic curvature \`Kθ\` and common wall velocity gives \`f=(R Kθ)²-v²\`, \`m=R(1-f)/2\`. Temporal \`Kτ\` then fixes exactly ONE linear combination of \`p_r,ρ\`, not both. The source invisibility direction at fixed \`m,v\` is \`δp_r=-v² δρ/(f+v²)\`; at \`v=0\`, surface density is not identified by \`Kτ\` at all. If the *same stationary material source* can be independently sampled at two unequal squared velocities \`u1,u2\`, the coefficient matrix for \`(p_r,ρ)\` has determinant \`f(u2-u1)\`, admitting a unique inverse; physical repeatability of the same source and observer under these controls is unproven. The source-specific negative-control proves a single velocity is insufficient.
2. **Reciprocal controller:** the signed interface stress jump of the original \`G(X)\` action fixes controller support \`-[Trr]\` and admits zero-support balanced signed flux \`q2=-q1(Xplus+Xminus)/2\` when \`q1(Xplus-Xminus)≠0\`. Source equivalence is required; the zero-force family is not evidence of free energy or shielding.
3. **Maxwell:** the exact one-polarization sourced Ward identifies \`J=-measured_balance/E\` only where \`E≠0\`. At \`E=0\`, source work measurement loses rank and **cannot** determine \`J\` from energy balance alone. This is a mathematical source identifiability no-go, not an assertion of an actual apparatus current.

### Acceptance and DAG
Added both new literal-source W2 checkers to \`scripts/run_engineered_gravity_endpoint_local.py\` at 6f28cf6de36d9483e29592206bd36900657f5546. Added **two** source/checker blob-pinned mathematical packet entries (\`moving_tov_timelike\`, \`three_source_reverse\`) to \`Artifacts/engineered-gravity/engineered_gravity_dependency_manifest_20261129.json\` at 20800685abd50d579e72190eacdf1018e87c9de0. Updated fail-closed DAG at dc648f474e4e5f2ea11240fad49aa52f3a1e4205 to require the same source custody and \`physical_paid=false\` for W2 entries as for W1. Updated tests at c2fcc1acd55fedbebb7530449c235118d82d7442 to reject **nine** malformed claims including forged W2 blob and false physical completion. The W2 two-checker local run is **literal committed-byte verified**, but the current manifest/DAG/test FULL repo replay is not; no CI, no native F8, no source-to-physical receiver acceptance.

### Next coarse welds
**W2.1:** extend the exact moving shell formula to the **time-dependent** polar-areal Einstein/matter metric with nonzero \`N_t,f_t\`, and compare to original \`check_tov_causal_tube_and_junction.py\` normal-acceleration jet, including proper embedding and dynamic Israel constraints. Then attach the actual second variation \`EH+GHY+corners\` and original graph domain.
**W2.2:** attach real controller/material dynamics and shell support action to the reciprocal traction, and actual Maxwell/MHD \`J,T_{\mu\nu}\` to the Poynting work; do not freely choose an unrelated source.
**W2.3:** compute source-identical receiver packets for F8 original same-clock native sidecar, G3 reduced-to-full Einstein and G4 York/RMHD before any 1g/shielding/shortcut reverse-target claims.
**W3:** solve same-action coupled evolution with signed physical work, native forward source and independent neutral observer; certify or return a precise obstruction.

No physical lane is promoted. The earlier 36 physical obligations remain OPEN.


## W2.1 time-dependent spherical Einstein source → moving normal → Israel (29 November)

**Implemented in this same W2 cut, not deferred.** Exact original source-domain symbolic checker \`scripts/check_tov_dynamic_flux_israel_abi.py\` committed \`254e283981d8b5623a6f8de7d4b4f5f8329dfdb6\` (SHA Git blob \`5fd775dc25104bd79f0a670198e08c8278315f76\`, independently equal to the byte-identical local executed file). The nonstationary polar-areal metric is
\[
ds^2=-N(t,r)^2dt^2+f(t,r)^{-1}dr^2+r^2d\Omega^2,
\quad f=1-2m(t,r)/r.
\]
With a common proper-time moving wall \(R(\tau)\), \(v=\dot R\), \(a=\ddot R\) and \(U^t=\sqrt{f+v^2}/(N\sqrt f)\), the exact radial acceleration and extrinsic curvature are
\[
K^\tau{}_\tau=
\frac{a+(f+v^2)N_r/N-v^2 f_r/(2f)- vU^t f_t/f}
{\sqrt{f+v^2}},\qquad
K^\theta{}_\theta=\frac{\sqrt{f+v^2}}{R}.
\]
The **new time-jet term \(-v U^t f_t/f\)** cannot be omitted as in the static comparator. The 2D base warped-product identity gives \(G_{tr}=-f_t/(rf)\). Define the signed Eulerian orthonormal radial energy flux \(j:=-T_{tr}\sqrt{f}/N\); then
\[
f_t=8\pi r N\sqrt f\,j,\quad
m_t=-4\pi r^2N\sqrt f\,j.
\]
The other original spherical Einstein sources yield \(f_r=2m/r^2-8\pi r\rho\), \(N_r/N=(m+4\pi r^3p_r)/(r^2 f)\). When the two faces have the **same boundary \(f,N,R,v,a\)** and exterior vacuum, the exact resulting temporal Israel jump is
\[
\boxed{
[K^\tau{}_\tau]
=\frac{4\pi R}{f\sqrt{f+v^2}}
\left[(f+v^2)p_r+v^2\rho
-2v\sqrt{f+v^2}\,j\right].
}
\]
The bracket is precisely \(f\) times the wall-normal material stress \(T_{\mu\nu}n^\mu n^\nu\) in the orthonormal fluid/observer decomposition (with the signed \(j\) convention). This **connects the same source mass, pressure, density, radial momentum flux, moving normal and junction** without inventing an independent normal force. Reverse-solving zero shell traction fixes
\[
\boxed{
p_r=-\frac{v^2\rho-2v\sqrt{f+v^2}j}{f+v^2}.
}
\]
The checker asserts exact nonstationary Christoffel symbols and normal acceleration, mixed Einstein flux equation, forward/reverse symbolic equality, static \(v=0\) reduction and two nonzero-density/flux negative controls. Local literal source under 90 seconds exit0; source SHA256 \`bc49bf91f17747477747fed9a9b2daadb9dbff74a0172ad035c22cc7bf5fe1b1\`, stdout SHA256 \`efa894c722cae311b397600b2da13f9c8bd4323c7b69c356cc938ba16681b3d5\`. The original TOV material level surface has \(\rho=p_r=j=0\) in the static background, but full moving Einstein–matter dynamics may generate nonzero physical flux; its evolution is **not** constructed or assumed away.

**Boundary interpretation limitations:** This is exact algebra for **one spherical polar-areal metric with vanishing radial shift**, the chosen signed flux convention, and assumed common physical boundary induced data. It does not construct the physically required dynamical solution or guarantee that the two faces admit matching \(N,f,R,v,a\); there is no full nonspherical trace analysis, Israel sheet conservation law, GHY/corner second variation or global stability. G4 Einstein–RMHD is a mathematical *consumer* of the flux/normal pattern, not a demonstrated transplant to the distinct G4 matter system.

**Accounting:** Runner registered at \`1e5c5b8f0c675a1822bbc60b3a0a296777c5687d\`. Source checker pinned as third W2 entry \`dynamic_tov_flux_israel\` at \`b1bef684df76d7c2e1bc5220cc19fb86631b6a16\`. Two additional source-admission controls were added to the DAG test at \`47558a63657d9d2a99f1b7f1afe46b53f4c108dd\`, bringing the planned malformed-claim count to eleven; full *committed* DAG test replay remains outstanding. The **three new W2 mathematical scripts** (static moving, typed three-source reverse, dynamic flux) passed **literal byte-identical local execution**; do not conflate that with original native F8, full programme owner replay, verified physical Einstein source or actual device.

**Next whole-system weld:** assemble exact time-dependent S0–S2 Einstein–matter boundary and exterior normal packet with independent nonzero \(j\) and a real constitutive/constraint-compatible matter evolution; simultaneously compile a distinct Maxwell current/stress sheet and reciprocal controller reaction packet. Then attach physical observer/tide/clock via original G3 and F8 receivers, not an arbitrary desired gain. The original 36 whole-programme physical obligations still remain open.


## W2.2/W2.3 large-cut closure: original Einstein mass + moving Israel + wall-frame inverse + constructive radial constraints (29 November)

**Repository reconciliation.** #1547 began this cut at \`d862d0337d0c621bd5838a287be3741ac2587b08\`; #1554 \`9c8e8721f4b0d721a630b5491a0870a0523a86d8\`; #1537 \`5b00538d4ba19b8c69cb198fe51b2c6aeba204c2\`; #1555 \`be212eec07c0475117c8985f08fdd7a21e4907e7\`. Read the literal existing original \`check_tov_dynamic_flux_israel_abi.py\`, \`check_tov_moving_mass_constraint_weld.py\`, \`check_engineered_gravity_boundary_packet_w2.py\` and the W2 manifest; reused them. No new PR-donor source code imported, no unverified master search success claimed.

### W2.2 two Einstein equations simultaneously close the moving wall stress source
New \`scripts/check_tov_mass_flux_surface_closure.py\`, executed literal source with Git blob \`df20eed79509be852151ce1f38c656130b44ffe9\`. Starting from the SAME Misner–Sharp mass \(m(t,r)\), original spherical Einstein equations
\[
m_r=4\pi r^2\rho,\qquad m_t=-4\pi r^2N\sqrt f\,j
\]
require exact mixed-derivative compatibility:
\[
\boxed{\partial_t(r^2\rho)+\partial_r(r^2N\sqrt f\,j)=0.}
\]
An independently prescribed density/current that violates this condition cannot arise from one smooth mass function. A nonzero-divergence numerical-symbolic negative control is included.

For a vacuum Schwarzschild exterior with constant \(M\), a common radius \(R(\tau)\), timelike proper radial velocity \(v=\dot R\), and common induced surface geometry, \(\frac{d}{d\tau}(m_{\mathrm{int}}-M)=0\) gives the **moving mass-flux condition**
\[
\boxed{j_{\mathrm{wall}}=\frac{\rho_{\mathrm{wall}} v}{\sqrt{f+v^2}}.}
\]
Together with the previously derived exact moving temporal Israel condition
\[
(f+v^2)p_r+v^2\rho-2v\sqrt{f+v^2}\,j=0,
\]
it determines the two radial source components uniquely for fixed wall density and velocity:
\[
\boxed{j=\frac{\rho v}{\sqrt{f+v^2}},\qquad p_r=\frac{\rho v^2}{f+v^2},\qquad \rho p_r=j^2.}
\]
The coefficient determinant in \((j,p_r)\) is \(- (f+v^2)^{3/2}\), nonzero for a timelike wall (\(f>0\)); the wall density \(\rho\), tangential stresses, matter action, bulk continuation and support dynamics remain FREE/UNPAID. The formula works for BOTH signs of \(v\) and does not assert positive energy when the source has arbitrary-sign \(\rho\). It is a necessary no-shell vacuum boundary relation, **not** a general bulk equation of state.

The original repaired TOV material profile has \(\rho_0(1)=p_{r0}(1)=0\). If a future physical material evolution preserves the *moving* zero-density level surface, then zero normal flux and pressure follow on the wall from these relations. At coordinate-fixed radius, however, the original \(p_{r0}''(1)=-8p\) makes the second pressure jet necessarily \(\;p_{r2}(1)=-2\phi p_{r1}'(1)+8p\phi^2\;\), and for a background zero current \(j_2(1)=-2\phi j_1'(1)\). These are not independently disposable. The checker verifies both shape derivatives and independent source/flux counterexamples.

### W2.2 exact moving observer stress frame (bidi converse)
New \`scripts/check_tov_wall_frame_stress_inverse.py\`, executed literal source Git blob \`b27efd0f5110228955276a99801675027faa97a9\`. In the radial Eulerian orthonormal frame the physical 1+1 stress is \(T_{\hat\alpha\hat\beta}=\begin{psmallmatrix}\rho&-j\\-j&p_r\end{psmallmatrix}\). The moving wall tangent and outward normal are \(U^{\hat\alpha}=(\sqrt{f+v^2},v)/\sqrt f\), \(n^{\hat\alpha}=(v,\sqrt{f+v^2})/\sqrt f\). Both orthonormality and independent stress projections are proved:
\[
T_{nn}=\frac{(f+v^2)p_r+v^2\rho-2v\sqrt{f+v^2}j}{f},\quad
T_{Un}=0\iff\text{no energy flow normal to wall}.
\]
Solving **both** \(T_{Un}=0\) and \(T_{nn}=0\) in reverse uniquely reproduces the same \(j,p_r\) as the Einstein mass/Israel forward construction. The resulting radial stress has rank one, \(\det T_{1+1}=0\), and the wall-frame comoving density is \(\rho f/(f+v^2)\), generically nonzero; a no-shell vacuum exterior does not imply vacuum matter immediately inside the wall. This is an exact two-way geometric equivalence. It leaves transverse pressure and the full tensor, actual material constitutive law and GHY/corner second variation unconstructed.

### W2.3 explicit NONZERO radial Einstein constraint family (constructive, NOT original action)
New \`scripts/check_tov_moving_constraint_family.py\`, executed literal Git blob \`23f2f03c33300c59a15d648698201220f76c6f5d\`. Instead of assigning independent wall data, construct, for any smooth positive radius \(R(t)\), with \(\alpha=\lambda(\lambda+2)\), \(x=r/R(t)\),
\[
m(t,r)=\frac{\alpha}{2}\left(\frac{x^3}{3}-\frac{x^5}{5}\right),\quad
\rho(t,r)=\frac{\alpha(1-x^2)}{8\pi R^3},\quad
p_r(t,r)=-\frac{\lambda(1-x^2)^2}{8\pi R^3}.
\]
Define \(f=1-2m/r\), the Einstein radial lapse slope \(N_r/N=(m+4\pi r^3p_r)/(r^2f)\) with exterior-matched boundary lapse, and **derive** the nonzero signed Eulerian flux
\[
j=\frac{\rho\,r\,\dot R}{R\,N\sqrt f}.
\]
The file proves both original Einstein radial mass/flux equations, their differential integrability (as one \(m\)), and the exact original TOV static limit at \(R=1,\dot R=0\), including \(f,\rho,p_r,N_r/N\). On \(r=R(t)\): \(m=M=\alpha/15\), \(\rho=p_r=j=0\), and \(f,f_r,N_r/N\) match the instantaneous Schwarzschild exterior. Thus this is a nontrivial **radially constrained, source-compatible geometric continuation** with nonzero interior time flux and matched physical wall *spatial* jets, not merely an imposed boundary condition.

**ESSENTIAL non-promotion:** The rescaled \(\rho,p_r,j\) have NOT been derived from the original 3-field repaired TOV constitutive action for dynamical material labels. \(N\) is defined by a spatial integration of its radial Einstein equation; no independent time equation, Einstein angular stress \(p_t\), Ward/matter Euler evolution, momentum constraint for a full 3+1 slice, global causal exterior, GHY/corner or energy positivity/regularity theorem was solved. The wall \(R(t)\) is prescribed for this *constructive radial constraint family*, not shown to satisfy the original material equations. Treat this as a candidate to weld to an actual constitutive deformation or use its failure as a concrete obstruction; do not promote it to a physical evolving star.

### Acceptance, provenance and next bigger cut
All THREE new W2.2/W2.3 files **ran locally under 90 seconds with exit0**, and their exact Git blob byte hashes match the resulting #1547 committed files. All three have signed \(v\) support and negative controls. The original existing checkpointed runner includes all three. The manifest now holds SEVEN W1 entries and SIX W2 entries, 13 total pinned mathematical source/receiver interfaces, with \`physical_paid=false\`. The added three failure controls (fake mass/flux payment, wall-stress source substitution, invented Einstein physical lane) bring the recorded negative-control suite to fourteen, but literal full DAG test/aggregate replay has NOT occurred. The 36 primary physical programme obligations remain OPEN.

**W2.4 whole-thing next:** compute the original nonlinear repaired TOV material action under a dynamical radial label \(Y(t,r)\); differentiate its exact stress to obtain \(\rho,p_r,j,p_t\), and test whether the W2.3 rescaled mass profile can be generated *without* a separate, unphysical source. This is the decisive material-to-Einstein weld, not more finite positive polar trial searching. If not, identify the exact algebraic incompatibility and reverse-solve admissible \(Y\)/metric histories. Alongside that, attach the same source-qualified work/traction to reciprocal controllers, Maxwell/RMHD matter, and F8/G3 same-event original receivers with independent source hashes. The physical EH/GHY/corner and free nonspherical modes remain essential; no native F8 or empirical 1g claim.


## W2.4 DIRECT original constitutive-action audit against the constructed moving Einstein mass profile (29 November)

**Genuine decisive obstruction, not a hypothetical open assumption.** New \`scripts/check_tov_original_material_flux_weld.py\`, committed \`5a9855fb7d9d561f980fca61c331bc96a21af8a2\`, Git blob \`671a81ab6afac23e30dacc5e8b739e0ec5d066af\`; literal locally executed Python/SymPy source PASS under 90 seconds. Reopened the ORIGINAL repaired TOV matter action with \(\lambda>0\), \(\rho=(2+\lambda)p(1-x)\), \(p_r=-p(1-x)^2\), \(p=\lambda/(8\pi)\), \(\,f=1-\lambda(2+\lambda)(x/3-x^2/5)\), \(d=(\rho+p_r)/(2f)\), \(a=(\rho+p_t)/2\), \(V=\rho-2a-df\). For a radially deforming three-component material map \(Y^A=Y(t,r)n^A\), its exact kinetic/source density on polar-areal spacetime is
\[
W=d(Y^2)\left[fY_r^2-\frac{Y_t^2}{N^2}\right]+2a(Y^2)\frac{Y^2}{r^2}+V(Y^2)
\]
and stress from the SAME action \(S_m=-\int\sqrt{-g} W\):
\[
\rho_{\mathrm{Eulerian}}=W+2dY_t^2/N^2,\quad
p_r=2dfY_r^2-W,\quad
j=-2d\sqrt f\,Y_tY_r/N.
\]
The checker derives and verifies ALL three and reobtains the exact original background \(\rho,p_r,j=0\) with \(Y=r,Y_r=1,Y_t=0\). No separately prescribed \(T_{tr}\) is used.

The constructive radial Einstein family \`check_tov_moving_constraint_family.py\` proposed uniform label scaling \(Y=r/S(t)\), whose first velocity time jet at \(S=1\) is \(Y_t=-r\dot S\). On the initial original metric and source, this true action predicts
\[
j_{\rm action}=\frac{(\rho+p_r)r\dot S}{N\sqrt f},
\quad\text{whereas the prescribed mass profile needs}\quad
j_{\rm mass}=\frac{\rho\,r\dot S}{N\sqrt f}.
\]
Therefore **the original material and the W2.3 mass family fail to weld for uniform scaling inside the bulk**:
\[
\boxed{j_{\rm action}-j_{\rm mass}=\frac{p_r r\dot S}{N\sqrt f}\ne0,\quad 0<r<1,\;\dot S\ne0.}
\]
At the source edge \(r=1\), this defect vanishes because \(p_r(1)=0\): first-order surface matching is INSUFFICIENT to pay the interior action/Einstein source. A rational pointwise nonzero interior fixture plus static/no-motion zero controls are executed.

**Exact reverse-solved candidate constructor:** on the original slice, holding the source \(d\), the Einstein mass flux constraint fixes the first material velocity to
\[
\boxed{Y_t=-\frac{\rho}{\rho+p_r}r\dot S
=-\frac{\lambda+2}{\lambda+1+r^2}\,r\dot S.}
\]
The ratio is regular on the closed star, has centre limit \((\lambda+2)/(\lambda+1)\), equals one at the material wall, and yields the correct kinematic boundary \(Y_t(1)=-\dot S\). This is a **genuine first-time-jet geometric weld** from the original source into the constructed mass profile. The necessary interior motion is **not** a uniform radial scaling; its induced \(Y_r(t,r)\), actual material Euler–Lagrange equation, evolving metric and lapse must be constructed and tested before it is called a solution. If the full PDE refuses this jet, return the exact obstruction; do not relax source identification.

Four W2.2–W2.4 checkers were run locally and exact Git SHA1 blobs matched committed source bytes:
- \`check_tov_mass_flux_surface_closure.py\` \`df20eed79509be852151ce1f38c656130b44ffe9\`
- \`check_tov_wall_frame_stress_inverse.py\` \`b27efd0f5110228955276a99801675027faa97a9\`
- \`check_tov_moving_constraint_family.py\` \`23f2f03c33300c59a15d648698201220f76c6f5d\`
- \`check_tov_original_material_flux_weld.py\` \`671a81ab6afac23e30dacc5e8b739e0ec5d066af\`.

Actual SHA256 checksums and log hashes committed to \`Artifacts/engineered-gravity/w2_mass_flux_material_local_receipt_20261129.json\`; all 4 exit0 with 90s limit. No GitHub CI, no all-lane aggregate or native F8. The runner now registers these four mathematical checks and W1/W2 manifest pins track the same source, with W2.4 math \`physical_paid=false\`; sixteen malformed-claim tests are committed but **not asserted as replayed**. The 36 named whole-programme physical obligations persist.

### Next whole-problem high-alpha order
**D first source weld:** generate the exact Euler–Lagrange PDE for radial material \(Y(t,r)\) from the ORIGINAL \(a,d,V\), including nonuniform reverse-solved time jet and the evolving \(f,N\); couple \(T_{tt},T_{tr},T_{rr},T_{\theta\theta}\) to all Einstein equations and matter Ward. Determine if the W2.3 candidate profile must be modified and derive actual \(m_t,m_r,\nu_r\) from one source. Then solve the physical wall graph domain, second Israel normal, EH+GHY/corners, and free metric polar modes, not merely additional Ritz trial signs.

**Cross-lane shared source ownership:** the mathematical Maxwell current \(J\) still has no original physical apparatus source; reciprocal \(G(X)\) needs actual material/controller and support; G3/G4/F8 source-identical causal history, native same-clock receiver and physical calibration are independent unsolved objects. Reuse the source/normal/energy maps and exact no-go fibres, without promoting any lane for algebraic identities or a constructed off-action star.
