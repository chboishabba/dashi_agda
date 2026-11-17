# Smith/Filsinger — finite-volume Poynting / CFL / Maxwell boundary max-cut
**17 November 2026.** No original device evidence added. User's solar-powered nonlinear source/sink steelman remains the motivating *hypothesis*, not a proof of solar-electric harvesting.

## Source / reuse first
- `DASHI/Physics/Plasma/KSW668FullVectorMaxwellJetExact.agda`: original pointwise real-field 3-vector Maxwell curl-jet Poynting identity, no space-time integral.
- `DASHI/Physics/Motors/SmithFilsingerFullVectorPoyntingPortWeldExact.agda`: same-original physical Maxwell-to-terminal **integration implication** with signed source/controller work, material-law and full restoration constraints.
- `SmithFilsingerSpatialPortChainExact.agda` and `SmithFilsingerTimedSpatialPortChainExact.agda`: all-N chain and finite travel-time order.
- `SmithFilsingerSpatialSourceBoundaryWeldExact.agda`, `SmithFilsingerSpatialSourceCapWeldExact.agda`: same-original evidence/source caps; no fabricated field.
- `SmithFilsingerMaxwellMaterialEnergyCutExact.agda`: canonical material/controller energy reconciliation.

## New formal F10 finite-volume mesh: not a new Maxwell solution

`DASHI/Physics/Motors/SmithFilsingerFiniteVolumeFaceIncidenceExact.agda` introduces `LocalVolumeCell` with separately oriented `exteriorIncoming,internalIncoming,driverWork,initialStored,exteriorOutgoing,internalOutgoing,usefulLoad,dissipation,finalStored`. It **requires** a local exact cell energy law; none is derived from a pointwise Maxwell jet alone.

`sumPairDistributes` and `foldLocalConservation` prove the sum of local laws for *arbitrary finite lists of volumes*. `OrientedFaceMesh` checks the internal incoming and outgoing sums against a common list of face-work receipts. Then `finiteVolumeExteriorEnergyBalance` uses the existing DASHI Nat cancellation lemma to prove:

[
W_{\rm exterior,in}+W_{\rm controller}+U_{\rm initial}
=
W_{\rm exterior,out}+W_{\rm load}+W_{\rm losses}+U_{\rm final}.
]

Proof is independent of a chain ordering; it permits branched meshes and cycles. `finiteVolumeUsefulBelowAllSuppliedWork` and `finiteVolumeSourceFreeHasZeroLoad` derive upper and source-off consequences; two-cell and branched three-cell nontrivial Agda example sources included.

**Refinement still needed:** the currently available `OrientedFaceMesh` matches *aggregate incoming/outgoing face sums against a common face list*. The underlying **per-cell, oriented face-ID bijection/permutation and signed quadrature** is a separate strengthened incidence certificate; it is not established by mere equality of the aggregate totals. Do not call this a fully indexed discrete 3D Stokes complex, and do not conflate a Nat nonnegative power record with the original signed real Poynting surface integral.

`DASHI/Physics/Motors/SmithFilsingerFiniteVolumeMaxwellBoundaryWeldExact.agda` converts a fully reconciled finite mesh to the ORIGINAL `SpatialCell` and `SpatialChain` owners. It then consumes the EXISTING source-indexed `SpatialToOriginalSourcePort` witness, including physically sourced *separate* input/output calibration equations, to derive the same-original port law. It does not solve those physical equations or establish that the selected Maxwell jet was integrated over actual receiver geometry.

## F02: CFL stability != physical light-cone theorem
For uniform spacing in d=3, the standard explicit Yee CFL bound is `c*dt <= dx/sqrt(3)`, and for anisotropic cells the corresponding inverse-square spacing formula applies. This controls a chosen scheme's stability, not a proof that any nonzero numerical influence is confined to the physical Maxwell cone. A local-stencil scheme can influence a neighbour `dx` away in one step `dt`, with `dx/dt>c` under a *smaller* stable timestep. Source `SmithFilsingerYeeCFLConeGuardExact.agda` proves a simple integer counterexample: Courant bound `1<=4` while a distance-4 stencil neighbour is outside the radius-1 physical front. A physically valid front-support theorem remains an **independent admission** tied to a specified continuum Maxwell PDE, physical material response and calibrated geometry.

Also, the staggered Yee magnetic cross-time energy `H^(n-1/2) dot H^(n+1/2)` need not be a positive *individual cell term* without supplementary stencil/global modified-energy estimates. Do not simply assert positive-definite per-cell energies from CFL. Existing finite-scheme energy conservation and positive physical energy under stable dispersion require separate proofs.

## F13: real current/voltage, surfaces and nonlocal Green operator

A **terminal** power equals the selected spatial surface Poynting flux only under the particular geometry, current return, instrument definition, and field constraints. At nonzero varying magnetic flux, `V=-int_C E·dl` can depend on contour. Ampere circulation `oint H·dl` equals conduction PLUS displacement current, so it is NOT generally equal to a measured conductor-current terminal trace. No source-free discrete Stokes theorem can establish `Wport=int V I dt` without this correct port identity.

The correct independent next physical producer is a causal, passive stratified background dyadic Green operator for the actual soil–air–ionosphere boundary with Hall/Pedersen and source data. Model local nonlinear plasma with `ΔJ_nl[E,n_e,...]`, and retain full source feedback, modulator work and energy exchange, with independent physical parameter estimates. Chew's *Waves and Fields in Inhomogeneous Media*, chapters 7 and 8, supplies a relevant analytic technique but is **not** itself a solved operator for the Filsinger geometry. Reference: https://engineering.purdue.edu/wcchew/book.html ; Yee CFL review: https://www.nist.gov/system/files/documents/mml/mmsd/Gibson-2.pdf ; https://www.osti.gov/servlets/purl/1418786 .

A Green operator can reduce simulation scope to a nonlinear active volume coupled to a known background, but does not *manufacture* source strength or justify ignoring remote backaction/response when the source itself is time varying and nonstationary.

## Execution and acceptance
New formal sources committed:
1. `DASHI/Physics/Motors/SmithFilsingerFiniteVolumeFaceIncidenceExact.agda`
2. `DASHI/Physics/Motors/SmithFilsingerFiniteVolumeMaxwellBoundaryWeldExact.agda`
3. `DASHI/Physics/Motors/SmithFilsingerYeeCFLConeGuardExact.agda`

All three added to the **existing** `scripts/check_smith_filsinger_formal_weld_agda29.sh` pinned local acceptance. Independent exact integer replay: **512/512** arbitrary directed meshes (N=0,1,2,3,5,8,16,32), all local + global conservation and exact internal-face equalities passed. Committed `scripts/test_smith_filsinger_finite_volume_face_incidence_exact.py` added to `scripts/check_smith_filsinger_dynamic_replenishment.sh` but full same-head pytest and pinned Agda compiler **not executed** in this session. Source proof candidates are NOT kernel-receipted.

Remaining:
- **F10-fvm** per-face indexed incidence + true signed field quadrature; actual SI Maxwell material PDE and local integrated power receipt;
- **F02-cone** scheme dispersion/energy stability and a separately proved *physical* finite-support Green cone, not mere CFL;
- **F13-port** identified terminal voltage/current/return geometry + causal dyadic soil-air-ionosphere Green operator + physical natural-source forcing;
- **F15/R3** verified replenished signed environmental work over same-source restored cycles after all material/controller/ionisation overheads;
- **F14/F16** original device inverse match and rain/cooling causal intervention still OPEN.
- **D1** pinned Agda kernel for every exact head target OPEN.

**Attribution:** Maxwell/Poynting/Yee/Chew are standard external physics/methods, the Smith/Filsinger high-energy solar phase-coupling idea is user-origin, and the finite graph/source-indexed Agda constructions are DASHI research artefacts. No ESD files edited; no premature TOE promotion.

## Adversarial incidence negative control (F10-INC wall)
`test_aggregate_totals_not_a_per_cell_face_id_certificate` supplies a declared 0→1 (3 work), 1→2 (4 work) graph, but replaces the physically expected per-cell incoming face assignment `[0,3,4]` with `[4,0,3]`. Because total inward and outward work remain both 7 and all local energy ledgers are individually balanced, the present aggregate `OrientedFaceMesh` theorem **accepts** this intentionally misassigned topology. This is a constructive proof of the limits of the current abstraction, **not** a failed conservation theorem.

Closing F10-INC needs an actual finite incidence/boundary matrix (`∂²=0` when applicable), typed cell IDs, exactly-once directed face assignments, and a signed field-valued orientation/area pairing; merely retaining an unordered face-work list cannot guarantee those physical identities.
