# Smith/Filsinger — all-N spatial and retarded-time formal cut (17 Nov 2026)

## Source and existing owners reused

The user-origin physical steelman is a coherently controlled differential/phase source–sink with propagation, nonlinear material response, and possible independently replenished Sun–Earth energy. The source circuit identity is still open; do not infer it from Smith and Filsinger source similarities, acoustic phase, or geometry.

Reuse: `Circuit36927RecoveryEnergyBoundExact` (Nat ordered-work carrier), `SmithFilsingerTimeIndexedTransferExact` (`RetardedFlight`), `SmithFilsingerReplenishedCycleCapExact` (same-cycle bound and order transitivity), `SmithFilsingerSourceMaxwellBoundaryWeldExact` (typed selected-original field/port and source attribution), and the existing `SmithFilsingerFinitePhaseMatchingExact` owner. The distributed LC/plasma script is a *numeric negative/positive topology donor*, not a substitute for formal proof.

## New formal Agda modules
- `DASHI/Physics/Motors/SmithFilsingerSpatialPortChainExact.agda`
- `DASHI/Physics/Motors/SmithFilsingerTimedSpatialPortChainExact.agda`
- `DASHI/Physics/Motors/SmithFilsingerSpatialSourceBoundaryWeldExact.agda`

### F10 all-N discrete local-to-global conservation
`SpatialCell incoming outgoing` carries exact local directed work:
[
incoming + (driver+stored_{initial})
= outgoing + (load+ (heat+radiation+stored_{final})).
]
`SpatialChain first last` is dependent: the outgoing of each preceding cell **definitionally matches** the next cell's incoming. `spatialChainWorkBalance` is a proof *by induction for any finite chain length*, using `spliceSharedWork`, normal-form polynomial regrouping, and cancellation of matched internal work. Conclusion:
[
first+\sum_i driver_i+\sum_i U_{i,initial}
=last+\sum_i load_i+\sum_i loss_i+\sum_i U_{i,final}.
]
Parentheses are grouped explicitly in the Agda module. `spatialLoadBoundedByAdmittedInputs` derives a general upper bound via the **existing** finite Nat order carrier. `sourceFreeSpatialChainHasZeroLoad` proves zero output from zero exterior input, local drivers and initial storage, for **every N**. A nonempty two-cell example has shared internal port 8 and outer work 10→6 with explicit losses and loads.

This is an exact energy-ledger proof candidate, **not** a theorem that a spatial Maxwell PDE admits such a chain or that an external solar port is physically energized. The Nat work grid may represent a chosen exact energy quantisation; no assertion of exact real-valued measured work is inferred.

### F02/R2 discrete retarded temporal weld
`CausalSpatialCell` combines a `SpatialCell` with the pre-existing `Time.RetardedFlight` and exact launch/arrival-index identity. `TimedSpatialChain` composes these with shared time endpoint types. `allTimedPathsArriveAfterLaunch` proves launch≤arrival for any finite causal chain by transitivity of the inherited Nat order. `eraseTiming` preserves the underlying all-N work conservation (`timedSpatialEnergyConservation`). Example: 1→3→7 clock indices, two spatial energy cells.

**Important:** discrete nonnegative travel-time alone is neither a strict Maxwell light cone, nor an actual phase/dispersive group-delay theorem, nor evidence the electrical 7.8 kHz carrier exists. Full F02/F10/R2 physical wave propagation, Hall/Pedersen tensor and source boundary remain open.

### Source-indexed original-world weld
`SpatialToOriginalSourcePort b f` is indexed by the existing `Weld.SelectedBoundary b` and `Weld.FormalFieldToPort b`. It demands *two additional physically sourced equalities*, connecting all-N spatial incoming/outgoing balances to the SAME selected original natural/controller/stored/load/returned-port fields. `spatialEnergyClosesSelectedPort` derives the original-port equality by transitivity from these obligations and the all-N theorem. Neither actual source input nor material/field coefficients are conjured by `Set` fields; the mapping remains UNINHABITED as a physical admission.

## Local source-equivalent verification and exact-head scope
- Independent Python-integer random chain replay: **900/900 exact nonnegative chains PASS**, lengths N=0,1,2,3,5,8,16,32,64, with global cancellation and load upper bound.
- Previously implemented distributed LC/plasma model: **16/16 local pytest pass**. Its series 110% useful-load improvement vs shunt −2.25% remains a chosen-model topology discriminator, not source-positive power.
- New regression owner `scripts/test_smith_filsinger_spatial_chain_exact.py`: deterministic integer tests (including forged intercell port, source-off, donor depletion); integrated into `scripts/check_smith_filsinger_dynamic_replenishment.sh`. Local random replay is an independent equivalent implementation; committed GitHub-head suite NOT executed here.
- Pinned Agda `scripts/check_smith_filsinger_formal_weld_agda29.sh` includes all THREE new formal owners. **The pinned Agda executable/toolchain is not available in this runtime; kernel gate D1 remains OPEN.** Source structure, no holes/postulates, and independent arithmetic validation are not kernel acceptance.

## Result / strict remaining gates
| Cut | New source-level mathematics | Still required |
|---|---|---|
| F10 finite spatial energy | All-N shared-port inductive law and load/source-off corollaries | Pinned kernel + real Maxwell/constitutive physical field solution |
| F02 finite timing | All-N causal clock order and conservation on timed paths | Real spatial geometry, full dispersion, physical phase at receiver, Maxwell signal-front causality |
| F13 physical source access | Typed same-original spatial→Maxwell port readback contract | Measured local boundary, true solar/magnetosphere coupling, nonlinear material and return admittance |
| F15/R3 whole-cycle gain | Finite-source and stored-state gate inherited | Independent replenishment and restored states, positive signed natural work after all ionization/thermal/control costs |
| F14/F16 | Earlier source-first and cloud-causality guards retained | Original full electrical/acoustic regime, actual atmospheric intervention causal study |

**Next max-cut:** execute pinned Agda target locally on the proper host; then work on a selected, *physically sourced* 3D spatial Maxwell/soil/ionosphere current-to-port operator. If device-specific source/geometry traces remain absent, a general formal operator can only be a conditional mathematical object and must not be promoted to original Sun–Earth power measurements.

Attribution: conventional network conservation / time-indexed reasoning cited as reusable mathematics; user originated the proposed large solar-powered phase-controlled harvesting steelman; DASHI proof source is a derived formalisation. No ESD edit, no claimed new physical theorem, no premature TOE promotion.

## Concurrent original material-ledger cross-check
While this cut was being committed, PR #1524 advanced to `fb897a90e819bd756523de6aa842c34f20b4a993`, adding `materialModulationReconcilesOriginalCycleLoss` in `SmithFilsingerMaxwellMaterialEnergyCutExact.agda`. It derives a **two-ledger consistency** obligation between signed original-cycle loss and the field/material-modulator ledger: `old internal loss + paid modulation = field dissipation/outgoing + material dissipation + recovered modulation` under explicit same-source work and restored-field/material-storage hypotheses.

This is complementary to the new all-N spatial port telescope: one checks **spatial intercell work cancellation**, the other prevents **double accounting of modulator work across two original-port ledgers**. Reuse both from the existing `SourceMaxwellBoundaryWeld` and do not merge their physical `Set` witnesses by assertion. The concurrent theorem is source-authored but was not pinned kernel checked in this session.
