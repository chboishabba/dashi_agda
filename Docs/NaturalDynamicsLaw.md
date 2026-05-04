# Natural Physical Dynamics Law (Doc lane)

This note isolates the *minimum theorem/program shape* required to claim a natural, non-engineered dynamics law in the Dashi stack. It draws from the closure pipeline, the Lorentz-seeking summaries, and the RG dynamics notes to list the state space, candidate evolution laws, admissibility conditions, and the outstanding engineered/post-selected points.

**State space**

- `State` = `ShiftState` for `(m=1,k=3)` as used in `DASHI/Geometry/ShiftLorentzEmergenceInstance.agda` and the RG instance: an ultrametric vector of four signed integers supporting MDL, projection, and cone evaluation.
- `Observable` space = Drop of `ShiftConeCompatible` + Hecke signature/eigen/motif summary saved in `Docs/PhotonBridge.md` and the RG notes; these engineered outputs are the objects under observation.
- `Coarse shell` = `shiftCoarse` from `DASHI/Physics/Closure/ShiftRGObservableInstance.agda`, which projects via `LFS.coarseProj` into an invariant coarse subspace.

**Evolution law candidates**

1. `ShiftStep` (MDL Lyapunov step) from `DASHI/Geometry/ShiftLorentzEmergenceInstance.agda` and `[Docs/CharmPhotoproduction.md](./CharmPhotoproduction.md)`: contraction + MDL descent utilities interpreted as the canonical evolution `T(x)`.
2. `ShiftCoarse` / `ShiftCoarseAlt` from the RG notes: projection-driven flows defined via `LFS.embedCoarse ◦ LFS.coarseProj` and the phase-shifted composite with `step`. These are not emergent laws but engineered coarse-graining maps.
3. Candidate `Rᵣ`, `Pᵣ`, `Tᵣ` flows in `DASHI/Physics/TailCollapseProof.agda` and `Docs/SaturationLayer.md`: physical RG-style renormalizers that collapse tail-data but are not yet wired to the canonical dynamics.

**Admissibility conditions**

- `ShiftRGAdmissible` bundles `ShiftInBasin` with `ShiftConeCompatible` and the execution-admissibility witness from `ShiftLorentzEmergenceInstance.agda`: MDL descent, cone invariance on projected delta, and basin stability.
- RG observables require `admissible⇒basin` and `admissible` closures defined in `Docs/CMSCapstone.md` and `DASHI/Physics/Closure/RGObservableInvariance.agda`, so true dynamics are only those satisfying both the geometric cone law and the coarse basin law.

**Why current dynamics look engineered/post-selected**

1. `shiftCoarse` is a prescriptive projection rather than a derived law; it uses `LFS.coarseProj`/`embedCoarse` without a dynamical derivation, so the flow is engineered in the code.
2. `ShiftCoarseAlt` and the phase-offset universality theorems in `Docs/CMSCapstone.md` compare ad-hoc schedules, not distinct emergent flows.
3. Basin and cone compatibility are enforced via fixed witnesses (e.g., canonical shell points, `ShiftInBasin` = `pos ∷ []`), so the dynamics are post-selected to keep the law satisfied.
4. The saturation/numerical lane (`Docs/SaturationLayer.md`) writes the response as a GBW-like prototype; the physics content still lives in the external model layer and is not derived from the internal dynamics.

**Repo-accurate correction**

The main gap is not that the repo lacks an execution contract from zero.
[`ExecutionContract.agda`](../DASHI/Physics/Closure/ExecutionContract.agda)
already exists and the shift lane already instantiates it. The stronger
problem is that several of the current shift-side witnesses are still too weak
or too local:

- arrow/eigen summaries are still trivialized on the shift side,
- basin nontriviality still concentrates on the canonical `(1,3)` carrier,
- and the best dynamics/invariant couplings are still local rather than
  realization-independent.

**Origin traceability correction**

The downloaded origin-traceability diagnosis correctly identifies the missing
general convergence-rate theorem, but it should not be read as saying the repo
has no dynamics owner. `CanonicalDynamicsLawTheorem.agda` already packages
propagation, causal admissibility, monotone quantity, continuum-law status, and
a realization-independent proof-shape slot over current bounded witnesses.
What remains missing is the stronger theorem:

```text
d(K^t x, x*) <= max 0 (d(x, x*) - t)
```

on the intended carrier, with an explicit horizon/fixed-point certificate. That
rate theorem is the promotion target; another status package would not close
the natural dynamics law gap.

**Current W2 promotion boundary**

`DASHI.Physics.Closure.NaturalP2ConvergencePromotionObligation` records the
current state after the landed convergence work. The repo has finite
shift-flow convergence, a pointed-metric/horizon rate over the shift-flow
carrier, and a realization-indexed metric family over realized shift-flow
states. Broader natural / `p2` promotion still needs:

- promotion authority;
- a natural bridge or obstruction over the intended candidate family;
- p2 naturality and coherence laws;
- carrier transport beyond the shift-flow carrier;
- a carrier-general convergence-rate receipt;
- uniform realization-rate evidence beyond the current shift-flow family.

That module is an obligation surface only; it does not promote a natural
dynamics law.

The current typed W2 output is the sharper obstruction
`canonicalNaturalP2BridgeCarrierGeneralConvergenceObstruction`. It names the
stronger ingredient rather than constructing a promotion receipt: a canonical
`p2`-key schedule bridge is still required on the natural side, and carrier
transport must preserve the pointed convergence rate with uniform
realization-rate evidence beyond the shift-flow carrier. The existing
shift-flow and realization-indexed receipts remain landed, but they are not
carrier-general authority.

**Path B / Offline L2 result**

`NaturalP2ConvergencePromotionObligation` now records
`canonicalOfflineL2InsufficientForConvergenceRate`. This is the Path B
diagnostic: the existing
`CanonicalP2OfflineL2ObstructionCertificate` proves that below-δ normalized
eigenShadow candidates cannot force the canonical `p2` key. That certificate
is therefore negative evidence for the bridge, not a convergence-rate lift.
It still leaves the carrier transport law, transport-preserves-rate law,
uniform realization law, and positive p2-key schedule bridge absent. W2 remains
blocked and non-promoted.

**Bridge toward natural dynamics law**

To answer the request, we require: a state space defined by the `ShiftState` vector and cone witness, an evolution candidate that emerges from contraction + projection (not a hand-wired coarse map), admissibility tied to geometry/MDL rather than fixed witnesses, and a demonstration that the engineered coarse maps can be replaced by naturally emergent flows (e.g., `Tᵣ` or `Rᵣ` flows). Without that derivation, the law remains engineered/post-selected.

This document is disjoint from shared README/TODO files and can serve as the working note for the natural dynamics law lane.
