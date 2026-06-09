# Autonomous Execution Brief

Date: `2026-05-19`
Phase: `Paper 7 full-unification publishability orchestration`

## Purpose

This file exists to stop autonomous child runs from rediscovering repo context
that has already been settled. Read it before broad exploration.

The current controlling context is ChatGPT thread `Recursive CLI Orchestration`
(`online_thread_id = 6a0c3c4b-75d8-83ec-8288-f46aae8ab948`,
`canonical_thread_id = bea9942a90b13e7708702515fdf7a3c0ad8d93a4`). It selects
a recursive manager/worker tree for real Agda theorem progress toward the
Paper 7 terminal receipt. Paper 1 is the foundation surface; the current
objective is not Paper 1 submission polish but all-gate progression toward
publishable full-unification closure.

## Active Blocker Routing

Workers must choose one active blocker lane from
`Docs/CorePhysicsTheoremRoadmap.md`, `Docs/Papers2To7CriticalPathStatus.md`,
or `Docs/WorkerCoordinationBoard.md`. They must not reopen completed checklist
items unless a downstream blocker explicitly requires that module as its
assigned file surface. Application lanes are frozen unless they directly
construct one of the eight core gate objects.

## Active Objective

Run a bounded recursive theorem-implementation campaign toward Paper 7
publishability:

- root manager: Paper7Receipt orchestration, dependency ordering, validation,
  and promotion governance;
- section managers: up to six concurrent gate clusters covering Gates 1-8;
- workers: each section manager may launch up to six bounded workers;
- worker leaves: workers may not spawn descendants.

The success criterion is publishability progress for Paper 7: close gate
receipts where possible, replace missing proofs by exact typed blockers where
not possible, and keep terminal promotion false until every upstream gate and
authority boundary is actually inhabited or accepted.

## Current Focus

The six active manager lanes for the full-unification campaign are:

1. Gate 1/2 manager: carrier-to-physics functor plus S8 spectral witness.
   Close the nearest `Energy = Nat` / covariance / non-vacuum witness pieces,
   or return the exact first uninhabited law.
2. Gate 3 manager: nonabelian Yang--Mills. Extend finite Lie support toward
   `SU(3)`, forms, curvature, Hodge, Killing Ad-invariance, and IBP while
   preserving Route A / Route B separation.
3. Gate 4 manager: non-flat FactorVec GR. Push the p2-time valuation metric
   toward nondegeneracy, Lorentzian signature, inverse metric, Christoffels,
   Riemann/Ricci, contracted Bianchi, and stress-energy compatibility.
4. Gate 5 manager: Hilbert/Stone depth limit. Push finite-depth Hilbert spaces,
   isometric embeddings, traversal compatibility, colimit domain, and
   self-adjoint generator/domain data.
5. Gate 6 manager: DHR/AQFT. Construct concrete sector/lane semantics,
   localized endomorphisms, tensor/fusion, dual/braiding/hexagon surfaces, and
   DR/Tannaka authority boundary wiring.
6. Gate 7/8 manager: matter/Higgs/Yukawa/CKM plus final Paper7Receipt
   composition. Push concrete representation families, Higgs argmin, Yukawa
   matrices, splitting-field/CKM closure, cross-gate consistency, and terminal
   product receipt. Do not set `terminalClaimPromoted = true` unless all
   upstream gate receipts and authority boundaries are already present.

## Active Proof-Blocker Wave

The next tmux-backed manager wave must implement against the exact blockers
left by the wave6 implementation pass inside `ao-paper7-wave3`.  Reuse the
existing `ao-paper7-wave3` tmux session name for future cycles instead of
creating new session names.  A manager may return another audit only if it
first demonstrates that its assigned proof target cannot be locally advanced
without an upstream inhabitant and records that exact inhabitant by name.

1. Gate 1/2 manager: inhabit the global real-carrier
   `SelfAdjointYangMillsHamiltonianOnCarrierQuotient` theorem.  Wave6 made the
   post-vacuum queue explicit and advanced the bounded Nat-side focus to
   `s8NonVacuumSectorPredicateField`; the global real-carrier theorem
   inhabitant is still absent and no spectral-gap promotion is constructed.
2. Gate 3 manager: prove the all-slot coefficient-aware `SU(3)` Jacobi closure
   over the global coefficient-aware arithmetic carrier by supplying
   `nonRepresentativeSlotCoefficientTermSupplyField`, then all-slot residual
   arithmetic and all-slot zero-residual witnesses.  Wave6 decomposed the
   blocker into a typed field lattice; it did not prove all-slot closure.
3. Gate 4 manager: inhabit stress-energy tensor symmetry after the supported
   unit p2-time component-family map.  Wave6 supplied the zero component-family
   progress surface and advanced the next tensor-candidate blocker to
   `missingValuationStressEnergyTensorSymmetryLaw`; finite support,
   carrier-embedding compatibility, Einstein-source coupling, divergence
   compatibility, and global non-flat GR promotion remain open.
4. Gate 5 manager: inhabit global physical quotient inner-product
   well-definedness after the selected finite projection/scalar first-field
   progress.  Wave6 threaded `SelectedQuotientPostProjectionScalarSocket`;
   Hilbert completion, invertible traversal group, strong continuity,
   traversal-derived `StoneBundle`, and self-adjoint physical colimit generator
   data remain open.
5. Gate 6 manager: supply the arbitrary-sector lane classifier, then
   arbitrary-sector carrier predicates and arbitrary-sector global foreign-lane
   identity.  Wave6 added `dhrSectorLaneSupplyFromExplicitData` and
   `DHRArbitrarySectorForeignIdentityProgress`; DR/Tannaka closure remains
   open.
6. Gate 7/8 manager: continue the concrete up-Yukawa 3x3 carrier matrix from
   the next typed entry `y13`.  Wave6 added staged `y12` progress and threaded
   it into the CKM ledger, advancing the next missing up-entry to `y13`.
   Down-Yukawa data, CKM field closure, Yukawa-DHR intertwiner compatibility,
   W4 authority, and Gate 8 product composition remain open.

Every manager report for this wave must include changed files, targeted
validation commands, promotion state, remaining blockers, and a compact
`FORMAL MODEL: O, R, C, S, L, P, G, F` summary.  Workers spawned by managers
are leaves and must not spawn descendants.

## Constraints

- Do not treat setup, architecture, or audit as open work.
- Do not switch to broad documentation edits unless implementation actually
  changes and those docs must be synchronized.
- Do not use heavy aggregate validation as an inner-loop check.
- Do not use `PhysicsClosureValidationSummary.agda` as a routine target.
- Do not use full `Everything.agda` as a routine target.
- Do not set `terminalClaimPromoted = true`.
- Do not claim external authority boundaries discharged.
- Do not create new application-side surfaces during this campaign unless they
  directly discharge a Gate 1-8 Paper 7 obligation.
- Root may launch at most six section managers.
- Each section manager may launch at most six worker descendants when its lane
  claim explicitly authorizes it.
- Workers are leaves: they may not spawn further descendants.
- Descendants must use distinct `--orchestrator-id`,
  `--parent-orchestrator-id`, `--lane`, and `--lane-claim` values.

## Preferred Validation

Use targeted Agda checks on touched canonical modules. Representative targets:

- `DASHI/Physics/Closure/CarrierToPhysicsInterpretationFunctor.agda`
- `DASHI/Physics/Closure/PressureBelow15SpectralNatWitnessSlice.agda`
- `DASHI/Physics/Closure/YangMillsFieldEquationObstruction.agda`
- `DASHI/Physics/Closure/YangMillsFieldEquationReceipt.agda`
- `DASHI/Physics/Closure/FactorVecDiscreteMetricTensorSurface.agda`
- `DASHI/Quantum/Stone.agda`
- `DASHI/Physics/QFT/DHRTensorDualGroupReconstruction.agda`
- concrete Gate 7/8 receipt modules touched by the manager.

Only widen validation if the touched dependency chain requires it.

## Forbidden Or Bounded-Only Validation

- Do not run `DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda`
  as routine validation.
- Do not run full `DASHI/Everything.agda` as routine validation.
- Treat `DASHI/Physics/Closure/CanonicalStageC.agda` as bounded/checkpoint
  validation only, not a casual leaf check.
- If a targeted Agda command runs longer than expected without being an
  explicitly assigned checkpoint, stop it and report the risk instead of
  waiting indefinitely.

## Current Parallel Workstream Ownership

When multiple workers are active, keep file ownership disjoint:

- Gate 1/2 manager: carrier-to-physics functor and S8 spectral modules only.
- Gate 3 manager: Yang--Mills obstruction/receipt and finite Lie modules only.
- Gate 4 manager: FactorVec metric / GR candidate modules only.
- Gate 5 manager: Hilbert/Stone/depth traversal modules only.
- Gate 6 manager: DHR/AQFT reconstruction modules only.
- Gate 7/8 manager: matter/Higgs/Yukawa/CKM and Paper7Receipt composition
  modules only.
- Root manager:
  status files, `.autonomous-orchestrator` metadata, and final integration
  reporting only. It should not edit proof modules directly while section
  managers are active.

## Operating Rules For Autonomous Children

1. Read `plan.md`, the selected `status.<id>.json`, this file, and
   `Docs/CorePhysicsTheoremRoadmap.md`.
2. Select one concrete theorem/code target from the assigned lane only.
3. Inspect only the files needed for that target.
4. Make a concrete implementation move before broad repo searching.
5. Run targeted validation on the touched module chain.
6. Report changed files, validation, promotion state, and remaining gaps.
7. Update status/devlog/context only if real implementation progress occurred.

## Failure Pattern To Avoid

Bad loop:

- reread plan/status/context repeatedly
- run malformed `rg` searches
- rewrite docs without theorem/code advancement

Good loop:

- choose a single closure target
- inspect its local dependencies
- patch the theorem internals
- run targeted Agda checks
- record the concrete result
