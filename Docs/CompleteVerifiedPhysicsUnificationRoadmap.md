# Complete And Verified Physics Unification Roadmap

This roadmap plans the path from the current DASHI physics-facing program to a
publishable claim of:

> complete and verified physics unification

It does not assert that the target claim is true today. It defines the finite
promotion path that would make the claim defensible.

Roadmap maintenance state for the current wave: complete. This marks the
status-review tranche as finished, not the physics-unification target itself.

## Publication-Scope Definition: Papers 0-4

The finished and publishable "full unification" package for the current
publication programme means the ordered Paper 0-4 bundle recorded by
`DASHI.Physics.Closure.FullUnificationPublicationRoadmapReceipt`.  Older
G1-G7 lane gates remain useful as long-range theorem/validation gates, but they
are not a license to claim full unification unless the Paper 0-4 bundle below is
also coherent, receipt-backed, and fail-closed at every forbidden claim.

| Paper | Publishable scope | Required Agda alignment | Still forbidden |
|---|---|---|---|
| Paper 0 | Shared fail-closed margin grammar: dynamics bound, ratio/signed equivalence with `A > 0`, strict absorption rule, and non-promotion grammar. | `StrictMarginImpliesAbsorptionReceipt`, `FullUnificationPublicationRoadmapReceipt` | Treating the grammar as an NS theorem, YM theorem, Gate 3 theorem, Clay result, or terminal result. |
| Paper 1 | NS theta/EV5 programme: fixed-`K` tail flux bookkeeping, computable theta diagnostics, one-way continuation targets, and NS-to-EV5 forward-simulation obligations. | `NSTailFluxAbsorptionMarginReceipt`, `EV5ThetaMarginUpgradeReceipt`, `ClayNSProofRoadmapReceipt` | Claiming theta preservation, actual-flow tail decay, BKM/Serrin closure, unconditional NS regularity, arbitrary-data regularity, or Clay Navier-Stokes. |
| Paper 2 | Gate 3 cutoff-frame/density/Mosco programme: finite cutoff frame bounds `A_N > 0` on finite `H_N` plus the required continuum density, Mosco recovery, no-spectral-pollution, and mass-shell bridge targets. | `Gate3NormDictionaryReceipt`, `SpectralConvergenceGate3Receipt`, `FullUnificationPublicationRoadmapReceipt` | Treating a finite dictionary or finite frame bound as continuum density, norm-resolvent convergence, physical spectral identification, or Gate 3 promotion. |
| Paper 3 | YM rho/KP/Balaban programme: same-prime reduction, BT path counting, convergence threshold, strict absorption threshold, actual polymer activity gap, Balaban RG hard-open bridge, and rho `< 1` non-promotion. | `YMSamePrimeOverlapReductionReceipt`, `YMBTPathCountingKPThresholdReceipt`, `YMKPAbsorptionMarginThresholdReceipt`, `YMActualPolymerActivityDefinitionReceipt`, `YMBalabanRGScaleTransferFrontierReceipt`, `YMPaper3RoadmapReceipt`, `Paper3YMDependencyGraphReceipt`, `ClayYMProofRoadmapReceipt` | Claiming toy rho as actual activity, convergence as strict absorption, perturbative beta estimates as Balaban RG, carrier gaps as continuum gaps, continuum YM, mass gap, or Clay Yang-Mills. |
| Paper 4 | Full DASHI unification programme: compose Papers 0-3 only after their joining lemmas are coherent, then state the strongest supported unification claim with explicit limitations. | `FullUnificationPublicationRoadmapReceipt` and the Paper 0-3 receipts it lists | Claiming full unification, terminal closure, Clay closure, exact Standard Model/GRQFT closure, or empirical adequacy beyond accepted receipts. |

Promotion gates for this publication package remain the canonical gates named by
`canonicalPublicationPromotionGates`: diagnostic is not theorem; toy ratio is
not analytic margin; finite frame is not continuum density; observed margin is
not proved margin; carrier gap is not continuum gap.

The current publishable boundary is therefore Paper 0 as shared grammar plus
downstream Papers 1-4 as roadmap/obligation papers.  Full unification becomes
publishable only when Papers 1-3 have their analytic inhabitants and Paper 4
composes them without violating the forbidden-claim table above.

## Current State

Current status is recorded in `Docs/PhysicsLaneMaturityMatrix.md`:

| Lane | Current maturity |
|---|---|
| Maxwell / gauge-field regime | present, bridged, partially packaged; not theorem-complete; not empirically validated |
| Schrödinger evolution | present, bridged, packaged; not theorem-complete; not empirically validated |
| GR curvature / GR-QFT consumer | present, bridged, packaged; not theorem-complete; not empirically validated |
| Predictions / empirical adequacy | present, bridged, packaged; not theorem-complete; not empirically validated |

The target state requires all four lanes to become theorem-complete and
empirically validated, with cross-lane consistency proven through the same
canonical carrier/spine rather than asserted by analogy.

Current coordination state, as of 2026-05-13:

- `G1` is the only definitively closed gate.
- `G2` has a typed Maxwell field-equation obligation surface in
  `DASHI/Physics/Closure/MaxwellGaugeFieldEquationScope.agda`; it is not a
  Maxwell field-equation theorem.
- `G3` has a typed Schrodinger/Hamiltonian obligation surface in
  `DASHI/Physics/Closure/SchrodingerEvolutionScope.agda`; it is not a
  Schrodinger evolution theorem.
- `G4` has advanced bridge or partial-consumer surfaces, but it is not
  curvature- or Einstein-equation-complete.
- `G5` is not closed: W3 now has a frozen local candidate pass
  (`chi2/dof = 2.1565191176275618`) and local checksum binding, but no
  `W3AcceptedEvidenceAuthorityToken`; canonical HEPData table payload
  checksum binding is still absent after metadata discovery and HTTP `403`
  payload-download attempts. W4/W5 remain blocked on accepted Drell-Yan
  convention and authority.
- `G6` now has a typed skeleton in
  `DASHI/Physics/Closure/CrossLaneCommutingTheoremSkeleton.agda`, but it is
  `skeletonOnlyNoPromotion`; no concrete lane morphisms or section proofs are
  inhabited.
- `G7` has no publication audit package.

The plateau is explicit: remaining work is either an internal construction
that has not yet been assigned to a theorem owner, or an external receipt /
authority boundary that cannot be replaced by local prose.

## 2026-05-13 Novel-Math Route Intake

The latest route sketch from
`/home/c/Downloads/As you can see in the pumls there are many blocker(6).md`
is treated as a guarded tranche-6 route ledger, not as a promotion event.  It
changes the work queue only where the route can be re-expressed as a typed
obligation, candidate proof route, or concrete worker lane.

The paste contains paper-level language such as "proof complete" for G2, G3,
G4, G6, and W8.  This roadmap does not adopt those labels as gate state.  A
gate closes here only when the corresponding repo-local Agda inhabitant,
receipt, or accepted external authority exists.

### Tranche 6 Current-State Table

| Gate / work item | Current validated state | Tranche 6 treatment | Next proof surface |
|---|---|---|---|
| `G1` canonical spine | Closed. | Unchanged. | Preserve revalidation discipline for downstream edits. |
| `G2` Maxwell | Obligation surface only. | Candidate sector-restriction route via `U(1)` Killing-form/Yang-Mills restriction; not a Maxwell theorem. | Inhabit `SpineActionU1SectorRestriction`, current extraction, and field-equation law. |
| `G3` Schrodinger | Obligation surface only. | Candidate route via Kato-Rellich/Stone plus Inonu-Wigner contraction; not a Schrodinger theorem. | State and inhabit Hamiltonian, domain/self-adjointness, unitarity, and contraction interfaces. |
| `G4` GR | Advanced bridge/partial-consumer surfaces only. | Candidate E8 / `SO(2,3)` MacDowell-Mansouri route; not curvature or Einstein-equation closure. | Type structure-group constraint, vierbein/spin-connection carriers, action equivalence, and sourced-consumer obligations. |
| `G5` empirical adequacy | Not closed. W3 t43 has local candidate pass `chi2/dof = 2.1565191176275618` and artifact SHA `92b61032...`, but no `W3AcceptedEvidenceAuthorityToken`. | Unchanged: local pass remains non-authoritative because canonical HEPData table checksum/authority is absent after HTTP `403` payload attempts. | Obtain canonical table checksum equivalence or accepted authority token; keep DY and unit authorities separate. |
| `G6` cross-lane consistency | Skeleton only; no concrete section proofs. | Candidate W/G fixed-point, E8/G Ward, and GR/W perturbative-negligibility routes; not a commuting theorem. | Inhabit lane sections for G2, G3, G4, G5 and cross-path propositional equalities. |
| `W8` origin | Candidate rigidity route only; no origin receipt. | E8 semisimplicity/Whitehead rigidity route remains candidate-only and must preserve `U(1)`/reductive caveats. | State semisimplicity boundary, rigidity theorem, model-uniqueness/origin receipt, and authority boundary. |
| `W9` cancellation | Blocked. | Pseudo-Goldstone / de Sitter-scale ideas are problem-formulation candidates, not cancellation proof. | New vacuum-energy/hierarchy-pressure theorem route or durable obstruction. |

| Surface | Route-sketch value | Current repo status | Governance decision |
|---|---|---|---|
| E8 completeness | Coordinatewise exhaustion proof for integer and half-integer families. | Generators and executable no-duplicate/disjointness checks exist; structural propositional proofs and completeness remain open. | Continue LILA-R2 as an internal proof-bridge lane. |
| LILA-R3 | Restrict Lam-Tung claim to an electroweak sub-root-system / Ward-identity route rather than all roots. | Staged and gated on `E8RootEnumerationComplete`; no identity receipt. | Update staging to require an electroweak-frame/branching receipt before any Lam-Tung promotion. |
| LILA-R4/LILA-R5 | Ratio and E8-observable coherence routes are typed but externally/branching gated. | No denominator authority and no naturality proof. | Treat as request/scope surfaces only. |
| G2 Maxwell | Bianchi part is routine; sourced equation depends on a sector-restriction theorem for the spine action. | Obligation surface exists; sector restriction is not proved. | Add sector-restriction as the next G2 obligation, not as theorem closure. |
| G3 Schrodinger | Unitarity route through self-adjoint Hamiltonian and contraction to non-relativistic dynamics. | Obligation surface exists; Hamiltonian, self-adjointness/domain, unitarity, and contraction are not proved. | Add contraction/domain theorem candidates as obligations. |
| G4 GR | BF / MacDowell-Mansouri route addresses the `F^2` versus Einstein-Hilbert `R` mismatch if the spine structure group supports it. | No G4 scope module currently encodes this route. | Assign a G4 scope worker to type the structure-group and first-order-gravity obligations. |
| G6 | W/G fixed-point test, E8/G Ward route, GR/W perturbative-negligibility route. | Skeleton only; no concrete sections. | Add typed route candidates while preserving `skeletonOnlyNoPromotion`. |
| W5 t45 | Correction formula is constructible after accepted DY convention. | DY convention authority is absent. | Keep W5 blocked on DY convention. |
| W8 origin | E8 semisimplicity/rigidity route proposed. | W8 remains external/blocked in current request packs; no rigidity theorem. | Downgrade from "no route" to "candidate internal rigidity route", not to unblocked. |
| W9 cancellation | No credible cancellation/vacuum-energy route. | Still blocked. | Preserve W9 obstruction status. |

No row in this table constructs a receipt, token, theorem, gate closure, or
empirical promotion by itself.

## Strict Dependency Path To The Target Claim

The path from the current position to a publishable physics-unification claim
has three phases:

1. Internal construction.
2. Empirical contact.
3. Cross-lane closure and publication audit.

The sequence below is the governing roadmap. It supersedes older "fastest path"
language that treated W2, HEP-R54, or t43-only evidence as sufficient for a
complete-unification trajectory.

### Phase I: Internal Construction

These steps have no external authority dependency, but may still require new
DASHI mathematics.

#### I.1 HalfTrit Type Construction

Gate:
- LILA-R2 obstruction.

Required outputs:
- `HalfTrit : Set`.
- An embedding / doubled-coordinate bridge from the existing trit carrier.
- Duplicate-freedom and equality/decision lemmas sufficient for E8 root
  enumeration.

Reason:
- `DASHI.Algebra.Trit` currently exposes only `Trit` constructors. Without a
  half-integer trit coordinate, LILA-R2, LILA-R3, LILA-R5, and any
  `computedashiratio` route through E8 remain constructorless.

Exit:
- A typechecked half-trit carrier plus the local lemmas needed by
  `DASHI.Algebra.Trit.E8RootEnumeration`.

#### I.2 Matter / Stress-Energy Bridge

Gate:
- W4 matter/stress-energy interface.

Current status:
- `DASHI/Physics/Closure/W4MatterStressEnergyMDLInternalBridge.agda` provides
  an internal MDL/Lyapunov-to-stress-energy-shaped bridge, but it is
  adapter-needed, not a physical stress-energy promotion.

Required outputs:
- Energy-density adapter from the Lyapunov scalar `J`.
- Pressure adapter, including the Nat/rational carrier needed for a scoped
  `p = J / 3` statement if that isotropic form is retained.
- A conservation boundary that honestly distinguishes Lyapunov descent
  (`<=`) from divergence-free conservation or equality.

Exit:
- An inhabited W4 matter/stress-energy interface or a typed obstruction naming
  the exact missing adapter.

#### I.3 TSFVTritCalibrationLaw

Gate:
- Candidate256 physical calibration law.

Current status:
- `DASHI/Physics/Closure/TSFVCandidate256CalibrationLawDiagnostic.agda`
  constructs a LILA-R2-independent 3-adic diagnostic layer, but the full
  calibration law is not inhabited.

Required outputs:
- Candidate256 quotient involution `T`.
- Integer address for `Candidate256QuotientClass`.
- Proof that address negation and absolute value/3-adic valuation are
  compatible with the quotient.
- Calibration map through the 3-adic scale.
- Dimensional-invariance theorem.
- Nontrivial calibrated separation.
- Physical-unit authority boundary.

Exit:
- `TSFVTritCalibrationLaw` inhabited, or an exact typed obstruction.

#### I.4 LILA-R2 E8 Root Enumeration

Dependency:
- I.1 HalfTrit construction.

Required outputs:
- 240-root enumeration over the doubled-coordinate HalfTrit/E8 frame.
- Root-decision procedure.
- Duplicate-freedom and completeness theorem.

Exit:
- `LILA-R2Receipt : E8RootEnumerationComplete`.

#### I.5 LILA-R3 and LILA-R4

Dependency:
- I.4 E8 root enumeration.

Required outputs:
- LILA-R3: Lam-Tung as an E8/Clifford even-sum identity.
- LILA-R4: SHA-bound Lean citation boundary to
  `../dashi_lean4/MoonshineEarn.lean`, preserving the corrected sibling path.

Exit:
- `LILA-R3Receipt` and `LILA-R4Receipt`, with no cross-language proof imported
  as an Agda theorem unless an explicit trust boundary is provided.

#### I.6 LILA-R5 `computedashiratio`

Dependencies:
- I.3, I.4, and I.5.

Required output:
- A real DASHI predictor function that the empirical runner can consume, such
  as `computedashiratio : PhistarBin -> RationalApprox`.

Exit:
- The empirical runner can emit predicted values for the target tables instead
  of a placeholder / residual boundary.

#### I.7 GRQFT Partial Consumer Receipt

Dependencies:
- I.2 stress-energy adapter and I.3 calibration law for any physical-source
  claim.

Current status:
- `GRQFTConsumerNextObligationV2.agda` now supports partial internal consumer
  closure for spacetime, wave-state, spinor-adapter, and gauge-representation
  fields.

Required outputs:
- Keep the partial receipt explicitly partial.
- Add stress-energy only after I.2 supplies the required adapter.
- Keep curvature, sourced Einstein law, and interaction closure external- or
  theorem-gated until their receipts exist.

Exit:
- A publishable limited-recovery theorem only if the paper language says
  exactly which fields are recovered and which remain blocked.

### Phase II: Empirical Contact

These steps require accepted data, frozen artifacts, or external authority.

#### II.1 HEAD Freeze And W3 Comparison Law Execution

Gate:
- `W3AcceptedEvidenceAuthorityToken`.

Required outputs:
- Frozen predictor state at `3205d74` or an accepted replacement freeze.
- Projection artifact digest.
- Comparison-law execution against the named CMS/HEPData table and covariance
  source.
- `chi2/dof <= 4.0` if promotion is claimed.
- Non-collapse witness.
- Accepted authority route.

Exit:
- W3 accepted authority, or a residual boundary that records the exact missing
  field. Current local state is residual, not promoted.

#### II.2 Accepted DY Luminosity Convention Binding

Gate:
- `AcceptedDYLuminosityConventionAuthorityReceipt`.

Required outputs:
- Provider identity and role.
- PDF set/version, member, grid checksum, scale convention, rapidity window,
  mass-bin rule, flavour weights, and integration method.
- Luminosity values or route for W5 `L43` / `L45` and W4 per-bin `ell_i`.
- Efficiency/acceptance model.
- Systematic budget.
- CMS-SMP publication pointer.
- Normalization-preservation law.
- Conversion law.
- Source citation, no-manual-overfit attestation, accepted status, and external
  provenance.

Exit:
- W4/W5 runners can consume a convention packet without inventing any physics
  convention locally.

#### II.3 W4 Z-Peak Adequacy Test

Dependencies:
- II.2 accepted DY convention, plus I.6 if the runner needs the LILA/DASHI
  predictor path.

Current status:
- The current dirty Z-peak result is a typed obstruction with
  `chi2/dof = 298.8462841768543`.

Exit:
- `W4ZAdequacyReceipt` if the convention-bound run passes the typed threshold,
  or a negative obstruction naming the failing component.

#### II.4 W5 `t45` Correction

Dependencies:
- II.2 accepted DY convention and, if the target route is DASHI-native rather
  than external-PDF-only, I.6.

Required outputs:
- Accepted high-mass Drell-Yan ratio/correction run.
- Provenance-bound artifact.
- Pass/fail receipt against the target tolerance.

Exit:
- W5 correction receipt, or a typed negative obstruction preserving the PDF /
  convention gap.

#### II.5 W3 Extended Scope

Dependencies:
- II.1, II.3, and II.4.

Required outputs:
- One receipt per table / observable.
- One comparison-law result per receipt.
- One non-collapse witness per promoted empirical claim.

Exit:
- `G5` empirical prediction validation can close only after the empirical
  scope is accepted beyond a request or residual surface.

#### II.6 W8 Origin Receipt And W9 Pressure Witness

Status:
- Parallel completeness lanes for publication audit, not substitutes for G5.

Required outputs:
- W8 origin-adequacy bridge / accepted source receipt.
- W9 cancellation-pressure witness or accepted retarget route consumed by an
  actual kill constructor.

Exit:
- Publication-audit completeness improves; no empirical or unification gate is
  bypassed.

### Phase III: Cross-Lane Closure And Publication

#### III.1 W2 Natural P2 Bridge Or Final Obstruction

Gate:
- W2 kill condition.

Current status:
- `W2CanonicalPressureMetricP2BridgeOrObstruction.agda` decides the local
  offline-L2 candidate family as obstruction. The constructorless
  `NaturalP2ConvergencePromotionAuthorityToken` still blocks promotion.

Exit:
- A smaller-universe positive bridge, or an accepted obstruction receipt that
  the W2 kill route can consume.

#### III.2 Maxwell Gauge Field Equation Theorem

Gate:
- `MaxwellGaugeFieldEquationTheorem` or explicit scoped substitute.

Required outputs:
- Field-equation-level statement over the canonical gauge/matter carrier.
- Preservation/no-bypass laws.
- Boundary if only part of Maxwell recovery is derivable.

Exit:
- `G2` closes.

#### III.3 Schrodinger Evolution Theorem

Gate:
- `SchrodingerEvolutionTheorem` or explicit scoped substitute.

Required outputs:
- Hamiltonian/evolution carrier.
- Evolution theorem.
- Unitarity/conservation or typed limitation.

Exit:
- `G3` closes.

#### III.4 G6 Cross-Lane Commuting Theorem

Gate:
- Cross-lane commuting theorem over the common spine.

Current status:
- `CrossLaneCommutingTheoremSkeleton.agda` records the obligation shape:
  a canonical spine, four lane embeddings, four recovery morphisms, and four
  section proofs. The skeleton derives equality between lane round-trips only
  after the section proofs are supplied.

Required outputs:
- A diagrammatic square/cube connecting Maxwell, Schrodinger, GR, and
  empirical prediction lanes through one carrier.
- Compositional proofs that lane morphisms commute.
- No-bypass law separating theorem completion from empirical validation.

Exit:
- The program becomes one unification package rather than parallel recovered
  surfaces.

#### III.5 G7 Publication Boundary Audit

Gate:
- Reproducibility and claim-governance audit.

Required outputs:
- Theorem list with exact module names and validation commands.
- Maturity matrix with closed columns.
- Empirical receipt bundle with SHA-256 digests.
- Limitations section.
- Reproducibility script or equivalent validation target.

Exit:
- The target publication claim can be made at the strongest level supported by
  inhabited receipts.

## Complete Step Graph

```text
I.1 HalfTrit -> I.4 E8 roots -> I.5 Lam-Tung + ThetaJ -> I.6 computedashiratio
I.2 Stress-energy -> I.7 GRQFT partial
I.3 TSFVTritCalibrationLaw -> I.7 GRQFT partial

I.6 -> II.1 t43 clean run -> W3 authority decision
II.2 DY convention -> II.3 W4 Z-peak -> W4 decision
II.2 DY convention -> II.4 W5 t45 -> W5 decision
II.1 + II.3 + II.4 -> II.5 W3 extended scope -> G5 decision
II.6 W8 + W9 run in parallel for audit completeness

III.1 W2 bridge/obstruction finalisation
III.2 Maxwell theorem -> G2
III.3 Schrodinger theorem -> G3
I.7 + II.3 + later sourced-curvature work -> G4
G2 + G3 + G4 + G5 -> III.4 G6 cross-lane commuting theorem
G6 -> III.5 G7 publication audit
G7 -> target claim, bounded by the receipts actually inhabited
```

## Honest Distance

| Phase | Steps | Internal? | Blocking factor |
|---|---|---|---|
| I internal construction | I.1-I.7 | Yes | New DASHI constructions; no external receipts. |
| II empirical contact | II.1-II.6 | No | Frozen runs, CMS/HEPData/DY convention authority, and empirical receipts. |
| III cross-lane closure | III.1-III.5 | Mixed | G6 is genuinely new unification mathematics; G7 is audit/governance. |

There are approximately fourteen major sequential steps between the current
state and the target claim. Roughly half are internal construction or novel
mathematics; the rest require external receipts, frozen empirical artifacts, or
publication-governance evidence.

## Target Claim

The publishable target claim is:

> DASHI is a complete and verified physics unification: its canonical formal
> spine recovers the Maxwell/gauge, Schrödinger, GR-curvature/GR-QFT, and
> empirical-prediction regimes as theorem-complete lanes, and those lanes are
> externally validated by accepted empirical receipts.

This claim becomes admissible only when every gate below is closed.

## Promotion Gates

| Gate | Requirement | Evidence required |
|---|---|---|
| `G1` canonical spine stability | Current canonical proof spine remains unchanged or all changes are revalidated. | Targeted Agda on theorem owners and updated closure ledger. |
| `G2` Maxwell/gauge theorem completion | Static/bounded/interpretable gauge surfaces promote to a field-equation-level theorem or explicit equivalent theorem. | Named Agda theorem owner, law statement, preservation laws, no-bypass proof. |
| `G3` Schrödinger theorem completion | Bounded Euler/proxy Schrödinger consumers promote to an end-to-end Schrödinger evolution theorem or scoped equivalent. | Named Agda theorem owner, Hamiltonian/evolution carrier, conservation/unitarity or scoped substitute, boundary proof. |
| `G4` GR curvature theorem completion | Known-limits GR/QFT bridges promote to a richer curvature/stress-energy/interaction consumer theorem. | W5-owned closure receipts, curvature/stress-energy carriers, consumer laws, interaction closure. |
| `G5` empirical prediction validation | HEPData/residual and broader empirical lanes promote from candidates to accepted empirical adequacy. | Accepted authority route, calibration/covariance, projection, comparison law, conformance tests, empirical adequacy theorem. |
| `G6` cross-lane consistency | Maxwell/gauge, Schrödinger, GR, and prediction lanes commute through the same canonical carrier/spine. | Commuting diagram/theorem package plus consistency tests. |
| `G7` publication boundary audit | All docs, diagrams, theorem names, and limitations match the final claim. | Claim audit, reproducibility instructions, validation transcript, changelog. |

## Workstreams

### W-MAX: Maxwell / Gauge Completion

Goal:
- Promote the Maxwell/gauge lane from present/bridged/partially packaged to
  theorem-complete.

Required outputs:
- `MaxwellGaugeFieldEquationTheorem` or an explicitly scoped equivalent.
- Gauge/matter carrier and field-equation law.
- Preservation law tying the gauge lane to the canonical spine.
- Obstruction certificate if full Maxwell recovery is not attainable.

Exit condition:
- `Docs/PhysicsLaneMaturityMatrix.md` can mark Maxwell/gauge as
  `theorem-complete = yes`.

### W-SCH: Schrödinger Completion

Goal:
- Promote the Schrödinger lane from bounded/proxy packaging to a finished
  evolution theorem.

Required outputs:
- End-to-end Hamiltonian/evolution carrier.
- Theorem connecting the current dynamics package to Schrödinger-form evolution.
- Conservation/unitarity proof, or a named scoped substitute with explicit
  limits.
- Boundary statement distinguishing theorem from numerical/proxy update.

Exit condition:
- `Docs/PhysicsLaneMaturityMatrix.md` can mark Schrödinger as
  `theorem-complete = yes`.

### W-GR: GR Curvature / GR-QFT Completion

Coordination owner:
- `W5` on `Docs/WorkerCoordinationBoard.md`, currently tracked through
  `GRQFTConsumerNextObligation`, `GRQFTConsumerSourceDiagnostic`, and
  `GRQFTClosurePromotionReceiptRequestPack`.

Goal:
- Promote the GR/QFT consumer from known-limits bridge to richer downstream
  theorem.

Required outputs:
- Curvature, stress-energy, metric/spacetime, interaction-closure carriers.
- Consumer laws for the GR side and QFT interaction side.
- W5 closure-promotion receipts.
- Explicit boundary for regimes not covered.

Weakest sufficient metric-recovery target:
- A discrete metric/curvature candidate over the current known-limits geometry
  and GR bridge surfaces, with an explicit map from the discrete spacetime
  carrier to curvature data. This is only a candidate target; it is not an
  Einstein-equation theorem.
- A continuum-limit dependency on W2: the discrete candidate can only become a
  GR recovery route after W2 supplies a positive natural `p2`
  bridge/rate/continuum receipt over the admissible carrier family. If W2
  resolves as obstruction only, this route remains blocked unless a new
  mathematical ingredient replaces the current convergence path.
- A stress-energy/source dependency on W4: the curvature side cannot be
  coupled to a physical source term until W4 supplies calibrated physical
  units, scale-setting, and dimensional-preservation receipts. Existing W4
  surrogate or pre-physical surfaces are not source terms for GR recovery.
- A W5/PDF and empirical dependency: the GR/QFT request pack must still receive
  promotion authority, downstream consumer fields, GR/QFT laws, witnesses, PDF
  carrier prerequisite, and empirical validation before G4 can close.

Operational status:
- Near-term work is diagnostic only. The honest target is to name the discrete
  metric/curvature candidate and its receipt dependencies, not to prove metric
  recovery.
- Full GR metric recovery is years/open and gated at minimum on W2 continuum
  progress, W4 physical source calibration, W5/PDF closure intake, and later
  empirical validation.

Exit condition:
- `Docs/PhysicsLaneMaturityMatrix.md` can mark GR curvature / GR-QFT as
  `theorem-complete = yes`.

Current boundary:
- W5 ownership is coordination wiring only. It does not promote G4, does not
  construct the GR equation law, QFT interaction law, or empirical validation,
  and does not reclassify the known-limits consumer as theorem-complete.

### W-EMP: Empirical Prediction Validation

Goal:
- Promote empirical prediction from provider-intake/candidate surfaces to
  accepted empirical adequacy.

Required outputs:
- Accepted residual observable-class receipt for the HEPData path.
- Exact selected observable, checksum-bound selection, baseline/residual
  definition, non-collapse witness, calibration/covariance, projection,
  comparison-law, and accepted authority receipts.
- At least one empirical adequacy theorem over an accepted dataset.
- Reproducible validation script and fixed artifact digests.

Exit condition:
- `Docs/PhysicsLaneMaturityMatrix.md` can mark predictions / empirical adequacy
  as `empirically-validated = yes`.

### W-XLANE: Cross-Lane Unification Closure

Goal:
- Show the completed lanes are not isolated successes, but commute through one
  unified carrier/spine.

Required outputs:
- Cross-lane carrier compatibility theorem.
- Diagrammatic commuting square/cube connecting Maxwell/gauge, Schrödinger, GR,
  and prediction lanes.
- No-bypass law preventing empirical validation from substituting for theorem
  completion or theorem completion from substituting for empirical validation.

Exit condition:
- The target claim can be evaluated as one unified theorem/validation package,
  not four unrelated results.

## Target Publication Package

The final publication package must contain:

- theorem list with exact Agda module names and validation commands;
- maturity matrix with all target columns closed;
- empirical receipt bundle with authority route and digests;
- diagram set showing current-to-complete transition;
- limitations section for regimes not covered;
- reproducibility script or Make target that checks all theorem and empirical
  artifacts.

## Current Claim Boundary

Until every gate closes, the correct claim remains:

> DASHI has a verified internal spine and explicit physics-facing lanes, with a
> finite roadmap to complete and verified physics unification.

The current post-HEP-R53 empirical claim is narrower:

> DASHI has a bounded below-Z Drell-Yan phistar ratio result for the t43
> `50-76 / 76-106 GeV` lane: a formal carrier and no-free-parameter phistar
> ratio comparison with `chi2/dof = 2.1565191176`, plus runner-side
> non-collapse evidence. This is not complete physics unification, not full
> W3 accepted authority before HEP-R54, and not closure of the W2, W4, W5, or
> W9 gaps.

## Superseded Fastest Path After HEP-R54

Status:
- Historical / superseded by `Strict Dependency Path To The Target Claim`
  above.
- Kept for traceability because older coordination rounds and changelog entries
  cite this section.
- Do not use this section as the active promotion path.

The fastest path to a complete physics-unification claim is not the same as the
fastest path to a publishable phenomenology/formal-methods paper.

For a publishable bounded paper, the remaining high-value items are external
W3 accepted authority, W4 Z-peak/cross-band calibration support, and W7
governance. HEP-R53 and HEP-R54 already moved the t43 claim to a reproducible
non-collapse witness plus a typed first-missing authority-token gate.

For complete unification, the critical dependency is W2. The carry-field
obstruction target is now superseded by a positive invariant:
`normalizeAdd` preserves `lhs + rhs` and therefore preserves p-adic valuations
of that sum for every tracked prime by definitional equality. This opens the
right W2 route, but the governance kill condition still requires the
constructorless W2 promotion authority token and carrier-general
convergence-rate packaging before W2 can be marked closed.

The GR flat-space side also now has an exact receipt:
`MinkowskiLimitReceipt.agda` records the hyperbolic/Minkowski quadratic and the
B4 intrinsic `sig31` match. This is flat-space only. Curved-regime GR recovery
still requires a continuum field-equation argument plus W4 source coupling and
W5 GR/QFT/PDF receipts.

Current fastest-path order:

1. Package the W2 sum/p-adic invariant into the carrier-general convergence
   receipt surface and supply the W2 promotion authority token.
2. In parallel, keep the W5 PDF-carrier route external: the t45 log-ratio
   diagnostic is suggestive but not an internal PDF derivation.
3. In parallel, keep W6 runtime PNF intake provider-ready; this is smaller and
   does not gate W2, W4, W5, or GR recovery.
4. Keep the GR recovery target at the weakest honest level: a discrete
   metric/curvature candidate only, with continuum promotion gated by W2,
   stress-energy/source coupling gated by W4, and downstream GR/QFT/PDF
   promotion gated by W5 receipts.

This keeps the current claim honest: DASHI has a formally verified bounded
collider-observable result, but complete unification still requires W2,
W4 source calibration, W5/PDF, W6 runtime, and GR metric recovery.

After every gate closes, the target claim can become:

> DASHI is complete and verified physics unification.
