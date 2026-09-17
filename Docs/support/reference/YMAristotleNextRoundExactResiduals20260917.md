# Yang–Mills Aristotle exact residual brief — 2026-09-17 transfer-operator recut

## Authority and scope

This brief supersedes the earlier F1+F2+F3+F4 cut and the intermediate trajectory-uniform-`c` formulation on PR #996.

The supplied Aristotle Lean tranches report `lake build RequestProject` GREEN. The earlier varying-carrier return reported 8220 jobs, zero errors and zero warnings, with no `sorry`, `axiom`, `postulate`, or `@[implemented_by]` in the new material and headline `#print axioms` containing only `propext`, `Classical.choice`, and `Quot.sound`. The later transfer-operator/frontier and correlation-criterion returns likewise report green RequestProject builds. These are donor Lean receipts, not Agda kernel receipts and not physical F1/F3/F4 inhabitants.

The current physical normal form remains

\[
\boxed{F_1+F_3+F_4}.
\]

Old F2 is no longer an independent research payment. Isometric cutoff embeddings remain real data inside F3, but separate Hamiltonian-compatibility and vacuum-compatibility hypotheses are not primitive inputs to the checked varying-carrier transport theorem.

A separate empirical axis is also retained. The existing CMS-SMP-20-003 / HEPData t43+t44 receipt is a bounded collider contact with the QCD-facing observable surface. It is not an F1, F3 or F4 payment and is not used as a proof premise for the Clay theorem.

No citation, status flag, synthetic model, source receipt, empirical fit, or assumption record renamed as a theorem counts as a physical payment.

## Already paid — do not redo

### Literal finite SU(2) Wilson theory

The retained Lean lattice chain constructs the literal Wilson/Gibbs probability measure, gauge-invariant physical Hilbert carrier, rescaled transfer form

\[
q_a=a^{-1}\left(1-\tfrac12(T+T^*)\right),
\]

self-adjoint finite Hamiltonian and normalized zero-energy vacuum. `Lattice.lattice_massGap_of_coercivity` compiles literal coercivity to the finite mass-gap conclusion.

The fixed-spacing sufficient strong-coupling theorem `Lattice.ym_phys_massGap_of_coupling_le` remains useful but is not a continuum-trajectory theorem; its hypothesis `64 |beta| (n+1)^4 <= 1/10` tightens in the wrong direction as the volume grows.

### Vacuum-sector spectral consequences

Use the checked `VacuumGapDatum` theorems:

- `VacuumGapDatum.eigenvalue_eq_zero_of_lt_gap`;
- `VacuumGapDatum.exists_unique_solution_vacuumSector`;
- `VacuumGapDatum.resolvent_bound_vacuumSector`.

Do not rebuild eigenvalue exclusion, vacuum-sector inversion, or the `(Delta-lambda)^-1` resolvent estimate.

### Varying Hilbert carriers — old F2 paid structurally

Use `RequestProject/YangMills/VaryingCarrierTransport.lean`.

For cutoff Hilbert spaces `E_k`, a common carrier `E` and linear isometric embeddings

```text
J_k : E_k -> E
```

are sufficient for the checked varying-carrier gap transport. The cutoff gap hypothesis lives intrinsically in `E_k`; separate Hamiltonian intertwining, vacuum compatibility and domain preservation are therefore not primitive F2 hypotheses.

The fixed-carrier theorem is recovered as the identity-embedding special case, and the donor contains a non-vacuity witness with genuinely cutoff-dependent carrier types. `CommonCarrier.lean` also shows that a generic common carrier can always be constructed while warning that the canonical direct-sum embeddings need not realize the physical continuum limit. Embedding existence is therefore not the physical F3 graph-limit theorem.

### Literal continuum weld

Use `RequestProject/YangMills/Lattice/ContinuumWeld.lean` and `RequestProject/YangMills/Lattice/FrontierF1F3F4.lean`.

The checked endpoint has the shape

```text
literal Wilson positive trajectory gap
+ isometric embeddings
+ embedded vacuum-sector graph limit
+ continuum Hamiltonian/vacuum data
-----------------------------------
continuum mass-gap conclusion

and, for the OS endpoint:
+ same YM/OS evolution on a common core
---------------------------------------
Clay.MassGapConclusion H_OS Omega Delta
```

No auxiliary or synthetic Hamiltonian is inserted.

### Transfer-operator / uniform-gap reduction

Use:

```text
RequestProject/YangMills/Lattice/TransferOperatorGap.lean
RequestProject/YangMills/Lattice/UniformGapReduction.lean
RequestProject/YangMills/Lattice/CorrelationCriterion.lean
```

The literal Euclidean transfer operator is

\[
T=P_1^*P_0,
\]

and the donor records the literal energy-form identity

\[
q(\psi,\psi)=\|\psi\|^2-\operatorname{Re}\langle T\psi,\psi\rangle.
\]

The finite payment may be expressed as the two-slice correlation bound, contractivity on the vacuum complement, or the equivalent phase-separation statement `decorrelation_iff_phase_separated`.

`CorrelationCriterion.lean` adds two sufficient normal forms on the literal slice measure:

```text
state-uniform truncated two-slice correlation bound
    -> transfer decorrelator bound

joint two-slice density = (1+h) * product of marginals, ||h||_infty <= eps
    -> transfer decorrelator bound with c = eps
```

The disconnected contribution vanishes for vacuum-orthogonal states. These are compiler theorems from a mixing input to the transfer payment; they do not prove the interacting Wilson mixing input.

Most importantly, the continuum trajectory does **not** require one constant `c<1` uniform in `k`. The checked trajectory compiler consumes only

\[
\boxed{\Delta a_k\le 1-c_k}.
\]

Thus `c_k -> 1` is allowed at rate `O(a_k)`. The older stronger condition with one trajectory-uniform `c` is sufficient but not primitive.

The donor still proves `c=0` at zero coupling for every volume. This shows unbounded volume by itself is not the obstruction; it does not prove the interacting physical trajectory `beta(a) -> infinity`.

### Native KP / Ursell assembly and its exact ceiling

The repository already contains machine-checked finite Kotecký–Preiss geometric arithmetic and the finite-tail/Cauchy assembly in `BalabanTraceKoteckyPreissGeometricExact` and `BalabanClayT2UrsellCauchyExact`.

Those owners can compile a supplied physical Ursell/tree-graph majorant into pairwise observable connected-correlation decay. They do **not** automatically produce the operator-strength statement

```text
sup over every psi ⟂ Omega in physical L2
```

or an `L^infty` Radon–Nikodym defect for the complete two-slice law. `YMClayUrsellTransferMixingBoundaryExact` therefore keeps the observable-to-uniform-mixing upgrade explicit.

---

# F1 — literal Wilson transfer defect on the actual continuum trajectory

The preferred terminal target is now

\[
\exists\Delta>0\quad\forall k,n,\psi\perp\Omega_{n,k},
\]

\[
|\langle P_0\psi,P_1\psi\rangle|\le c_k\|\psi\|^2,
\qquad
\Delta a_k\le 1-c_k.
\]

The trajectory must be the same literal Wilson family used by F3, including the selected `n -> infinity`, `a -> 0`, `beta(a) -> infinity` normalization.

## Existing non-dominated producers

1. **Direct literal transfer-operator route** via `TransferOperatorGap` / `UniformGapReduction`.
2. **Uniform two-slice mixing route** via `CorrelationCriterion`: either state-uniform truncated correlation or a full joint-slice density defect implies the transfer decorrelator.
3. **R387/CMP116 covariance route**: merged #987 already compiles a genuine `R387.DirectSelectedSpectralUpper` plus one-sided limit closure and positivity to `PositiveTransferGapCore`; do not rebuild R410 or the historical factor-by-factor terminal stack.
4. **P33/Hessian route** can provide finite coercivity and Combes–Thomas inputs but still needs structure-specific Stage-II gap transport; finite Hessian coercivity is not itself the trajectory transfer defect.

## Current source-native CMP116 cut

The earlier R318 presentation

```text
PublishedTwoJLocalizationForBase
SelectedBaseJApplicability
```

is a valid **general external-presentation adapter**, but it is not the least-privilege proof-search frontier. Its arbitrary source magnitude/root/distance representation charges presentation equalities that later source-native work already eliminated.

The canonical current cut is:

```text
R338 CanonicalCommonDomainCMP116Source
  - differentiatedLocalizationOnCanonicalCommonDomain
  - source magnitude/root/distance/envelope on the canonical common domain

R339 CanonicalSelectedT5CMP116Application
  - sourceMagnitudeIsSelectedMagnitude
  - sourceEnvelopeBelowSelectedRootedShell
```

and PR #996 contains the direct compiler

```text
R338 + R339
  -> R339.canonicalApplicationBuildsR320Payment
  -> R320.localizeBaseDirectlyAsR295
  -> R295.DirectT5StateFamilyJPresentation
```

in `YMClayF1CanonicalSourceApplicationExact.agda`.

This removes the old R318 magnitude/root/distance presentation pair from the primitive frontier. It does **not** manufacture the remaining physical/source theorems.

Closed-world search finds no concrete `CanonicalCommonDomainCMP116Source` inhabitant on the selected physical base and no concrete `CanonicalSelectedT5CMP116Application` inhabitant. The source theorem authority is CMP116 Sect. 1 / (1.23)--(1.36), DOI `10.1007/BF01239022`; the DOI and `standardImported` classification do not perform the local Agda source-carrier alignment. The R339 physical application remains exactly the selected response same-object identity plus source-envelope calibration.

The later selected-spectral R346 route removes still more presentation structure, but its `literalSelectedDifferentiatedLocalization` and `selectedPhysicalDistanceIsTime` fields remain proof-bearing physical inputs. It therefore remains an alternate producer, not an unconditional F1 payment.

The lower R406--R409 replay remains useful provenance/optional source reconstruction. Its exact remaining attachments include `SingleChangedFourStageAgreement` and `differentiatedTermAbsoluteIsOperatorDifferenceNorm`; they are not mandatory terminal architecture after the R338/R339 recut.

## Balaban 1989 complete-density same-trajectory route

The current repository also has a stronger same-object RG bookkeeping lane:

```text
Balaban1989BetaSplitInverseSquareTerminalHistoryExact
  -> Balaban1989BetaDrivenCompleteDensityFlowExact
  -> Balaban1989BetaHistoryToCanonicalCompleteDensityExact
```

The important positive result is that the source `Balaban1989EffectiveDensityFlow.couplingAt` is definitionally the same coupling history produced by the finite beta trajectory, and the small-effective-coupling condition is derived from that history rather than supplied on a parallel RG path.

The imported source theorem is Bałaban 1989 CMP 122 Theorem 1, DOI `10.1007/BF01238433`: under sufficiently small positive effective couplings, the effective densities preserve the Section-2 density form and satisfy the Section-2 conditions/bounds. The repository transport from the source theorem into its canonical state is machine-owned once the source theorem witness and dictionary are supplied.

This strengthens the upstream F1 route but does **not** yet identify a Section-2 density bound with the exact full-slice mixing condition required by `CorrelationCriterion`. The next useful bridge is therefore:

```text
same beta-driven CMP119/CMP122 complete-density state
    -> literal two-slice joint law / density ratio
    -> uniform defect bound strong enough for all vacuum-orthogonal L2 states
```

or, alternatively, a complete-basis/operator-norm theorem upgrading the existing observable correlation family to the transfer-operator norm.

`YMClayF1MixingSourceAuditExact` deliberately blocks the inference

```text
cluster/polymer convergence => required 4d SU(2) two-slice L∞ density defect
```

unless that strengthening is actually sourced/proved.

---

# F3 — embedded literal-Wilson continuum limit

F3 owns the embedding family because that is where it is consumed.

Required physical output:

```text
isometric embeddings of each literal cutoff carrier
+ actual embedded vacuum-sector graph/Mosco limit
+ actual continuum Hamiltonian and vacuum
+ self-adjointness/domain/vacuum normalization and ground-state data
```

The Agda semantic cross-check remains `BalabanVacuumOrthogonalMoscoRecoveryExact.VacuumOrthogonalRecoverySystem`. The generic recovery theorem is paid. Sprint129 Boolean/evidence receipts do **not** instantiate that record.

The Round124–131 measure/Schwinger/stress lane is valuable same-family infrastructure, but its `literalFiniteMeasuresConverge` and OS/literal-Schwinger weld are stored as physical fields. Measure convergence is not silently promoted to Hamiltonian graph convergence.

Exact closed-world search finds no physical literal-Wilson inhabitant of `VacuumOrthogonalRecoverySystem`, no concrete assignment to `literalFiniteMeasuresConverge`, and no accessible Lean branch containing an additional physical graph-limit instantiation. Aristotle's varying-carrier theorem pays transport once the graph-limit input exists; it does not manufacture that input.

---

# F4 — actual YM/OS same evolution

The decisive physical theorem remains

\[
\boxed{U^{YM}_{\infty}=U^{OS}}
\]

on the actual theory and a common invariant core.

Use the existing generator-uniqueness / same-evolution compilers after this equality is proved. Do not use a reflexive `OSWeld.self`, define both evolutions to be equal post hoc, or substitute Round127 Schwinger-family naming for an evolution theorem.

The repository's common-core Ward/generator compiler is downstream machinery. Exact search on current master finds no concrete constructor of `commonCoreActionEquality`, no assignment to `YMOSSameObjectWitness.evolutionsEqual`, and no later `sameEvolution` physical inhabitant. Round127's Schwinger-family weld is a distinct obligation and itself has no concrete source-to-literal Schwinger inhabitant on current master.

---

# Empirical contact — CMS-SMP-20-003 (orthogonal evidence axis)

The repository contains a literal frozen empirical contact in `DASHI/Physics/Closure/HEPDataCMSBelowZDrellYanClaimExact.agda` and `HEPDataW3ComparisonLawReceipt.agda`:

```text
CMS-SMP-20-003 / CERN-EP-2022-053
DOI 10.1140/epjc/s10052-023-11631-7
HEPData ins2079374/t43, covariance t44
50--76 GeV / 76--106 GeV Drell--Yan ratio
chi2 = 38.8173441173
effective dof = 18
chi2/dof = 2.1565191176
mean prediction/data = 0.9941233097
freeze commit = 3205d746639568762c9e97adf4a3672c356bd491
```

The t43 comparison passes the repository's bounded W3 criterion `chi2/dof < 4` and mean-ratio interval `[0.97,1.03]`. Agda checks the typed receipt, source binding, digests and promotion boundary; the floating-point covariance statistic is an external byte-replayable calculation rather than an Agda re-computation.

`YMClayCMSDrellYanEmpiricalContactBoundaryExact` brings this result into the YM focused ledger and pins:

```text
bounded collider/QCD empirical contact = true
pays F1 = false
pays F3 = false
pays F4 = false
proves zero fitted parameters = false
proves whole canonical spine = false
```

This is useful empirical contact with the QCD observable surface. It is not evidence that can replace the constructive continuum proof obligations.

---

# Current exact acceptance surface

Agda PR #996 now records:

```text
YMClayVaryingCarrierTransportParityExact
YMClayUniformGapReductionParityExact
YMClayCorrelationCriterionParityExact
YMClayUrsellTransferMixingBoundaryExact
YMClayF1MixingSourceAuditExact
YMClayCMSDrellYanEmpiricalContactBoundaryExact
YMClayF134ContinuumWeldParityExact
YMClayF1CanonicalSourceApplicationExact
YMClayClosedWorldResidualAudit20260917Exact
YMClayOutstandingPhysicalFrontierExact
```

and `OutstandingPhysicalFrontier` contains only:

```text
f1LiteralWilsonUniformGap   -- now per-step Delta*a_k <= 1-c_k semantics
f3PhysicalContinuumLimit
f4YMOSSameObject
```

with the embedding family nested in F3. `f2PrimitiveResearchPayment = false`, `f1TrajectoryUniformCRequired = false`, and `f1PerStepTransferDefectForm = true` are pinned by construction.

The final Lean acceptance theorem remains schematically

```lean
theorem clayYangMillsMassGap_unconditional :
  RequestProject.YangMills.Clay.MassGapConclusion H_OS Omega Delta
```

for the actual continuum theory. It may be claimed only after actual F1/F3/F4 inhabitants are supplied; the checked `ContinuumWeld` / `FrontierF1F3F4` compilers then perform the remaining transport.

## Verification gate

Before a completion claim:

1. `lake build RequestProject` exits 0 on the exact Lean head containing the final physical inhabitants.
2. The focused Agda parity/root typechecks on its exact head.
3. No `sorry`, `axiom`, `postulate`, `@[implemented_by]`, trust escape, or unresolved meta appears in the new proof tranche.
4. `#print axioms` is reported for each Lean headline theorem.
5. Exact theorem names and remaining hypotheses are reported verbatim. If F1, F3 or F4 remains a physical hypothesis, do not call the Clay theorem unconditional.

## Closed-world audit note

`YMClayClosedWorldResidualAudit20260917Exact` records only the searched repository state. Its Bool/status values are diagnostic evidence about that search and are never used as mathematical proof terms. The audit is intentionally weaker than a theorem of global nonexistence.
