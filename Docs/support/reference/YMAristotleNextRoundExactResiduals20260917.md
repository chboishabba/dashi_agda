# Yang–Mills Aristotle exact residual brief — 2026-09-17 dense-L2 recut

## Authority and scope

This is the current bookkeeping surface for PR #996. It supersedes the older F1+F2+F3+F4 and trajectory-uniform-`c` formulations.

The proof-accounting distinction is strict:

```text
source authority
!= compiler theorem
!= physical inhabitant
!= empirical contact
```

The physical frontier remains

\[
\boxed{F_1+F_3+F_4}.
\]

Old F2 is not an independent payment. Isometric embeddings remain real data inside F3, but the checked varying-carrier compiler does not require separate Hamiltonian/vacuum-compatibility hypotheses as primitive inputs.

No unconditional Clay completion is claimed.

## Already paid — do not redo

### Literal finite Wilson theory

The retained Lean lattice development supplies the literal four-dimensional SU(2) Wilson/Gibbs carrier, gauge-invariant physical slice Hilbert space, transfer form, finite self-adjoint Hamiltonian, normalized zero-energy vacuum, and the finite coercivity-to-gap compiler.

The literal transfer operator is

\[
T=P_1^*P_0,
\]

with

\[
q(\psi,\psi)=\|\psi\|^2-\operatorname{Re}\langle T\psi,\psi\rangle.
\]

The continuum trajectory compiler consumes only

\[
\boxed{\Delta a_k\le 1-c_k},
\]

so `c_k -> 1` at `O(a_k)` is allowed. One trajectory-uniform `c<1` is stronger than required.

### Vacuum-sector spectral consequences

Use the existing `VacuumGapDatum` theorems for eigenvalue exclusion, vacuum-sector inversion and the `(Delta-lambda)^-1` resolvent bound. Do not rebuild them.

### Mosco / graph-limit / physical L2 infrastructure

The repository already owns serious typed infrastructure here:

- `BalabanVacuumOrthogonalMoscoRecoveryExact.VacuumOrthogonalRecoverySystem`;
- its vacuum-complement uniform-gap recovery theorem;
- the selected gauge-invariant physical `L2` carrier architecture;
- varying-carrier and graph-limit gap compilers;
- the Aristotle `Clay/MassGapAssembly` and literal `Lattice/ContinuumWeld` consumer shapes.

Therefore:

```text
MOSCO THEORY      != F3
L2 CONSTRUCTION   != F1/F3/F4
```

F3 is the **physical literal-Wilson instantiation** of the already-owned recovery/embedded-graph-limit interface.

The supplied Lean archive additionally proves that the generic direct-sum common carrier is degenerate for a nontrivial physical graph limit (`ymCanonicalCarrier_graphLimit_degenerate`). Generic carrier existence is not a substitute for the physical embedding family.

### OS reconstruction / generator machinery

The repository already owns continuum OS theorem surfaces, preferred physical OS reconstruction compilers, common-core generator uniqueness, and the Aristotle `OSWeld` consumer.

Therefore:

```text
OS RECONSTRUCTION != F4
```

F4 is the last-mile same-object identification of the already-available YM and OS dynamics on the physical common core.

---

# F1 — literal Wilson transfer defect on the actual continuum trajectory

The terminal payment is

\[
\exists\Delta>0\quad\forall k,n,\psi\perp\Omega_{n,k},
\]

\[
|\langle P_0\psi,P_1\psi\rangle|\le c_k\|\psi\|^2,
\qquad
\Delta a_k\le 1-c_k.
\]

The trajectory must be the same literal Wilson family used by F3.

## Four honest input normal forms

The finite-side compiler can now be targeted through:

```text
A. direct transfer-operator norm/decorrelator bound on physical L2_0

B. state-uniform connected/truncated two-slice correlation bound on all L2_0

C. full joint-slice density mixing
     d nu_01 / d(nu_0 x nu_1) = 1 + h,
     ||h||_infty <= eps

D. dense local/cylinder observable algebra bound
     D subset L2_0 dense
     + uniform connected-correlation bound on D
       -> full physical L2_0 decorrelator
```

`CorrelationCriterion.lean` supplies B -> A and C -> A on the literal Wilson slice measure.

## New dense-L2 bidirectional compiler

A new source-written Lean module was produced from the supplied 2026-09-17 Aristotle archive:

```text
RequestProject/YangMills/Lattice/DenseCorrelationCriterion.lean
```

with theorem targets:

```text
dense_vacuum_decorrelation_iff_full
truncated_correlation_eq_decorrelation
truncated_correlation_iff_decorrelation
decorrelation_of_dense_truncated_correlation
```

Its theorem grammar is:

\[
D\subset L^2_0,\;\overline D=L^2_0,
\]

\[
|\langle P_0\psi,P_1\psi\rangle|\le c\|\psi\|^2\quad(\psi\in D)
\iff
|\langle P_0\psi,P_1\psi\rangle|\le c\|\psi\|^2\quad(\psi\in L^2_0).
\]

On the vacuum complement the disconnected term vanishes, so the connected two-slice correlation equals the transfer pairing. Hence a uniform connected-correlation estimate on any dense physical local/cylinder algebra is enough for the existing F1 transfer compiler.

The proof strategy is ordinary functional analysis: both sides of the inequality are continuous on the closed vacuum complement; the inequality defines a closed set containing the dense test algebra.

**Validation boundary:** the file was written RED-first in the attached tree and the theorem names/static surface were checked, but this runtime has no Lean binary/dependency cache. No fresh Lean kernel receipt is claimed for this new file yet. The Agda bookkeeping owners are therefore conditional:

```text
YMClayDenseL2CorrelationBidiParityExact
YMClayDenseL2CorrelationBidiParityValidation
```

This compiler does **not** prove the physical dense-algebra correlation estimate.

## Consequence for native KP/Ursell machinery

The old ceiling was:

```text
pairwise/local observable correlation decay
  !=
full operator-strength bound over every psi in physical L2_0
```

The dense-L2 compiler removes the need to jump directly to a global `L^infty` density ratio. The source-side question can instead be:

```text
choose a natural dense gauge-invariant local/cylinder algebra D subset L2_0
+
prove a uniform connected two-slice correlation estimate on D
+
prove D is dense in the selected physical vacuum complement
```

then use the new compiler to extend to all `L2_0`.

The remaining nontrivial source payment is therefore potentially much more native to cluster/polymer/RG machinery.

## Current CMP116 source-native producer

The canonical current localization cut remains R338/R339:

```text
R338 CanonicalCommonDomainCMP116Source
R339 CanonicalSelectedT5CMP116Application
  -> R339.canonicalApplicationBuildsR320Payment
  -> R320.localizeBaseDirectlyAsR295
  -> R295.DirectT5StateFamilyJPresentation
```

`YMClayF1CanonicalSourceApplicationExact` records this compiler. R346 remains a weaker alternate presentation but still stores proof-bearing physical localization/time-distance fields.

Do not rebuild the older R318 presentation pair or the lower R406--R409 replay unless needed for provenance/source reconstruction.

## Bałaban 1989 complete-density same-trajectory route

The current repository owns the same-beta-history lane

```text
Balaban1989BetaSplitInverseSquareTerminalHistoryExact
  -> Balaban1989BetaDrivenCompleteDensityFlowExact
  -> Balaban1989BetaHistoryToCanonicalCompleteDensityExact
```

so the effective-density `couplingAt` is the same coupling history produced by the finite beta trajectory; the small-coupling condition is not being imported on a parallel trajectory.

The imported Bałaban 1989 CMP 122 theorem (DOI `10.1007/BF01238433`) preserves the Section-2 complete-density form/bounds under sufficiently small effective coupling. The repository dictionary currently compiles those data to `InYM4RGInvariantRegion`, not definitionally to a positive physical mass floor or full transfer mixing.

The preferred next source theorem is now weaker than the old full-density target:

```text
same beta-driven CMP119/CMP122 complete-density state
    -> identify a natural dense local/cylinder algebra in physical L2_0
    -> uniform adjacent-slice connected-correlation bound on that algebra
    -> dense-L2 compiler
    -> full transfer decorrelator
    -> F1
```

The stronger route remains valid:

```text
same complete-density state
    -> literal adjacent-slice joint law
    -> d nu_01 / d(nu_0 x nu_1) - 1 in L-infinity
    -> full L2_0 decorrelator
```

but the `L^infty` density defect is no longer a primitive logical requirement of the F1 compiler.

---

# F3 — physical literal-Wilson continuum-limit instantiation

F3 is now stated narrowly:

```text
literal Wilson cutoff physical L2 spaces
+ nondegenerate physical isometric embeddings
+ actual embedded vacuum-sector graph/Mosco limit
+ continuum Hamiltonian/vacuum
+ self-adjoint/domain/unit-vacuum/ground-state data
```

This is an instantiation problem for machinery already present in both Agda and the supplied Lean development, not a request to redevelop Mosco convergence.

`VacuumOrthogonalRecoverySystem` and the Aristotle `EmbeddedContinuumLimit` / `IsEmbeddedVacuumGraphLimit` interfaces are the canonical consumer shapes.

No synthetic/common-carrier witness counts as F3 unless it is tied to the literal Wilson trajectory and is nondegenerate in the physical limit.

---

# F4 — physical YM/OS same-object weld

F4 is now stated narrowly as

\[
\boxed{U_t^{YM}=U_t^{OS}}
\]

for the actual continuum theory, together with the common-core/generator witnesses consumed by existing uniqueness machinery.

The supplied Lean development already contains:

```text
Clay.OSWeld
GeneratorUniquenessCore.generator_unique_of_evolution_eq
GaugeInvariantL2Carrier.hamiltonian_eqOn_core_of_same_evolution
```

and bounded-core special cases.

Do not discharge F4 using a reflexive synthetic `OSWeld.self`, by naming both evolutions equal after the fact, or by substituting Schwinger-family naming for a theorem identifying the physical dynamics.

---

# Empirical contact — CMS-SMP-20-003

The orthogonal empirical axis remains:

```text
CMS-SMP-20-003 / CERN-EP-2022-053
DOI 10.1140/epjc/s10052-023-11631-7
HEPData ins2079374/t43 + covariance t44
50--76 GeV / 76--106 GeV ratio
chi2 = 38.8173441173
effective dof = 18
chi2/dof = 2.1565191176
mean prediction/data = 0.9941233097
freeze commit = 3205d746639568762c9e97adf4a3672c356bd491
```

`YMClayCMSDrellYanEmpiricalContactBoundaryExact` pins that this is bounded collider/QCD empirical contact and pays none of F1/F3/F4.

---

# Current acceptance surface

The focused Agda rollup now includes:

```text
YMClayVaryingCarrierTransportParityExact
YMClayUniformGapReductionParityExact
YMClayCorrelationCriterionParityExact
YMClayDenseL2CorrelationBidiParityExact
YMClayDenseL2CorrelationBidiParityValidation
YMClayUrsellTransferMixingBoundaryExact
YMClayF1MixingSourceAuditExact
YMClayCompleteDensityTransferMixingBoundaryExact
YMClayCMSDrellYanEmpiricalContactBoundaryExact
YMClayF134ContinuumWeldParityExact
YMClayF1CanonicalSourceApplicationExact
YMClayClosedWorldResidualAudit20260917Exact
YMClayOutstandingPhysicalFrontierExact
```

`OutstandingPhysicalFrontier` still has exactly F1/F3/F4. The dense-L2 theorem **weakens the admissible F1 producer shape**; it does not silently construct the physical source estimate.

## Verification boundary

Before a completion claim:

1. run `lake build RequestProject` on the exact Lean head containing `DenseCorrelationCriterion.lean` and any eventual physical inhabitants;
2. report `#print axioms` for the new headline Lean theorems;
3. typecheck the focused Agda parity/root on the exact branch head;
4. reject `sorry`, `axiom`, `postulate`, `@[implemented_by]`, trust escapes or unresolved metas in the new proof tranche;
5. report remaining F1/F3/F4 hypotheses verbatim.

Until those checks are observed, the new dense-L2 compiler is **source-written / conditional**, not freshly kernel-certified.

## Closed-world audit note

`YMClayClosedWorldResidualAudit20260917Exact` is diagnostic bookkeeping about a searched repository state, not a theorem of global nonexistence and not proof currency.
