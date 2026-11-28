# Paper 3 Draft: Yang–Mills Mass-Gap Reduction on the Literal Wilson Family

Author: Johl Brown
Date: `2026-06-09`
Version: `draft 1`
Status: live analytic manuscript draft; Clay-facing candidate preprint; non-promoting

## Abstract

This manuscript presents a **conditional** mass-gap reduction for the original four-dimensional SU(2) Wilson–Gibbs family, whose proof compiler takes three distinct, genuinely physical inputs `F1`, `F3`, and `F4`. Fixed-lattice identities, finite reflection/transfer algebra, changing-carrier spectral compilers and exact finite block encodings are *donors*, not proofs of those physical inputs. The final continuum/mass-gap theorem, its nontriviality and the extension from SU(2) to all compact simple gauge groups remain open. The surviving physical obligations in this particular route are:

```text
F1  a positive transfer defect on the interacting Wilson continuum trajectory;
F3  an actual embedded vacuum-sector graph/Mosco limit for the same Wilson family;
F4  equality of the resulting Yang–Mills and Osterwalder–Schrader evolutions
    on the physical common core.
```

Finite Gate 3 geometry still matters, but only as setup for the operator and
Hamiltonian language. The paper is no longer a geometry-first draft. It is a
mass-gap reduction draft with explicit claim boundaries.

> **Theorem 1.1 (conditional same-source mass-gap assembly).** Fix the
> original interacting four-dimensional SU(2) Wilson–Gibbs cutoff family and
> its physical time/slice observables. Suppose **(F1)** a physically sourced,
> cutoff- and volume-uniform vacuum-orthogonal two-slice transfer estimate
> holds along its continuum trajectory with a positive gap in physical
> units; **(F3)** the *same* cutoff theory possesses the required nontrivial
> reflection-positive/OS continuum and a physical embedded graph/Mosco
> limit preserving that uniform gap; and **(F4)** the limiting Yang–Mills
> and OS reconstructed evolutions agree on the same dense invariant core.
> Then the stated spectral-gap compiler produces a positive gap for that
> reconstructed physical Hamiltonian. These are explicit **premises**, not
> physical inputs proved by finite F19/R445 encoding, finite RG algebra,
> abstract transfer estimates or a citation. The SU(2) statement alone
> does not prove the full compact-simple-group Clay target.

This is the honest current target. The draft can state a finite-to-continuum
assembly route sharply while keeping the constructive multiscale intake
explicitly cited rather than silently internalized.

**November 21, 2026 original Wilson-source audit.** The newer
F19/R445 source-weld program does not supersede the physical assumptions in
Theorem 1.1. On the actual 4D side-four finite torus it accounts for **1,024
fine oriented-positive links** as **128 selected links plus 896 spectators**
(and 64 native blocked coarse links). The original Wilson weight depends on
the spectator links: changing one unselected SU(2) link from `I` to
`-I` leaves the blocked selected links unchanged but flips six original
plaquette traces, changing their sum by 24. Consequently **no** function of
those blocked coarse links alone equals the original interacting fine action.
The correct F19 weighted coarse expectation must integrate over the
spectator fibres with the **original** 1,024-link Gibbs weight. Finite label,
parity, Haar or weighted-pushforward equalities cannot establish cutoff-uniform
Wilson covariance bounds, continuum OS existence, a gap on every nonvacuum
sector of the same physical Hamiltonian, nontriviality or all compact simple
groups. The relevant Agda #1536 source-written adapters still require native
kernel validation. Source/physical controlling owner:
`Docs/roadmaps/ClayYMProofRoadmap.md` on Agda PR #1536; historical
R445/F19/CMP numbers refer to iterative proof attempts, not separate theorem
milestones.

**Formal status box.** In the Agda closure surfaces, the main Clay-facing
Yang-Mills theorems remain `Proved = false` because DASHI does not claim to
have locally reproved the full Balaban/OS constructive package. The manuscript
is a candidate preprint package whose internal receipts identify the finite
operator, transfer-interface, and terminal-guard surfaces. The external
constructive-QFT intake remains explicit and reviewable; no Clay approval,
external acceptance, or terminal promotion is asserted.

**Proof scope summary.**

| Manuscript surface | Role | Boundary |
| --- | --- | --- |
| finite carrier gap | proves the fixed-lattice operator/gap surface | not a continuum physical mass gap |
| uniform finite margin | carries domination input into the transfer problem | conditional on the stated domination package |
| `H3a` transfer | load-bearing continuum intake | cited Balaban/RG authority, not repo-native rederivation |
| `H3b` and no spectral pollution | vacuum compatibility and gap preservation | depends on RP.4 and the stated norm-resolvent strength |
| RP/OS reconstruction | Hilbert-space and Wightman bridge | subject to OS/Seiler compatibility and external review |

For the abstract closure grammar that places this reduction inside the wider
corpus, see Paper 8, *Closure Grammar, Jordan-von Neumann Recovery, and
Controlled Consumers*. The present paper remains the analytic home of the
Yang-Mills reduction narrative.

## 2. Finite nonabelian carrier and operator setup

The finite starting point is a selected family of nonabelian carriers for a
compact simple Lie group `G`, equipped with curvature, Wilson-action
bookkeeping, and a transfer or Hamiltonian operator at each depth. The older
finite geometry draft supplies the structural language: Lie brackets,
curvature witnesses, and selected finite non-flat surfaces. In the present
manuscript these are used only to justify the existence and domain of the
operator family `H_N`.

The Hilbert-space operator language used here is developed in detail in the
support compendium, Section 2, following Paper 4.

What matters analytically is that each `H_N` acts on a finite carrier Hilbert
space or transfer-matrix space with a distinguished vacuum sector and an
orthogonal positive-energy complement. The finite objects are real data, but
they are not yet the continuum Yang-Mills Hamiltonian. This distinction drives
the whole paper.

## 3. Finite self-adjointness and explicit spectral gap

The first theorem-sized step is finite self-adjointness. On each carrier, the
selected operator `H_N` is symmetric on its canonical finite domain and closes
to a self-adjoint operator. This gives meaning to the spectral minimum and to
gap statements of the form

```text
Delta * a_k <= 1 - c_k,
```

so no trajectory-uniform constant `c < 1` is required. A state-uniform truncated two-slice correlation bound supplies the same decorrelator, and a still-stronger uniform joint-slice density estimate

```text
d nu_01 / d (nu_0 x nu_1) = 1 + h_k,
||h_k||_infty <= c_k
```

is sufficient as well. The manuscript distinguishes these checked compiler implications from the still-open interacting physical estimate itself.

The Bałaban renormalization-group literature is used at its verified source ceiling. In particular, the repository now identifies the finite beta history with the coupling history of Bałaban's complete-density flow and imports the conditional 1989 ultraviolet-stability theorem on that same trajectory. This is a substantive same-object reduction, but it does not by itself prove the full two-slice `L^infty` density defect or the operator-strength `L^2` mixing estimate required for `F1`.

**Section 3 status.** The displayed `SU(2)` bound is finite-volume and
fixed-`beta`. It is not asserted to be uniform as `a(beta) -> 0` and
`beta -> infinity`. The continuum physical mass-gap burden begins only when
Sections 4-5 supply a uniform finite margin and the `H3a` transfer theorem
preserves that margin through the scaling limit.

## 4. Hamiltonian domination and uniform finite spectral margin

The paper therefore makes a reduction claim, not an unconditional Clay-completion claim.

## 1. Current theorem grammar

The previous draft organized the continuum burden around a single `H3a` trace-norm transfer theorem. That formulation was useful as a sufficient route, but the newer literal transfer-operator analysis is both weaker and more exact. The current theorem grammar is

```text
literal finite Wilson theory
    + F1 interacting transfer defect
    + F3 physical embedded continuum limit
    + F4 YM/OS same-object evolution
    -> continuum OS mass-gap conclusion.
```

Old `F2`, a separate common-carrier/compatibility obligation, is no longer primitive. A common carrier with linear isometric embeddings can be constructed for arbitrary cutoff Hilbert spaces, and the varying-carrier gap theorem needs no separate Hamiltonian/vacuum intertwining hypothesis. The embeddings remain genuine data inside `F3`, because the choice along which the physical graph limit occurs cannot be replaced by an arbitrary direct-sum embedding.

The final checked Lean endpoint is represented by the `FrontierF1F3F4` / `ContinuumWeld` theorem family. Schematically:

```text
F1 + F3
  -> continuum mass-gap conclusion on the limiting YM Hamiltonian

F1 + F3 + F4
  -> Osterwalder-Schrader mass-gap conclusion on the same physical theory.
```

No auxiliary Hamiltonian is inserted into this endpoint.

### 1.1 Claim boundary

The paper does **not** claim that the physical inhabitants of `F1`, `F3`, and `F4` have all been constructed. It claims that the surrounding compiler architecture has been reduced far enough that these are now the surviving physical payments.

The distinction used throughout is:

```text
source theorem authority
!= source-to-repository same-object alignment
!= machine-checked compiler theorem
!= physical inhabitant
!= empirical contact.
```

A citation does not manufacture a theorem term; a theorem compiler does not manufacture its physical hypothesis; and an empirical fit does not become a constructive continuum proof.

## 2. Literal finite Wilson theory

The finite starting object is the literal four-dimensional SU(2) Wilson/Gibbs family, with gauge-invariant physical Hilbert carrier, normalized vacuum, transfer form, and finite Hamiltonian. In the Lean donor formalization the rescaled energy form is

\[
q_a(\psi,\psi)=a^{-1}\left(\|\psi\|^2-
\operatorname{Re}\langle T\psi,\psi\rangle\right),
\]

where the literal Euclidean transfer operator is

\[
T=P_1^*P_0.
\]

Here `P0` and `P1` are the two slice embeddings of the same Wilson–Gibbs measure. The finite operator is contractive, preserves the vacuum, and the form-to-Hamiltonian infrastructure supplies a self-adjoint finite Hamiltonian with zero-energy vacuum.

There are also fixed-spacing sufficient gap theorems. They are useful non-vacuity checks, but a fixed-spacing strong-coupling condition is not the continuum problem: the physical trajectory simultaneously changes lattice spacing, coupling and volume. The continuum burden is therefore not the existence of *some* finite gap, but a positive physical gap scale that survives the selected `a -> 0`, `beta(a) -> infinity`, volume-growth trajectory.

## 3. F1: the interacting transfer defect

The most economical surviving finite-side physical target is

\[
\exists\Delta>0\;\forall k,n,\psi\perp\Omega_{n,k},
\]

\[
|\langle P_0\psi,P_1\psi\rangle|
\le c_k\|\psi\|^2,
\qquad
\Delta a_k\le 1-c_k.
\]

The second inequality is the important sharpening. The continuum argument does **not** require one constant `c < 1` independent of cutoff. The permitted defect may shrink linearly with lattice spacing. In particular, `c_k -> 1` is compatible with a fixed positive `Delta` provided

```text
1 - c_k >= Delta * a_k.
```

The stronger old uniform-`c` formulation remains sufficient but is not the primitive target.

### 3.1 Three normal forms for F1

The literal transfer analysis exposes three useful ways to pay the same finite-side debt.

#### A. Direct transfer defect

Prove the two-slice bound for every vacuum-orthogonal state and the per-step defect inequality directly. This is the closest form to the final Hamiltonian gap compiler.

#### B. State-uniform truncated correlation

For a vacuum-orthogonal state the disconnected product of one-slice expectations vanishes. Therefore a bound on the connected two-slice correlation supplies the same transfer estimate:

```text
|Corr_c(psi at slice 0, psi at slice 1)|
    <= c_k ||psi||^2
        ->
|<P0 psi, P1 psi>| <= c_k ||psi||^2.
```

This is formalized in `RequestProject/YangMills/Lattice/CorrelationCriterion.lean` as `decorrelation_of_truncated_correlation`.

#### C. Uniform joint-slice density mixing

A stronger sufficient condition is to identify the two-slice joint law relative to the product of its marginals:

\[
\frac{d\nu_{01}}{d(\nu_0\otimes\nu_1)}=1+h_k,
\qquad \|h_k\|_\infty\le \varepsilon_k.
\]

Then every vacuum-orthogonal `L^2` state satisfies the decorrelation estimate with `c_k = eps_k`. This implication is formalized as `decorrelation_of_uniform_joint_density`.

This third form is attractive because it removes operators from the physical input and presents `F1` as a classical mixing statement about the literal Wilson measure. It is also deliberately strong. Polymer convergence or pairwise local-observable clustering cannot be silently relabelled as this full `L^infty` density defect.

### 3.2 Zero coupling and non-vacuity

At zero coupling the two slices factor and the decorrelation constant is zero, uniformly in volume. This establishes that volume growth alone is not the obstruction. The unresolved issue is the interacting continuum trajectory, not the logical consistency of the transfer criterion.

## 4. What the native KP/Ursell machinery already gives

The repository already contains substantial constructive machinery around polymer counting and connected correlations.

`BalabanTraceKoteckyPreissGeometricExact` owns the finite geometric summability arithmetic. `BalabanClayT2UrsellCauchyExact` owns a machine-checked passage from a supplied physical Ursell/tree-graph majorant to a finite-tail estimate and then to pairwise observable connected-correlation decay.

This is real progress, but there is a type-strength distinction that matters:

```text
for selected/local observables A,B:
    |<AB> - <A><B>| <= decaying envelope
```

is not automatically the same theorem as

```text
sup_{psi ⟂ Omega}
    |<P0 psi,P1 psi>| / ||psi||^2 <= c_k.
```

The latter is an operator-norm statement over the full physical `L^2` vacuum complement. The current formal boundary therefore exposes two honest upgrade routes:

1. construct the full two-slice Radon–Nikodym/mixing estimate of Section 3.1C; or
2. construct a complete-basis/density theorem and an operator-norm extension taking the observable family to all physical `L^2` states.

Until one of these is paid, pairwise Ursell decay is not promoted to `F1`.

## 5. Bałaban RG and the complete-density same-object route

The source picture is now sharper than in the previous draft. Three Bałaban papers play distinct roles:

- *Renormalization Group Approach to Lattice Gauge Field Theories. I.* (CMP 109, 1987), DOI `10.1007/BF01215223`;
- *Convergent Renormalization Expansions for Lattice Gauge Theories* (CMP 119, 1988), DOI `10.1007/BF01217741`;
- *Large Field Renormalization. II. Localization, Exponentiation, and Bounds for the R Operation* (CMP 122, 1989), DOI `10.1007/BF01238433`.

The current Agda lane no longer treats the source RG flow as a parallel trajectory. `Balaban1989BetaDrivenCompleteDensityFlowExact` constructs a source effective-density flow whose `couplingAt` is definitionally the same coupling history produced by the finite beta calculation. Its small-effective-coupling field is derived from that beta history.

`Balaban1989BetaHistoryToCanonicalCompleteDensityExact` then makes the running coupling of the canonical repository state definitionally the same beta-history coupling. This removes a significant same-object ambiguity: the beta estimate and the imported complete-density theorem now concern the same trajectory coordinate.

### 5.1 Exact source ceiling of the 1989 theorem

The repository imports Bałaban 1989 Theorem 1 conservatively. Under sufficiently small positive effective couplings, the effective densities remain in the Section-2 density class and satisfy the Section-2 conditions and bounds. The source owner also records the important caveat immediately following that theorem: the stronger result removing the effective-coupling-smallness assumption relied on a lengthy second-order perturbative calculation whose proof was not published there. The formalization therefore does not import that stronger statement.

This source theorem pays a UV-stability/complete-density preservation step. It does **not**, merely by its name or by polymer convergence, state the full literal two-slice density theorem required by Section 3.1C.

The remaining source-to-F1 bridge is thus concrete:

```text
same beta-driven CMP119/CMP122 complete-density state
    -> identify the literal adjacent-slice joint law and marginals
    -> obtain a quantitative density or state-uniform connected-correlation bound
    -> prove Delta * a_k <= 1 - c_k
    -> F1.
```

A proof that the Section-2 bounds control precisely this density ratio would be high-value. A source citation that only establishes local polymer convergence or selected correlation decay is not enough.

### 5.2 CMP116 alternate route

A second non-dominated path reaches the finite gap through selected source localization rather than full-slice mixing. The canonical source-native cut uses R338/R339:

```text
CanonicalCommonDomainCMP116Source
+ CanonicalSelectedT5CMP116Application
    -> direct selected marked decay payment
    -> localized T5 carrier
    -> existing spectral-gap compiler.
```

The lower-level R346 selected-spectral route removes arbitrary source-root/source-distance presentation, but still requires literal selected differentiated localization and the equality between selected physical support distance and Euclidean time. This remains a genuine alternate F1 producer; neither route is currently identified with the full-slice mixing route.

## 6. F3: the physical embedded continuum limit

The old common-carrier obligation has been recut into the correct place. Embeddings are data of `F3`, because the physical graph/Mosco limit is defined along them.

The surviving F3 payment consists of:

```text
literal cutoff Hilbert spaces
+ selected linear isometric embeddings
+ continuum Hamiltonian and vacuum
+ actual embedded vacuum-sector graph/Mosco recovery
+ self-adjoint/domain/vacuum data
```

The repository already contains generic recovery machinery, including `BalabanVacuumOrthogonalMoscoRecoveryExact.VacuumOrthogonalRecoverySystem`, and the Lean donor contains the varying-carrier transport theorem. These compilers preserve a uniform intrinsic cutoff gap once the physical embedded graph-limit input exists. They do not construct that input.

This distinction is essential. An abstract direct-sum carrier always exists, but its canonical embeddings need not approximate any nonzero common limit. The relevant embeddings are therefore part of the physical continuum construction, not a bookkeeping nuisance.

## 7. F4: Yang–Mills = Osterwalder–Schrader evolution

The final same-object theorem is

\[
U^{YM}_{\infty}=U^{OS}
\]

on the actual physical theory and a common invariant core.

Once this equality is available, the existing common-core/generator uniqueness machinery transports the vacuum-gap datum to the OS reconstructed Hamiltonian. But equality may not be obtained by defining both evolutions to be the same function post hoc, by reflexivity on a synthetic carrier, or by identifying Schwinger-family names. It is a physical same-object theorem.

The present closed-world repository audit finds the generic compiler but no physical inhabitant of the decisive common-core action/evolution equality. `F4` therefore remains explicit.

## 8. Continuum mass-gap assembly

The current assembly theorem should be read schematically as follows.

> **Theorem 8.1 (conditional literal-Wilson mass-gap assembly).** Let the literal finite SU(2) Wilson family be the finite theory described above. Assume:
>
> 1. `F1`: there exists `Delta > 0` and cutoff-dependent `c_k` satisfying the literal vacuum-orthogonal two-slice estimate and `Delta a_k <= 1-c_k` along the physical continuum trajectory;
> 2. `F3`: the same literal Wilson cutoff family admits the selected physical embeddings and an actual embedded vacuum-sector graph/Mosco limit to a continuum Hamiltonian/vacuum pair;
> 3. `F4`: the resulting Yang–Mills evolution equals the Osterwalder–Schrader evolution on the physical common invariant core.
>
> Then the checked finite-gap, varying-carrier, continuum-gap and same-evolution compilers yield the positive mass-gap conclusion for the reconstructed OS Hamiltonian.

This theorem is conditional until the three physical premises are inhabited. It is not weakened by stating those premises explicitly; rather, the purpose of the current proof search is to make them as small, literal, and non-duplicative as possible.

The precise theorem-intake chain is the following. Balaban's block-spin
renormalization group (`Balaban1987`) supplies the passage to a scale where
the fluctuation integral is controlled and the effective action is localized. The
large-field/small-field decomposition suppresses the complementary region.
Most importantly for the `H3a` norm, the Balaban 1988 cluster expansion
(`Balaban1988`, Lemma 3 and equations (2.11)-(2.13), with the activity bound
recorded there as (2.38)) gives exponentially decaying polymer activities:

```text
|H(Z)| <= C exp(-c d(Z)).
```

Consequently the polymer sums for boundary-touching and large-diameter
polymers are absolutely summable. On the vacuum-orthogonal sector the
nontrivial representation blocks also carry the heat-kernel Casimir
suppression

```text
sum_{lambda != 0} d_lambda^2 exp(-a C_lambda) < infinity,
```

for the compact groups under consideration. The combination of polymer
summability and Casimir suppression is the cited input that upgrades strong or
Mosco-style convergence to the trace-norm transfer conclusion of Theorem 5.2.
This is an authority-backed theorem import, not a repo-native proof of
Balaban's multiscale estimates.

The repo-native alternative is explicitly deferred. A companion Option-B
paper would have to reprove, for the specific DASHI lattice families, the
Casimir suppression, polymer localization, Kotecky-Preiss activity bound,
trace-norm consequence, and intermediate-`beta` RG induction. Until that
separate proof exists, Theorem 5.2 remains authority-backed by the Balaban
intake above.

The reviewer-facing packet is now organized around the same exact chain. The
finite self-adjointness and domination layers are internal to this manuscript.
The remaining cited chain is:
`H3a -> H3b -> no-spectral-pollution -> RP/OS -> Wightman -> continuum mass-gap transfer`.
The packet surfaces are useful because they tell the reviewer exactly which
steps are local and which steps remain explicit authority intake. They do not
convert the cited constructive route into a repo-native proof.

The proof frontier above should be distinguished from an older empirical-contact lane that is already present in the repository.

The source measurement is the CMS Collaboration's 2023 analysis *Measurement of the mass dependence of the transverse momentum of lepton pairs in Drell–Yan production in proton–proton collisions at sqrt(s)=13 TeV*, EPJC 83, 628, DOI `10.1140/epjc/s10052-023-11631-7`, analysis code `CMS-SMP-20-003` / `CERN-EP-2022-053`. The measurement uses 13 TeV proton–proton data and presents ratios of mass-window differential distributions relative to the Z-peak window so that systematic uncertainties partially cancel.

**Seiler compatibility note.** The transfer theorem of this section is used to
place the limiting theory on the path toward the standard
Osterwalder-Schrader/Wightman framework built in Section 6. Any comparison to
Seiler's continuum mass-gap conclusions requires an additional compatibility
check between the constructed limiting objects and the hypotheses of the
continuum gauge-theory theorem being cited; it is not automatic from finite
transfer alone.

### 5.2 H3b: vacuum projection continuity

```text
chi2                 = 38.8173441173
effective dof         = 18
chi2/dof              = 2.1565191176
mean prediction/data  = 0.9941233097
freeze commit         = 3205d746639568762c9e97adf4a3672c356bd491
```

Logical-order note. RP.4 is established in Section 6. Lemma 5.3 is stated here
to keep the continuum-transfer interface in one place; its proof is downstream
of the reflection-positive vacuum construction.

> **Lemma 5.3 (`H3b` from `H3a` and RP.4).** Assume Theorem 5.2 and suppose the
> limiting Euclidean theory reconstructed in Section 6 yields a unique vacuum
> vector `Omega` with positive Hamiltonian gap above the vacuum. Then the finite
> vacuum projectors converge to the limiting vacuum projector in operator norm:
>
> ```text
> || P_N^Omega - P_infinity^Omega ||_op -> 0.
> ```
>
> Consequently the finite and limiting vacuum-orthogonal sectors are
> canonically compatible for the purposes of Theorem 5.1.

This result is scientifically interesting because it demonstrates contact with a literal collider observable on QCD data. It is **not** used as evidence for the constructive mass-gap theorem. The formal boundary pins:

```text
CMS empirical contact present                     true
CMS contact pays F1                               false
CMS contact pays F3                               false
CMS contact pays F4                               false
zero fitted parameters proved                     false
whole canonical theory spine proved               false
```

The empirical and constructive axes can therefore be reported together without confusing validation with proof.

## 10. Current proof-search priorities

The highest-information next questions are now narrow.

### 10.1 F1 / complete-density-to-mixing bridge

Inspect Bałaban's Section-2 complete-density bounds and the exact repository dictionary to determine whether they control the adjacent-slice joint density strongly enough to derive either:

```text
|| d nu_01 / d(nu_0 x nu_1) - 1 ||_infty <= c_k
```

or the weaker-but-sufficient state-uniform truncated-correlation operator bound. If not, expose the missing source/analytic theorem explicitly rather than treating generic cluster convergence as sufficient.

### 10.2 F3 / graph-limit inhabitant

Construct the actual literal-Wilson recovery system, including the selected embeddings, continuum Hamiltonian/vacuum, and embedded vacuum-sector graph/Mosco limit. Existing measure/Schwinger/stress convergence infrastructure should be reused only where it proves the same required object.

## 7. Final mass-gap assembly and claim boundary

The primary focused status surfaces for the 2026-09-17 recut are:

```text
DASHI/Physics/YangMills/YMClayUniformGapReductionParityExact.agda
DASHI/Physics/YangMills/YMClayCorrelationCriterionParityExact.agda
DASHI/Physics/YangMills/YMClayUrsellTransferMixingBoundaryExact.agda
DASHI/Physics/YangMills/YMClayF1MixingSourceAuditExact.agda
DASHI/Physics/YangMills/YMClayF1CanonicalSourceApplicationExact.agda
DASHI/Physics/YangMills/YMClayF134ContinuumWeldParityExact.agda
DASHI/Physics/YangMills/YMClayOutstandingPhysicalFrontierExact.agda
DASHI/Physics/YangMills/YMClayClosedWorldResidualAudit20260917Exact.agda
DASHI/Physics/YangMills/YMClayCMSDrellYanEmpiricalContactBoundaryExact.agda
```

The exact residual brief is `Docs/support/reference/YMAristotleNextRoundExactResiduals20260917.md`.

The paper-facing theorem-variable manifests remain formal-support indices rather than proof substitutes. No terminal `Proved`, `SubmissionReady`, Clay-approval, or external-acceptance status is inferred from a receipt, imported authority, empirical fit, or source-written branch state.

## Appendix A. Formal-support appendix

The paper-facing theorem-variable manifest is generated by
`scripts/generate_paper_proof_manifest.py` and recorded at
`Docs/papers/generated/core_papers_theorem_var_manifest.md`. For Paper 3 it
indexes the normalized theorem interface
`DASHI/Papers/YangMills/TheoremInterface.agda` and the associated finite,
transfer, reflection-positivity, and terminal-guard surfaces. The manifest is a
formal-support index: it records which Agda/DASHI names are intended to back
the manuscript interfaces, but it is not a substitute for the analytic
continuum argument or for external review of the cited constructive inputs.

## Appendix B. Claim boundary table

| Surface | Paid / available | Still open |
| --- | --- | --- |
| Section 3 identifies the finite self-adjointness and explicit fixed-lattice gap surface. | Character-expansion and constructive lattice-gauge background are cited through `Balaban1988` where used as context. | Any inference that a fixed-lattice finite gap is already the continuum physical mass gap. |
| Section 4 isolates the uniform finite spectral-margin target conditional on domination. | Balaban/KP-style domination and polymer estimates are cited as the external constructive stress-test surface. | A repo-native first-principles proof of the full domination package in the exact strength consumed here. |
| Theorem 5.1 states the corrected `H3a`/`H3b` continuum-transfer interface; Theorem 5.2 packages `H3a` from cited multiscale inputs. | The Balaban block-spin/effective-action, fluctuation-integral, large-field/small-field decomposition, and interacting reflection-positive continuum inputs used in the transfer theorem (`Balaban1987`, `Balaban1988`, and surrounding cited constructive work). | Any claim that DASHI has internally rederived the full Balaban multiscale transfer theorem. |
| Lemma 5.3 derives vacuum-projection continuity from `H3a` and RP.4; Theorem 5.4 derives no spectral pollution below the finite margin. | The existence and compatibility of the reconstructed limiting vacuum are consumed through the RP/OS route. | Spectral-pollution exclusion without the stated norm-resolvent or vacuum-compatibility hypotheses. |
| Section 6 records the RP.1-RP.4 reconstruction bridge and the Seiler-compatibility boundary; Theorem 7.1 packages the final mass-gap assembly. | Osterwalder-Schrader reconstruction (`OS1973`, `OS1975`), continuum gauge-theory authority boundaries (`Seiler1982`), and asymptotic-freedom background (`GrossWilczek1973`, `Politzer1973`). | Referee/community acceptance, Clay eligibility review, or any terminal claim beyond the candidate proof package stated here. |


## 23 November 2026 — YM P0 direct master-native CMP102 finite signed-parity specialization

On master-based [#1536](https://github.com/chboishabba/dashi_agda/pull/1536), added `DASHI/Physics/YangMills/YMClayCMP102NativeMasterSignedParitySpecializationExact.agda` (**source-written, Agda kernel NOT run**). It directly specializes the EXISTING `BishopUnsignedFactorialCauchyParitySplitExact.unsignedEvenExponentialCoefficientSuccessor` on the original Bishop exponential at x=1, y=-1 and composes `BishopExponentialSetoidCongruenceExact.expTermCongruent` with `BishopExponentialPositiveOrderExact.expTermZeroAtPositive`. The result `originalSignedEvenOddRowZero` establishes the **all-degree positive-even plus negative-odd original exponential Cauchy row cancellation** (at degree 2n+2) without any new finite parity algorithm. Existing finite Cauchy left/right series, endpoint ownership and original Bishop carrier retained. Local independent Python Fraction checker confirms 128/128 degrees n=0..127; this is not a kernel receipt.

**Exact gate separation:** the donor does NOT by itself inhabit older research PR #1444's `BalabanCMP102BishopShiftedCoefficientExact.signedEvenRow ≃ evenPart` or `signedOddRow ≃ -(oddPart)` because those CMP109 A/B shifted-index definitions do not exist on this #1536 tree. Reconcile against original #1444 branch and then specialize the master proven-index donor at the original source coefficients using exact Fin/Bishop bridge. Keep n=0 singleton and last even endpoint. Do not port the four master donor modules blindly into the deeply divergent research branch; on #1536 they are already imported. Kernel acceptance remains OPEN on both branches. In parallel, YM **physical** P0.T same Wilson/F19/CMP119/122 constrained T source, P0.W3 absolute marked rooted shell and cutoff/volume beta(a)-uniform rate, and P0.OS same interacting H remain OPEN. Source original Wilson/Haar, Bałaban and Murray/Csimma attribution maintained; no CI, no new postulate, no physical radius weakening, no Clay completion.


## 23 November 2026 — P0 direct CMP102 original A/B unit-source Cauchy weld (master #1536)

**Exact new source / no parallel factorial engine:** `DASHI/Physics/YangMills/YMClayCMP102MasterPositiveABCoefficientSourceWeldExact.agda` on master-based #1536 builds on existing `YMClayCMP102NativeMasterSignedParitySpecializationExact.originalSignedEvenOddRowZero`, original `BishopUnsignedFactorialCauchyParitySplitExact`, `BishopSignTwistedFiniteCauchyCoefficientExact.rowCauchyCoefficientRespectsTerms`, original `BalabanBishopConcreteSineCosineTermParityExact.evenPowerNegation/oddPowerNegation`, `BishopRound11SignedFactorialExponentEncodingExact` and the actual source inverse-factorial constructor `BalabanClayGate4BishopHalfRadiusRealEstimatesExact.inverseFactorialRational`. It source-writes the direct all-k unit-sign identities `negativeUnitEvenTermIsPositive`, `negativeUnitOddTermIsNegative`, *original shifted CMP109 formula* attachments `masterEvenShiftIsOriginalCMP109A` and `masterOddShiftIsOriginalCMP109B` (no second aSeries/bSeries carrier), the two original finite Cauchy row congruences and `originalPositiveEvenAndSignedOddRowsCancel` for ALL natural n as an Agda **source-written** composition. The two original master row definitions retain their exact Fin(suc n) support and negative odd sign.

**ACTUALLY LOCAL EXACT reference:** `scripts/check_ym_cmp102_master_positive_row_weld_20261123.py` was run locally under Python `fractions.Fraction` for n=0..127, with 17,536/17,536 exact checks: 8,384 negative-unit even term signs, 8,256 odd signs, 128 each original A shift, B shift, even-row sign, odd-row sign, total original exponential cancellation, original shifted G coefficient, and missing-even-endpoint negative control. Executed local file Git blob `3d72c989c7bb0580818d0380e0e216fe29b10aa2` was checked byte-identical to the GitHub-created blob. **Finite arithmetic does not typecheck or prove the whole Agda module**.

**Exact remaining P0 CMP102:** master source identities establish original positive EVEN / signed ODD *full* Cauchy rows and pointwise same inverse-factorial CMP109 shifted A/B expressions. They do NOT yet inhabit older #1444 original `BalabanCMP102BishopShiftedCoefficientExact.signedEvenRow n ≃ evenPart n` and `signedOddRow n ≃ -(oddPart n)`: still pay precise Cauchy boundary/interior splitting (including singleton n=0 and the terminal even endpoint) and branch-compatible same-source proof import, without blind-merge of #1444's deeply divergent branch. Then original `G(X)=1-2A-XA²+2XB+X²B²=0` on the **same represented A/B series** requires its analytic Cauchy limit, native quaternion norm/chord and literal physical CMP102 domain. No substitute from finite regression.

**Formal verification blocker to inspect, not conceal:** Agda `--safe` propagates to imports. The existing `BishopUnsignedFactorialCauchyParitySplitExact`, `BishopSignTwistedFiniteCauchyCoefficientExact` and the prior `YMClayCMP102NativeMasterSignedParitySpecializationExact` declare `--safe`, yet import `BishopFiniteCauchyRowReindexExact` which does not declare `--safe` in inspected source. An actual pinned Agda 2.9 typecheck must resolve the imported options and any proof elaboration defects before ANY kernel acceptance or `--safe` certification. This new adapter deliberately claims only SOURCE_WRITTEN. Do not confuse a `machineChecked` source tag with an accepted build.

**Physical Clay P0 remains independent:** Existing original full 4D Wilson/Haar/F19, CMP119/122 E/R/B/V/T and CMP116/W3 consumers remain substantial donors. Still OPEN: a unique real original global two-mark physical Wilson/F19 normalized source at actual beta(a) and constrained ΩΛS/FP/Jacobian/R T, then absolute all-connected two-support CMP116 rooted shell with cutoff/volume/SI-uniform positive rate and prefactor, then same-noncollapsed interacting OS H and strict positive nonvacuum mass; no spectral promotion from this finite Bishop identity. Original Wilson/Haar, Bałaban, Bishop/Bridges, Murray/Csimma, Cauchy and prior DASHI contributors retain attribution. No CI, new postulates, radius weakening or Clay proof claim.


### 23 November 2026 — CMP102 original finite A/B endpoint/Cauchy row paid at the source-written level

[Detailed same-original-source index cut](../physics/YMCMP102OriginalEndpointCauchySourceWeld20261123.md) and `DASHI/Physics/YangMills/YMClayCMP102OriginalEndpointCauchyShiftExact.agda` on master-based #1536. Actual original Fin `sum-init-last` and Nat `∸-suc` split both Cauchy endpoints; previous original Bishop `Row.cauchyCoefficientSuccessor`, `Twist.rowCauchyCoefficientRespectsTerms` and `YMClayCMP102MasterPositiveABCoefficientSourceWeldExact` pay the shifted original A/B factorial term identity. Source now contains explicit all-n `originalSignedEvenRowIsNativeAPart`, `originalSignedOddRowIsNegativeNativeBPart` and their `shiftedNativeBracketCoefficientZero` consumer, with odd degree-zero singleton and every terminal even endpoint retained. **No new carrier and no unproved row arguments in these source declarations; Agda kernel remains NOT RUN**, including transitive `--safe` acceptance. The #1444 source A/B definitions are formula-identical, but that old diverged branch is NOT imported or merged. Local exact Fraction source regression `scripts/check_ym_cmp102_endpoint_cauchy_20261123.py`: **17,281/17,281 PASS**, n=0..127; executable script SHA `d53a6f588e0ed9780a53be0be25641d146747389` verified byte-identical to GitHub blob. **Still OPEN:** pinned Agda elaboration, same-original-series analytic Cauchy limit `G(X)=0`, quaternion unit/chord, selected physical CMP102/minimizer; dominant physical CMP119/122 original Wilson T → absolute CMP116/W3 physical SI rate → same-H interacting OS gap. Do not promote finite arithmetic to physical Yang–Mills mass gap. Preserve original-source attribution and radius.


## 28 November — controlling current source-native priority

The newer live manuscript on [#1551](https://github.com/chboishabba/dashi_agda/blob/330bab7de4da3234778f90d2e0584aacc9204300/Docs/papers/live/Paper3YangMillsClayDraft.md) reconciles master Route S with the strong F1/F3/F4 route; this older version's original factorial A/B source and Bishop Cauchy rows are retained. Immediate P0 source work is CMP102: Lean #15 signed Path13 word norm recursion 0f1fc0d21803 and literal Eq119/120 nonflat row bound 858caa5eb9c9. Conditional per-block (61874/13)e, four-block row sum ≤20000e, e≤1/1142440000 sufficient for selected inverse enclosure. Original log/exp operator estimates and physical H(s(Y0)) on same common ball remain unpaid. No native kernel or continuum promotion. Existing F1/F3/F4 sufficient route is not the only possible route.
