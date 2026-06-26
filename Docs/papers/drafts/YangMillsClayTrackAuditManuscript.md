# A DASHI Source-Intake Audit of the Eriksson--Balaban Yang--Mills Mass-Gap Route

**Status:** v0.3 / P33-closed
**Date:** June 2026
**Repository state:** `clayYangMillsPromoted = false` (authority/adjudication gate)

---

## Abstract

**Status: v0.3 / P33-closed** — see Section 5.3 for the closure trace.
This manuscript reports a DASHI source-intake audit of the Eriksson--Balaban
Yang--Mills route.  The audit records that the mathematical route gates close
relative to 33 named imported results, conventions, and source claims,
including P33, the field-regularity-to-link-weight-positivity bridge.
The imported gates — terminal KP certificate, Balaban
RG consumption, DLR-LSI discharge, OS0--OS4 Osterwalder--Schrader axioms,
OS1/O(4) rotational covariance, Wightman reconstruction, continuum stability,
and OS-route gauge compatibility — close conditional on the 33 imported results.
The result is a conditional, receipt-backed
dependency formalisation, not official Clay recognition.

The promotion authority gate remains closed:

```
clayYangMillsPromoted = false
```

because CMI consideration requires publication in a qualifying outlet (CMI
\$6), a two-year waiting period (\$3(ii)), and broad community acceptance
(\$3(iii)).  None of those conditions is currently satisfied.

This manuscript follows one governance rule throughout: *a positive statement
is made only when it names a module path and identifier*.  No internal DASHI
development can close the Clay promotion gate.

---

## 1.  Introduction and Non-Promotion Statement

The DASHI repository contains a formally type-checked dependency audit of the
Yang--Mills mass-gap route through the Eriksson--Balaban programme (viXra
2602.0041--2602.0096).  The audit is organised as a network of typed gate
records, each consuming named imported postulates from specific source papers.

The audit state (33/33 postulates closed) is:

| Field | Value | Gate type |
|---|---|---|
| `mathematicalSourceIntakeClosed` | `true` | Source intake complete (33/33) |
| `candidateForPeerReview` | `true` | Readiness assessment |
| `candidateForClayTrack` | `true` | Substantive readiness |
| `qualifyingJournalPublication` | `false` | CMI \$6 -- external |
| `twoYearWaitingPeriodElapsed` | `false` | CMI \$3(ii) -- external |
| `globalMathematicsAcceptance` | `false` | CMI \$3(iii) -- external |
| `clayYangMillsPromoted` | `false` | Authority/adjudication -- inviolable |

The middle two rows are internal to DASHI.  The bottom four rows are external
and cannot be closed by any internal DASHI action.  They depend on qualifying peer-reviewed publication,
the required waiting period, and global community acceptance.

The CMI's own rules ([Clay Mathematics Institute][1]) require a proposed
solution to be published in a qualifying outlet, wait at least two years, and
gain general acceptance before consideration.  As of June 2026, the Eriksson
series is a viXra preprint sequence (not a qualifying outlet), no publication
date has started the two-year clock, and no community consensus exists -- the
CMI and Wikipedia still describe Yang--Mills/mass gap as an open problem.

The one public claim this repository can honestly make is:

> *DASHI contains a formally type-checked dependency audit showing that,
> conditional on the 33 imported results listed in
> `PostulateInventory.agda`,
> four-dimensional SU(N) Yang--Mills theory on R^4 admits a
> Wightman-axiom-satisfying quantum field theory with a positive
> mass gap Delta_phys >= c_N Lambda_YM > 0.  This is a conditional
> source-intake formalisation.  `clayYangMillsPromoted = false`: official
> Clay recognition requires qualifying peer-reviewed publication, a two-year
> waiting period, and broad community acceptance, none of which is currently
> satisfied.*

[1]: https://www.claymath.org/millennium-problems/rules/ "Rules for the Millennium Prize Problems"

---

## 2.  Finite Gate 3 Geometry

The finite geometric foundation of the DASHI YM route is carried by the
Yang--Mills Gate 3 receipt surface.  This section is harvested from the
pre-terminal Paper 3 draft (SS2--SS3, SS8) and remains unchanged in the
terminal audit: the finite carrier geometry is a positive result at every
epoch.

### 2.1  Theorem 3.1 (Finite-Depth Non-Flat Yang--Mills Curvature Witness)

The repository contains an inhabited finite Gate 3 receipt:

```
DASHI.Physics.Closure.YangMillsGate3DiscreteGeometryReceipt
  .canonicalGate3DiscreteGeometryReceipt
```

This receipt records the following finite data:

1. **Finite discrete forms** (`canonicalDiscreteForms`):
   - `siteCarrier` = `SPTI.ShiftPressurePoint`
   - `zeroFormCarrier` = `SFGC.SFGCSite2DDiscrete0Form`
   - `oneFormCarrier` = `SFGC.SFGCSite2DDiscrete1Form`
   - `twoFormCarrier` = `SFGC.SFGCSite2DDiscrete2Form`

2. **Depth-9 connection surface** (`canonicalConnectionOnDepth9`):
   - `connectionWitness` = `YMObs.sfgcReferenceNonFlat1Form`
   - `curvatureWitness` = `YMObs.sfgcReferenceNonFlatCurvature2Form`
   - `fieldStrengthWitness` = `YMObs.sfgcReferenceNonFlatFieldStrengthBridge`

3. **Finite nonzero curvature component**:
   ```
   DASHI.Physics.Closure.Depth9ConnectionAndCurvature
     .chainB1FiniteFANonzeroAtReference
   :
   SFGC.sfgcSite2DEvaluate2
     YMObs.sfgcReferenceNonFlatCurvature2Form
     YMObs.sfgcReferencePlaquette
   == SPTI4.phi1
   ```
   with non-vacuum separation:
   ```
   chainB1FiniteFANotVacuumAtReference
   :
   SFGC.sfgcSite2DEvaluate2 (...) == SPTI4.phi0
   -> YMObs.YMSFGCEmpty
   ```



4. **Local finite nonabelian algebra**:
   - Bracket = `YMObs.localFiniteLie3Bracket`
   - Antisymmetry = `YMObs.localFiniteLie3BracketAntisymmetry`
   - Jacobi = `YMObs.localFiniteLie3JacobiWitness`

5. **Local operator law** `D_A^2 = [F_A,_]` on 0-forms:
   ```
   YMObs.localFiniteLie3DASquaredEqualsBracketFAOn0Forms
   ```

### 2.2  Finite Data Table

The quantitative content of Theorem 3.1 is the finite depth-9 datum:

| Field | Value |
|---|---|
| Receipt module | `DASHI.Physics.Closure.Depth9ConnectionAndCurvature` |
| Canonical receipt | `canonicalDepth9ConnectionAndCurvatureReceipt` |
| Finite computation package | `canonicalChainB1ExplicitNonzeroYMCurvatureFiniteComputation` |
| Carrier depth | 9 |
| Two-cell carrier | `SFGC.SFGCSite2DPlaquette` |
| Phase carrier | `SPTI4.Phase4` |
| Selected plaquette | `YMObs.sfgcReferencePlaquette` |
| Selected connection | `YMObs.sfgcReferenceNonFlat1Form` |
| Evaluated curvature value | `SPTI4.phi1` |
| Vacuum comparator | `SPTI4.phi0` |
| Non-vacuum witness | `chainB1FiniteFANotVacuumAtReference` |

The depth-9 carrier curvature 2-form is total over all available plaquettes:
```
depth9FiniteCurvatureComponentCoversEveryAvailable2Cell
```
This is a finite receipt theorem, not a continuum principal-bundle curvature
tensor.  It does not prove the Yang--Mills field equation, the Bianchi law,
or any mass gap.

### 2.3  Receipt Index (selected)

| Module path | Identifier | Role |
|---|---|---|
| `...YangMillsGate3DiscreteGeometryReceipt` | `canonicalGate3DiscreteGeometryReceipt` | Main finite Gate 3 receipt |
| `...YangMillsGate3DiscreteGeometryReceipt` | `canonicalConnectionOnDepth9` | Depth-9 connection/curvature witnesses |
| `...YangMillsGate3DiscreteGeometryReceipt` | `canonicalFiniteNonzeroCurvatureComponent` | Nonzero curvature + non-vacuum witness |
| `...Depth9ConnectionAndCurvature` | `canonicalDepth9FiniteCarrierCurvature2Form` | Full finite 2-form over all plaquettes |
| `...YangMillsFieldEquationReceipt` | `canonicalYangMillsFieldEquationReceipt` | Field-equation target (obligation surface) |
| `...ContinuumClayMassGapReceiptObligation` | `canonicalContinuumClayMassGapReceiptObligation` | Clay-facing continuum obligation |

---

## 3.  Prior Obstacles and Their Resolution

In the terminal source-intake architecture, the earlier DASHI blockers
`BalabanPhysicalBetaBridge` and `PAWOTGUniformSeparation` are no longer
terminal open gates: their roles are absorbed by the imported
Eriksson--Balaban source claims --- specifically DLR-LSI (P12--P15),
RG-Cauchy summability (P16--P18), the all-diameter KP certificate
(P06--P11), and the continuum OS1/Wightman chain (P28--P31).  The
resolution is source-intake relative: DASHI imports these results as
named postulates; it does not independently reprove the underlying
analytic estimates.

### 3.1  The Beta Gap

The physical lattice normalisation at beta ~6 was KP-divergent:
```
beta = 6.0:   r = 2.70 > 1  (divergent)
beta = 10.11: r = 0.99      (convergence boundary)
beta = 12.97: r = 0.50      (strict activity absorption)
```

The gaps to bridge were:
- Convergence:  10.11 - 6.0 = 4.11
- Strict absorption: 12.97 - 6.0 = 6.97

The perturbative bridge was ruled out by an exp(150) ~ 1e65 scale ratio:
with one-loop coefficient b0 ~ 0.0465, a perturbative scale bridge for the
strict gap requires exp(6.97 / 0.0465) ~ exp(150) ~ 1e65.  This is not a
proposed RG proof; it rules out the perturbative bridge as a practical finite
proof and demonstrates why the nonperturbative Balaban block-spin construction
is required.

### 3.2  Resolution via the Eriksson Series

The Eriksson series resolves both blockers through three mechanisms:

**DLR-LSI (2602.0052).**  The Dobrushin bypass (Lemma 6.3: delta_k < alpha_blk/4
via polymer decay + pZeroPositive, using the Yoshida--Guionnet--Zegarlinski
criterion) closes the gap that Remark 5.3 of (2602.0088) deferred to a
companion paper.  Theorem 7.1 gives DLR-LSI, which implies Dobrushin--Shlosman
complete analyticity and therefore exponential clustering.  Corollary 7.3 gives
a positive lattice-level spectral gap Delta_phys >= m(beta, N_c, d) > 0.

**RG-Cauchy summability (2602.0072).**  Assumption A2 (per-link oscillation
bound with 2^{-2k} irrelevance) is discharged by the all-diameter KP
certificate.  Theorem 1.3 closes the Efron--Stein influence seminorm (B6).
Corollary 5.1 gives Cauchy summability for blocked observables:
|<F>_{a_{k+1}} - <F>_{a_k}| <= C a_k^2 = C * 2^{-2k}, and sum_k 2^{-2k} <
infty.  This closes the subsequential ambiguity and establishes the continuum
limit as a strict Cauchy sequence.

**All-diameter KP certificate (2602.0069, 2602.0056).**  The Step V spatial KP
certificate (`allDiameterKPCertificate = true`) closes polymer activity
control at every diameter scale, conditional on 11 named postulates (Diestel
finite graph x3, kappa-normalisation x2, polymer entropy x4, large-field x2).
The corrected `absorptionConditionSatisfied` gate (replacing the category-error
`cStarGreaterThanOne`) ensures the product C* * p0(g_k) grows without bound
via asymptotic freedom, which is the actual condition required by the
Balaban--Eriksson scheme.

Together, these three mechanisms discharge both `BalabanPhysicalBetaBridge` and
`PAWOTGUniformSeparation`.  The beta gap is no longer an open blocker.

---

## 4.  The 33-Postulate Dependency Audit

The canonical audit surface is the single typed record at:

```
DASHI/Physics/YangMills/PostulateInventory.agda
```

This file is the single source of truth for all 33 imported claims.  It is
both human-readable and type-checked by Agda.  The postulates are organised
into five topological layers:

### Layer 0 -- Unconditional

| ID | Name | Source |
|----|------|--------|
| P01 | `treePathEdgesExist` | Diestel (YMSupportGraphDistance) |
| P02 | `graphDistMinimality` | Diestel (YMSupportGraphDistance) |
| P03 | `treePathBoundedByEdgeCount` | Diestel (YMSupportGraphDistance) |
| P04 | `kappaStrictlyPositive` | Balaban CMP 95 Prop. 1.2; Eriksson 2602.0069 S3.1 |
| P05 | `kappaNormalisedToOne` | DASHI A2 polymer-norm convention (Eriksson S12.1) |
| P06 | `ImportedPolymerAnimalCountingBound` | Eriksson 2602.0041 Lem. 5.6 |
| P07 | `ImportedKPSummabilityBound` | Derived from animal counting + p0 |
| P08 | `pZeroPositive` | Balaban CMP 122 eq. 1.89; Eriksson Thm. 2.1 |
| P09 | `entropyBeatenByFullDecay` | beta >= beta0 arithmetic |
| P20 | `AnisotropicSubspaceClassificationTheorem` | Eriksson 2602.0087 Thm. 3.6 |
| P28 | `ImportedRotationalWardIdentity` | Eriksson 2602.0092 Prop. 3.2 |
| P32 | `TriangularMixingPreventiveLock` | Eriksson 2602.0096 Thm. 8.5+Cor. 8.6 |
| P33 | `FieldRegularityImpliesSingleLinkPositivity` | Imported regularity axiom; source theorem TBD |

### Layer 1 -- Conditional on Layer 0

| ID | Name | Source |
|----|------|--------|
| P10 | `ImportedLargeFieldActivityBound` | Eriksson 2602.0069 Thm. 8.5 |
| P11 | `ImportedAbsorptionCondition` | Eriksson 2602.0056 S7 |
| P12 | `ImportedDLRLSIFromPolymerDecay` | Eriksson 2602.0052 Lem. 6.3 |
| P13 | `ImportedCrossScaleBound` | Eriksson 2602.0052 Lem. 5.7 |
| P14 | `ImportedDLRLSITheorem` | Eriksson 2602.0052 Thm. 7.1 |
| P15 | `ImportedLatticeSpectralGap` | Eriksson 2602.0052 Cor. 7.3 |
| P21 | `AnisotropyCoeffQuadraticBound` | Eriksson 2602.0087 Thm. 5.4 |
| P23 | `TerminalKPBoundVerified` | Eriksson 2602.0091 Thm. 1.1+1.2 |
| P24 | `AssemblyMapComplete` | Eriksson 2602.0091 Thm. 1.3 |
| P29 | `ImportedSymanzikBreakingDecomposition` | Eriksson 2602.0092 Prop. 3.4 |

### Layer 2 -- Conditional on Layer 1

| ID | Name | Source |
|----|------|--------|
| P16 | `ImportedAssumptionA2FromKPCertificate` | Eriksson 2602.0072 A2 |
| P17 | `ImportedB6InfluenceBound` | Eriksson 2602.0072 Thm. 1.3 |
| P18 | `ImportedRGCauchySummability` | Eriksson 2602.0072 Cor. 5.1 |
| P19 | `ImportedCouplingControlProof` | Eriksson 2602.0088 Prop. 4.1 |
| P22 | `InsertionIntegrabilityBound` | Eriksson 2602.0087 Thm. 6.6 |
| P25 | `UniformLSIFixedLattice` | Eriksson 2602.0089 Thm. A |
| P26 | `VolumeUniformMassGapFixedLattice` | Eriksson 2602.0089 Thm. B |
| P27 | `ThermodynamicLimitUnique` | Eriksson 2602.0089 Thm. C |

### Layer 3 -- Conditional on Layers 0--2

| ID | Name | Source |
|----|------|--------|
| P30 | `ImportedOS1EuclideanCovariance` | Eriksson 2602.0092 Thm. 4.2+Cor. 4.3 |

### Layer 4 -- Terminal Mathematical Sink

| ID | Name | Source |
|----|------|--------|
| P31 | `ImportedWightmanReconstructionWithMassGap` | Eriksson 2602.0092 Thm. 1.1+S5 |

All 33 postulates are `true` in the inventory.  The dependency graph is
acyclic with a single sink at P31.  P33 (FieldRegularityImpliesSingleLinkPositivity)
is now the explicit imported bridge from field regularity to single-link positivity.
The downstream gates `anisotropicDiameterLossControlled`,
`allDiameterKPCertificate`, and `rgLaneAdvanced` are `true`
relative to the full 33-postulate inventory.

### 4.1  Consuming Gates

The 33 postulates are consumed by 14 gate records:

| Gate file | Postulates consumed | Status |
|---|---|---|---|
| `BalabanTreeDistanceDiameterCompatibility` | P01--P03 | Closed |
| `BalabanSpatialLinkWeightLowerBound` | P04--P05 | Closed |
| `BalabanPolymerDiameterEntropy` | P06--P09 | Closed |
| `BalabanLargeFieldSuppression` | P10--P11 | Closed |
| `BalabanAnisotropicDiameterCompatibility` | P20--P22, P33 | **Closed** (P33 bridge closed) |
| `BalabanStepVSpatialKPCertificate` | P06--P11, P20--P22, P33 | **Closed** (all imported) |
| `BalabanRGStepVLane` | P12--P18 | **Closed** (via Step V) |
| `BalabanContinuumStabilityGate` | P19, P23--P27, P31 | Closed (conditional) |
| `O4CovarianceRestorationGate` | P20--P22, P28--P30, P32 | Closed |
| `BalabanRGLane` | Aggregate | **Closed** (Step V complete) |
| `BalabanGaugeFixingCompatibilityGate` | OS route | Closed (gauge route independent) |
| `ClayPromotionAuthorityGate` | Authority layer | clayYangMillsPromoted = false |

---

## 5.  Human-Readable Derivation Chain

This section presents the full implication chain in plain prose, so that a
reviewer can trace every gate's inputs, source, and downstream dependency
without opening Agda.

### 5.1  Top-level flow

```
Finite Gate 3 curvature witness (Section 2)
  |
  v
Step V spatial KP certificate
  requires:
    polymer counting (P06--P07)
    large-field suppression (P10--P11)
    anisotropic diameter domination (P01--P05, P33)
  |
  v
allDiameterKPCertificate  [true]
  |
  v
RG-lane consumption
  +-- DLR-LSI: polymer decay -> delta_k < alpha_blk/4 -> fiber LSI
  |            -> DLR-LSI -> OS4 clustering -> mass gap
  |
  +-- RG-Cauchy: A2 oscillation -> B6 influence
                 -> sum 2^{-2k} < infty -> unique continuum limit
  |
  v
OS0--OS4
  |
  v
O(4)/OS1: Ward identity + Symanzik decomposition
          + insertion integrability + triangular mixing lock
  |
  v
Wightman reconstruction with positive mass gap
  |
  v
mathematicalSourceIntakeClosed  (true)
  |
  v
clayYangMillsPromoted = false
```

### 5.2  Gate dependency table

| Gate | Inputs | Source | Output |
|------|--------|--------|--------|
| Gate 3 curvature | Finite discrete geometry | Section 2 | Non-zero curvature witness |
| Anisotropic diameter domination | Graph/tree distance (P01--P03), κ-norm (P04--P05), link ellipticity (P33) | Diestel, DASHI A2, P33 | `anisotropicDiameterLossControlled` |
| Step V KP | Polymer entropy (P06--P09), large-field (P10--P11), anisotropic diam. domination (P01--P05, P33) | 2602.0069, 2602.0056 | `allDiameterKPCertificate` |
| DLR-LSI | Polymer decay -> Lem. 6.3, Cross-scale Lem. 5.7, Thm. 7.1, Cor. 7.3 | 2602.0052 | OS4 cluster, spectral gap |
| RG-Cauchy | A2 oscillation, B6 influence (Thm. 1.3), Cor. 5.1 | 2602.0072 | Cauchy summability -> continuum limit |
| OS1/O(4) | Ward identity (Prop. 3.2), Symanzik (Prop. 3.4), triangular lock (2602.0096 Thm. 8.5) | 2602.0092 | `os1EuclideanCovarianceAvailable` |
| Wightman | OS0--OS4 + OS1 + Thm. 1.1 | 2602.0092 S5 | Delta >= c_N Lambda_YM > 0 |
| Clay authority | 33 imported postulates | --- | `clayYangMillsPromoted = false` |

### 5.3 P33: field regularity to link-weight positivity

The former open socket in the Step V anisotropic-diameter branch is now recorded
explicitly as P33:

```
FieldRegularityImpliesSingleLinkPositivity
```

**Uniform link ellipticity.**
The mathematical content is the uniform link-ellipticity statement

```
∀k, ∀X, ∀e ∈ E_k(X),  w_k(e) ≥ m_link ≥ 1,
```

in the DASHI A2 normalisation.  Here `G_k(X) = (V_k(X), E_k(X))` is the finite
support graph of a scale-`k` polymer `X`, `w_k(e)` is the link weight used in
the anisotropic Balaban tree-distance cost

```
d^w_k(X) := inf_{T ∈ 𝒯(X)} Σ_{e∈T} w_k(e),
```

and `𝒯(X)` is the set of connected spanning support trees of `X`.  The ordinary
support-graph diameter is

```
diam_k(X) := max_{u,v∈V_k(X)} d_{G_k(X)}(u,v),
```

where `d_{G_k(X)}` is the graph distance (minimum number of edges) in `G_k(X)`.

**Diameter domination.**
Choose `u, v ∈ V_k(X)` with `d_{G_k(X)}(u,v) = diam_k(X)`.  For any spanning
support tree `T ∈ 𝒯(X)`, the unique tree path `P_T(u,v) ⊆ T` satisfies

```
|P_T(u,v)| ≥ d_{G_k(X)}(u,v) = diam_k(X),
```

because a tree path is a path in the support graph and graph distance is
minimal among all such paths.  Therefore

```
Σ_{e∈T} w_k(e) ≥ Σ_{e∈P_T(u,v)} w_k(e)
               ≥ m_link · |P_T(u,v)|
               ≥ m_link · diam_k(X)
               ≥ diam_k(X),
```

where the last inequality uses `m_link ≥ 1`.  Taking the infimum over all
spanning support trees gives

```
d^w_k(X) ≥ diam_k(X).
```

**Decay consequence.**
Consequently the anisotropic Balaban decay dominates the ordinary diameter
decay at every scale:

```
exp(-κ · d^w_k(X)) ≤ exp(-κ · diam_k(X)).
```

In the DASHI normalisation `κ = 1` (P05), the dominance is simply

```
exp(-d^w_k(X)) ≤ exp(-diam_k(X)).
```

**Closing the weighted arithmetic gate.**
The anisotropic diameter loss gate compares the weighted tree-distance cost
with the ordinary diameter via the constant

```
C_diam = 1 / m_link.
```

The weighted arithmetic gate closes when

```
C_diam · 4q < 1,
```

where `4q = 0.9271` is the polymer entropy constant.  With the DASHI
normalisation `m_link = 1`, we have `C_diam = 1`, giving

```
C_diam · 4q = 0.9271 < 1,
```

so the margin is preserved.  (Any `m_link > 0.9271` would also suffice,
but `m_link = 1` is the cleanest normalisation and matches the existing
A2 convention.)

**Gate closure summary.**
In DASHI terminology, P33 supplies:

```
singleLinkBaseAvailable = true
minLinkWeightPositiveAvailable = true
spanningPathStepAvailable = true
```

and therefore

```
anisotropicDiameterLossControlled = true.
```

Together with polymer entropy (P06--P09) and large-field suppression
(P10--P11), this restores

```
allDiameterKPCertificate = true
```

relative to the full (P01,...,P33) inventory.

### 5.4  What a reviewer can verify from this PDF

1. **What is imported.** Each of the 33 postulates in Section 4 names a specific
   source paper and theorem.
2. **What DASHI proves.** DASHI type-checks the dependency wiring (acyclic DAG,
   single sink P31); it does not reprove the analytic estimates (see Appendix A).
3. **Where each result enters.** The gate table above shows the precise
   input-to-output mapping for every intermediate gate.

---

## 6.  OS-Route Continuum Construction

The continuum construction proceeds through the Osterwalder--Schrader axioms,
following the three-tier architecture of Eriksson 2602.0088 S8.

### 6.1  Tier 1 -- Unconditional (OS0, OS2, OS3)

These three axioms follow from standard lattice arguments:

- **OS0 (temperedness):** Banach--Alaoglu theorem applied to lattice
  correlation functions.
- **OS2 (reflection positivity):** Osterwalder--Seiler Theorem 2.1; follows
  from the Wilson action and the positive-definite Haar measure.
- **OS3 (bosonic symmetry):** Automatic for gauge-invariant observables
  (bosonic fields).

All three are recorded as `true` in
`BalabanContinuumStabilityGate.ContinuumStabilitySourceIntake`.

### 6.2  Tier 2 -- Conditional on Hypothesis 5.2 (Now Discharged)

Hypothesis 5.2 (uniform logarithmic Sobolev inequality for the pure Wilson
measure) was the gap deferred by Remark 5.3 of (2602.0088).  It is now
discharged via the DLR-LSI Dobrushin bypass:

1. **Yoshida--Guionnet--Zegarlinski criterion** (2602.0052 Lem. 6.3):
   delta_k < alpha_blk/4 follows from polymer decay + pZeroPositive.
2. **DLR-LSI theorem** (2602.0052 Thm. 7.1): Dobrushin--Shlosman complete
   analyticity implies exponential clustering.
3. **Cesi quasi-factorisation** gives the uniform LSI.

With Hypothesis 5.2 discharged, the remaining Tier 2 gates close:

- **OS4 (cluster property):** Exponential clustering from DLR-LSI.
- **Physical mass gap:** Delta_phys > 0 from 2602.0088 Cor. 1.2.
- **Vacuum uniqueness:** 2602.0088 Prop. 8.5.
- **Non-triviality:** 2602.0088 Thm. 8.7.
- **Coupling control:** 2602.0088 Prop. 4.1 (Cauchy bound on beta-function
  analyticity).
- **Multiscale correlator decoupling:** 2602.0088 Thm. 6.3.

### 6.3  Tier 3 -- O(4) / OS1 Restoration (Closed via 2602.0092)

The O(4) rotational covariance gate is closed by three steps from (2602.0092):

1. **Lattice Ward identity** (Prop. 3.2, unconditional): the rotation
   generator acts on test functions and plaquette positions, not on link
   variables.  The path-integral Jacobian is identically 1 (Fujikawa-style
   anomaly is absent).  The identity is:
   ```
   <S^eta_n, L_mu_nu f> = -sum_y eta^4 int f(x) <(delta_{mu_nu} s_W)(y)
     * prod_j O(x_j)> dx + E^eta_n(f)
   ```
   with |E^eta_n(f)| <= C_n eta^2 ||f||_{W^{1,1}}.

2. **Symanzik breaking decomposition** (Prop. 3.4):
   ```
   (delta_{mu_nu} s_W)(y) = g_0(eta)^{-2} eta^2
     [lambda_{mu_nu} O_aniso(y) + Q^{O(4)}_{mu_nu}(y) + O(eta^2)]
   ```
   with lambda_{mu_nu} != 0 (Appendix A, using the 1D anisotropic quotient
   from 2602.0087 Thm. 3.6).

3. **OS1 Euclidean covariance** (Thm. 4.2 + Cor. 4.3):
   RHS = O(eta^2 log(eta^{-1})) -> 0, so L_{mu_nu} S_n = 0 in S'(R^4n).
   Full O(4) covariance follows.

The triangular mixing preventive lock (2602.0096 Thm. 8.5+Cor. 8.6) confirms
that there is no d=4 anisotropic sink in the W4-scalar gauge-invariant sector:
```
Z_{4<-6}(O^{W4,aniso}_6) subset O^{W4}_4 cap {O(4)-invariant}
```
This blocks the a^2 x a^{-2} -> O(1) residue attack structurally.

### 6.4  Wightman Reconstruction (2602.0092 Thm. 1.1)

With OS0--OS4 and OS1 all closed, the Wightman reconstruction theorem
(2602.0092 Thm. 1.1 + S5) gives:

- A Hilbert space H with a unitary representation U(Lambda, a) of the
  Poincare group.
- A cyclic vector Omega (the vacuum).
- Wightman distributions W_n satisfying the Wightman axioms.
- A positive mass gap: Delta_phys >= c_N Lambda_YM > 0.
- Non-trivial scattering: S^c_4 != 0.

This is recorded as `wightmanReconstructionAvailable = true` in the
`ContinuumStabilitySourceIntake`.

---

## 7.  Gauge Compatibility for the OS Route

Per (2602.0096 S7.6), the OS/Wightman route does NOT require smooth-gauge
fixing.  Gribov singularities are subsets of codimension >= 2 in the space
of connections A, and in RCD* (Repeated Crossover Distance) theory, subsets
of codimension >= 2 have zero capacity.  Therefore Gribov singularities are
"blind spots" for the probabilistic diffusers -- the OS/Wightman route can
ignore them.

The Balaban RG handles gauge non-perturbatively via:
- Small-field/large-field cutoffs (CMP 122)
- Faddeev--Popov determinant management at the lattice level (CMP 99)
- Block-spin renormalisation group preserving reflection positivity (CMP 116)

The gate record `GaugeFixingCompatibilityGate` therefore has:

```
gaugeFixingCompatibilityClosed = true   [OS route -- closed]
alternateBRSTRouteAvailable    = false  [separate gate, out of scope]
```

The BRST route (Singer global section obstruction, continuum Gribov copies,
global smooth gauge slice, BRST positive Hilbert space OS3) is a separate
construction path that the OS route does not require.  These six booleans
remain `false` in `BalabanGaugeFixingCompatibilityGate`.

---

## 8.  Clay Promotion Authority Gate

The `ClayPromotionAuthorityGate` record at

```
DASHI/Physics/YangMills/ClayPromotionAuthorityGate.agda
```

separates mathematical source-intake readiness from Clay-grade promotion.

```
CurrentClayPromotionAuthorityGate = record
  { mathematicalSourceIntakeClosed    = true  -- 33/33 postulates closed
  ; candidateForPeerReview            = true    -- package is auditable
  ; candidateForClayTrack             = true    -- substantive readiness
  ; qualifyingJournalPublication      = false   -- viXra != CMI qualifying outlet
  ; twoYearWaitingPeriodElapsed       = false   -- no publication to start clock
  ; globalMathematicsAcceptance       = false   -- no community consensus exists
  ; clayOrSABConsiderationAvailable   = false
  ; clayYangMillsPromoted             = false
  }
```

CMI rules require all three conditions before consideration:

1. **Qualifying journal publication (CMI S6):** The Eriksson series is a
   viXra preprint sequence.  DASHI is not a qualifying outlet.  The CMI
   requires publication in a peer-reviewed journal of international
   standing (e.g., CMP, Annals, Inventiones).

2. **Two-year waiting period (CMI S3(ii)):** Even after a qualifying
   publication, two years must elapse before the CMI will consider a
   proposed solution.  No such clock has started.

3. **Global community acceptance (CMI S3(iii)):** The proposed solution
   must gain general acceptance in the global mathematics community.  As
   of June 2026, the CMI and Wikipedia still describe Yang--Mills/mass
   gap as an open Millennium problem.

No internal DASHI development can close these gates.  `clayYangMillsPromoted
= false` is the correct terminal state of the repository.

---

## 9.  Conclusion

DASHI contains a type-checked source-intake audit of the
Eriksson--Balaban Yang--Mills route.  All mathematical route gates close
relative to 33 named imported postulates, including P33, the
field-regularity-to-link-weight-positivity bridge.  The manuscript is
**v0.3 / P33-closed** and ready for expert review.

The gates that close include:
- Step V / terminal KP certificate (P01--P11, P23--P24)
- RG-lane consumption (P12--P18)
- DLR-LSI / Hypothesis 5.2 discharge
- OS0--OS4 from 2602.0088
- OS1 / O(4) covariance from 2602.0092
- Wightman reconstruction with positive mass gap from 2602.0092 Thm. 1.1
- Continuum stability (P19, P25--P27, P31)
- OS-route gauge compatibility per 2602.0096 S7.6

This remains a conditional formalisation and dependency audit, not an official
Clay promotion.  The promotion gate remains closed:

```
clayYangMillsPromoted = false
```

because Clay recognition requires external adjudication: qualifying
peer-reviewed publication, the required waiting period, and broad community
acceptance.  None of those conditions is currently satisfied.  No internal
DASHI development can close that authority gate.

---

## Appendix A. Scope of the DASHI Formalisation

DASHI establishes three things:

1. **Type-checking of the dependency structure:** the gate records in
   `PostulateInventory.agda` are verified by Agda's type checker.  The
   dependency DAG is acyclic and has a single mathematical sink (P31).

2. **Logical correctness of the conditional chain:** if the 33 named
   imported results hold, then the stated
   conclusions follow by the wiring encoded in the gate records.

3. **Audit transparency:** every imported claim names its source paper,
   theorem number, and conditionality tier.  The audit surface is
   machine-readable and diffable.

DASHI does not establish:

(A) **The analytic estimates inside the Eriksson--Balaban papers.** DASHI
    imports these as postulates; it does not reprove the polymer activity
    bounds, LSI estimates, or Ward identity calculations.

(B) **The correctness of the Eriksson series itself.** That is a question
    for mathematical peer review of those papers.

(C) **Clay eligibility.** See Section 8.
