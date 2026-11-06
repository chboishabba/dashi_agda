### Physical R445/R320: derivation of a uniform q from UV RG error budget

**New** `YMClayPhysicalRGDriftToUniformInfluenceExact.agda`: defines `finiteRGDrift`, `SelectedPhysicalRGInfluenceBudget` and proofs `selectedRGInfluenceBelowFiniteDrift`, `selectedRGInfluenceUniformPhysicalUpper`, `selectedRGInfluenceUniformStrictMargin`. It implements exact induction for:

```text
kappa_0 <= q0
kappa_(n+1) <= kappa_n + delta_n
sum_(k<n) delta_k <= B  for ALL n
q0+B < 1
---------------------------------
for ALL n: kappa_n <= q := q0+B < 1 .
```

`YMClayRGDriftOriginalGibbsInstantiationExact.agda` then *constructs* an indexed finite conditional family `Cube.OriginalPhysicalCubeConditionals` with common `q=q0+B` by proof transport through the preexisting rational normalized-row Dobrushin owner. No independent global q field is chosen in this constructor. Source is **AGDA_UNVERIFIED and PHYSICALLY_CONDITIONAL**.

The exact original physical obligation now decomposes into three non-interchangeable proofs:
1. `UV.P01`: selected actual full SU(N) Wilson (continuous Borel Haar) Gibbs pushforward and regular conditionals on the SAME original chosen physical cube. **Current rational finite-fibre record does not itself encode equality to the original continuous measure.** Build a genuine physical measure-to-conditional kernel weld or a valid approximation with cutoff-uniform TV error.
2. `UV.P02`: bound `kappa_0<=q0` for that physical source at reference fixed physical `ell`; establish `kappa_(n+1)<=kappa_n+delta_n` on the SAME conditional family for every cutoff and volume. A β(a) bare-link perturbation that grows cannot silently inhabit this premise.
3. `UV.P03`: derive `sum_(k<n)delta_k<=B` uniformly in n (and L), e.g. a source-proved geometric-polymer envelope `delta_k<=A theta^k` with `0<=theta<1` gives `B=A/(1-theta)`; check strict `q0+B<1`.

**Exact rational independent fixture (NOT the Wilson source):** `q0=1/3`, `A=1/12`, `theta=1/2`, so `B=1/6`, `q=1/2`. `scripts/check_ym_rg_drift_budget_reference.py` executed 128 exact Fraction refinements, exact geometric partial-sum equality and 5 negative controls PASS.  No source-Gibbs/OS interpretation or compiler receipt is inferred from this fixture.

**Critical distinction:** `YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact` constructs a selected original weighted *positive functional*, not a regular conditional probability or a density on a continuous measurable carrier. `YMClaySUNWeightedDisjointPairFibreReparamExact` supplies weighted finite fibre identities under one-link Haar algebraic prerequisites, not a full SU(N) Borel measure. `BalabanCMP116PublishedLiteralSelectedRound467Exact` provides the correct literal source ABI, but its `literalSelectedCMP116Localization` and `sourceEnvelopeBelowPhysicalClusteringEnvelope` are physical fields without constructed original-source witnesses.

### OS and Clay endpoints (same source, NOT promotional bookkeeping)

Even if UV.P01–03 establish actual conditional q at fixed physical `ell`, the inference `m >= -log(q)/ell` requires a **separate selected physical** local-support-to-OS-time bound, positive transfer semigroup, dense relevant local vectors, continuum limit, original same-`H` and no inaccessible sectors; these are in existing `BalabanCMP116PublishedLiteralToGapRound479Exact`, `BalabanClayT5ClusteringToTransferGapExact`, and `YangMillsDirectSourceOSSameHGapExact`. Nontrivial axiomatic 4D continuum for every compact simple G remains unproved. Do not claim Clay completion.

**Verification in this tool environment:** no `agda`/Nix binary; no green associated PR-triggered workflow receipt. Python exact-reference and source/GitHub readback only. The deadline for `VERIFIED_AGDA` status is an actual pinned Agda return code, no metas and audited transitive authorities, not a GitHub PR link.

---

# YM #1444 — physical-cube Dobrushin × CMP116 × OS: constructive maximum-cut steelman (2026-11-06)

**Target:** physical 4-dimensional nontrivial Yang–Mills with strictly positive spectral gap for prescribed compact simple groups. **Current status:** stronger quantitative *criterion and finite Gibbs compiler*, **NOT** a proof that its universal physical assumptions hold. This document supersedes the bare-link `18 tanh(12 beta)` as the priority strategy but does not deny that sufficient estimate. Golden proof owners remain the existing Agda sources, not this prose.

## 1. Same-source findings from source-level audit

| Pipeline | Existing golden owner | Exact already-owned statement | Unpaid source-native interpretation |
|---|---|---|---|
| Original finite Gibbs/haar | `YMClaySUNVariablePeriodicProductHaarExact`, `YMClaySUNMatrixSpatialC3RealFubiniExact`, `YMClaySUNNativeSixPlaneFullC3FromInverseTraceExact` | Finite periodic Wilson action, normalized product-Haar algebra, C3 original 6-plane real-sum reindexing | Continuous actual Borel Haar with integrable tests and all selected CMP119 E/R/B/V terms |
| Native pair pushforward | `YMClaySUNWeightedDisjointPairFibreReparamExact` F17–F22, `YMClayNativeSideFourTwoLinkPairSameObjectExact` | Arbitrary coupled weighted 64-pair plus 896 spectator integration, pointwise original block link | 1,024 original label canonical permutation, physical same-decoder Gibbs density and true analytic Haar |
| Dobrushin (finite rational) | `BalabanFiniteDobrushinReopeningExact`, `BalabanFiniteNormalizedWeightDobrushinExact`, `BalabanFiniteBoundaryConditionedDobrushinExact` | Finite original conditional row L1 ≤ 2 times raw relative-weight epsilon; expectation oscillation ≤ 2A epsilon | Original physical cube conditional weights over SU(N), a strict coefficient common to changing UV cutoffs/volumes |
| Finite RG same-object | `BalabanFiniteRGReopeningDobrushinExact`, `YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact` | Finite push/pull/reopening and selected original cylinder algebra | Physical weighted fibre kernel, reflection-compatible actual coarse time/block projection |
| UV & RG source | `BalabanPublishedUVStabilityNonlinearRGCoreExact`, `BalabanCMP122PublishedFourDimensionalUVStabilityExact`, `Balaban1989Theorem1UVStabilityExact` | Source-owned CMP119/CMP122 step stability when active trajectory/source hypotheses are supplied | Same original selected Wilson/Haar/ghost/background/large-field carrier and all-scale physical estimates. Published UV stability is not a continuum mass-gap proof |
| Full CMP116 direct selected H1 | `BalabanCMP116PublishedLiteralSelectedRound467Exact`, `BalabanCMP116ModeSelectedSubgapClusteringBidiExact`, `BalabanCMP116CanonicalFiniteCovarianceDecayRound452Exact` | Literal selected `D_Jleft D_Jright log Z` adapter, no independent abstract covariance or coefficient-1-rooted-shell detour | In R467, `literalSelectedCMP116Localization` and `sourceEnvelopeBelowPhysicalClusteringEnvelope` are genuine unconstructed fields. In mode route, same-spectrum convergence and envelope matching remain conditional |
| Same-H spectral | `BalabanCMP116PublishedLiteralToGapRound479Exact`, `BalabanClayT5ClusteringToTransferGapExact`, `BalabanClayT5PhysicalContinuumOSGapBridgeExact` | Spectral positive-measure contradiction and conditional OS gap compiler | Same physically selected OS semigroup, dense local observable overlap, uniform physical rate, continuum limit/nontriviality, all-G scope |
| Uniform cone alternative | `BalabanClayUniformPerronContractionExact` | Explicit proof that finite-stage projective diameter need not have any uniform common bound | Uniform projective contraction of actual time transfer / coarse Gibbs kernels in physical units |

**No duplicate CMP116 reconstruction:** source coverage of many sublemmas is already extensive. What has NOT been shown is that the literal actual selected Wilson family *inhabits* the R467 common analytic domain, localization and envelope fields, and that their rate remains physical-uniform.

## 2. Replace bare-link contraction with one fixed-physical-cube contraction

Set one positive physical side `ell>0`. Choose a continuum cutoff schedule with `a_n>0` and `b_n a_n = ell` (where `b_n` is the number of fine links per cube side). More general schedules may use an interval `ell <= b_n a_n < ell + a_n` with its own certificate. This is different from fixing `b_n` when `a_n→0`.

Let `mu_{a,L}^{Wilson}` be the actual normalized original compact-group Wilson-Gibbs measure, `B_{a,ell}` its original Wilson block holonomy, and `gamma_i^{a,L}(·|eta)` the *same* physical conditional law for one block given its exterior. The intended quantitative input is a weighted Dobrushin–Shlosman inequality for original block influence matrix `C^{a,L}`:

```text
PCUBE.P01: OriginalCubeConditionalIsSelectedGibbs
  gamma_i^{a,L}(·|eta) is the regular conditional of
  B_{a,ell *} mu_{a,L}^{Wilson}; no alternate Haar/Gibbs law.

PCUBE.P02: FixedPhysicalCubeCalibration
  for all cutoffs a: b(a)*a = ell  (or the proved ceil variant).

PCUBE.P03: GaugeCompatiblePhysicalCube
  canonical original source/blocked Wilson action/positive-time sigma
  algebra and reflection commute with the exact selected block.

PCUBE.P04: UniformWeightedInfluence
  exists positive weights w_i and one q<1, BOTH independent of a,L:
  for every cutoff/volume/block i,
      (sum_j C^{a,L}_{ij} w_j)/w_i <= q.
  The coefficients C are upper bounds on SAME original normalized
  conditional TV influences for a single neighbour perturbation.

PCUBE.P05: UniformMarkedSourceTransfer
  the original R467 mixed-J source class and selected observable vector
  have scale/volume-uniform amplitudes in physical norms, with the
  common physical-cube exponential envelope and no divergent prefactor.

PCUBE.P06: SameHilbertStrongContinuityAndDensity
  selected OS reflection positive limit, nontrivial local algebra,
  strong e^{-t H}, dense centered local vectors, physical time t.

PCUBE.P07: ContinuumAndAllG
  tightness/Schwinger convergence, OS/Wightman axioms, source
  identification, full actual compact simple G coverage.
```

**Proof of finite weighted contraction:** for a nonnegative matrix `C`, `w_i>0`, and `Cw≤q w`, positivity gives by induction `C^r w≤q^r w` for every `r∈Nat`. The corresponding supported observable sensitivity decays no slower than `q^r`. The exact rational checker `scripts/check_ym_physical_cube_perron_certificate.py` implements these checks and rejects `q>=1`, negative entries, zero Perron weights, wrong fixed physical cube calibration and missing physical source receipts.

**Physical rate:** if the SAME OS correlations at times `t=r ell` satisfy `0≤<FΩ,e^{-r ell H}FΩ>≤C_F q^r` for a dense centered family, the positive spectral measure argument yields `H|_{Ω⊥}≥m I` with `m=-log(q)/ell>0`. This is meaningful at every `a→0` because `ell`, **not** the number of fine links, is fixed. Strong continuity and density upgrade the bound from the sampled semigroup `e^{-ell H}` to the full generator.

**Converse/negative control:** `T_a=diag(1,e^{-a^2})` has positive finite-cutoff gap but `H_a=-log(T_a)/a=diag(0,a)` and physical gap tends to zero. Thus a finite gap, an `a`-uniform *dimensionless* lower gap, or stagewise Perron diameter without compatible scaling is NOT a physical mass-gap certificate. Another negative control is an entire block influence matrix with `q>=1`, even if finite rational rows and Gibbs normalization all typecheck.

## 3. Two competing max-cut routes (keep both; don't assume the stronger one)

**Route A — uniform raw-weight influence:** prove `|u_eta(y)-u_xi(y)|≤epsilon u_eta(y)` on original bounded local fibre uniformly for permitted boundary changes; use `BalabanFiniteBoundaryConditionedDobrushinExact` and new `YMClayPhysicalCubeDobrushinFromGibbsExact` to get L1 `≤2epsilon≤q<1`. Exact Agda **compiler written**, with strict same physical cube `Nat×a=ell`; the original input ratios `epsilon_{a,L}` remain unpaid. This criterion can be too strong at high beta because it bounds pointwise relative densities.

**Route B — weighted/averaged Dobrushin–Shlosman:** prove actual conditional TV influence matrix `C^{a,L}` and positive Perron weights `w` with `Cw≤q w`; `q` is independent of cutoff and physical volume. This may succeed when pointwise raw relative variation fails. The exact rational matrix checker is now implemented, with fake-fixture/physical-admission distinction. To promote a numerical matrix: prove it **upper-bounds actual continuous SU(N) conditional integrals**, using interval arithmetic, original Wilson/Haar/Fubini, correct boundary sectors, and an arbitrary-volume extension theorem. Bounded boxes alone are not arbitrary-cutoff/volume estimates.

**Route C — source-native polymer:** from original CMP116 marked expansion derive `sum_{connected polymers crossing distance r} |weight|≤A q^r` with `q<1` and fixed physical `ell`. The existing `BalabanClayT5PhysicalRootedShellInjectionExact`, `BalabanClayT5TwoSupportRootedShellGeometryExact`, `BalabanCMP116PublishedLiteralSelectedRound467Exact` cover combinatorial and compiler portions; the *actual signed weight bound uniform in a,L* remains mathematical work.

Rank by proof economy: use source-native C first if physical polymer theorem supplied; use B for a finite-size certificate; use A as fast sufficient control in good regions. **Never require all A/B/C simultaneously**: any one genuine original-family path plus OS/continuum requirements can close the mass gap.

## 4. What the 2D/3D/5D comparisons actually purchase

`YMClayVoyagerDimensionSignatureForkExact` already computes `2[g_d]=4-d`. It explicitly distinguishes spacetime dimension, stochastic auxiliary time, Euclidean 5D lattice, and KK fifth dimension; reuse it rather than treating all “5D” statements as the same theory.

| d | Coupling mass dimension | Reusable proof mechanism | Missing to infer 4D Clay |
|---|---:|---|---|
| 2 | +1 | Exact compact-surface Yang–Mills, stochastic quantization, planar Wilson loop character/heat-kernel semigroup and exact area law | 2D local fields/canonical scaling are not the 4D marginal running family |
| 3 | +1/2 | Superrenormalizable stochastic-gauge regularity, renormalization/covariant Markov quotient and tightness techniques | Different degree of singularity and physical field dimensions; a 3D stochastic result is not 4D OS mass-gap proof |
| 4 | 0 | Asymptotic freedom, CMP119/CMP122 RG, selected 4D Wilson plaquettes and CMP116; target `β(a)→∞` | Uniform nonperturbative physical-block/correlation decay plus nontrivial continuum/OS |
| 5 | -1/2 | Useful lattice countermodels, compactified KK metric and dimension reduction comparisons | 5D pure YM is power-counting nonrenormalizable; KK does not preserve the 4D Yang–Mills measure/spectra without full action/measure/spectral identification |

A compactified fifth coordinate changes the 4D effective action: KK massive modes, radion/metric fluctuations, counterterms and cutoff matching must all be accounted for. It is not a shortcut from a 5D source record to a positive physical 4D YM spectral gap. The recent PR #1460 is a downstream Lorentz/KK *bridge*, not an accepted independent Clay proof.

## 5. Exact deliverables and acceptance after this pass

- **PCUBE.F01** `YMClayPhysicalCubeDobrushinFromGibbsExact.physicalCubeCellLength` and strict physical calibration. **SOURCE/PENDING KERNEL**.
- **PCUBE.F02** `originalConditionalRowsUniformlyContract` on the original normalized conditional fibre, from real relative `epsilon` plus a cutoff/volume-independent q. **SOURCE/CONDITIONAL/KERNEL PENDING**.
- **PCUBE.F03** `originalConditionalObservableUniformlyContract` with exact real-time-independent `A q` bound on the same selected local observable. **SOURCE/CONDITIONAL/KERNEL PENDING**.
- **PCUBE.F04** exact rational positive-weight Perron checker with 7 negative controls; Python reference-only. The illustrative 4×4 matrix has max weighted row ratio `5/12`, chosen `q=1/2`, fixed physical `ell=1`, and valid `a=1/2,1/4,1/8`. **EXACT REFERENCE, NOT PHYSICAL**.
- **PCUBE.P01/P02/P03** prove original R445 fine Gibbs→physical coarse conditional and reflection/geometry for all cutoffs and volumes; a fixed 1024-bond example is insufficient.
- **PCUBE.P04** the quantitative comparison `Cw≤q w` for all actual `a,L` at `ell`, with `q<1` and physical source pins. **OPEN MATHEMATICS**.
- **PCUBE.P05** original CMP116 `literalSelectedCMP116Localization`, original common analytic domain and physical time envelope. **OPEN MATHEMATICS**.
- **PCUBE.P06/P07** continuum selected OS Hilbert and same-H gap, nontriviality and all compact simple groups. **OPEN MATHEMATICS**.

**Acceptance firewall:** no stagewise `machineChecked` label, `Set`-typed field, fake rational influence fixture, reference value or standalone normalized finite Gibbs model may be called a Clay solution. Exact-head Agda receipt, strict transitive analytic authority, original source same-object proof, and dimensionally correct continuum limits are separate. The external one-cube/forest-gauge preprint (Hexagon 2610.00341v6, 2026-11-02) is **independent unreviewed candidate prior art**, not Agda/physical authority; its own abstract says tuned-cube estimate and continuum existence were not proved. Relevant DOI for original CMP116: `10.1007/BF01239022`.

### Verified recent five-sector PR #1460 cross-fibre result — dimensional reuse, not spectrum transport

The *actual* new downstream owner is `DASHI/Physics/YangMills/YMClayFiveSectorBidiSteelmanExact.agda` in [PR #1460](https://github.com/chboishabba/dashi_agda/pull/1460), not a claimed 2/3/5-dimensional continuum QFT completion. Its `threeToTwoExact`, `fourToThreeExact`, `fiveToFourExact` decompose 1/3/6/10 positively oriented plaquette contributions; `sumEqualsBaseForcesZeroCross` and `fiveMatchesFourForcesCrossZero` show *strictly positive discarded curvature* prevents silently identifying higher- and lower-dimensional Wilson actions. The existing `fiveFibreCounterexample` gives that obstruction concretely. Its matched observables are conditional `matched54/matched43/matched32`; it does not construct their physical witnesses. Preserve the parent→child dependency: #1444 must not import a not-yet-integrated #1460 child; reusing the donor after proper reconciliation is a separate source move.

The strongest use of these dimensional results for the 4D Clay route is **a negative control and geometry calibration**: all 4D positive plaquette orientations, the correct 4D marginal beta flow, and the *same* selected physical OS observables must survive dimensional comparison. Cross-fibre curvature, KK scalar modes and 5D gravity stress are not allowed to disappear via a projection name. This eliminates invalid purported gap transfers; it does not establish the physical-cube q estimate.

