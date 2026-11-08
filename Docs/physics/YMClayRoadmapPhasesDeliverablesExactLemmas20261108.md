# Yang–Mills Clay — canonical roadmap, phases, deliverables, exact remaining lemmas

**Reconciled:** 8 November 2026 · **Working PR:** [#1444](https://github.com/chboishabba/dashi_agda/pull/1444) · **Earlier Route-S donor:** [#1440](https://github.com/chboishabba/dashi_agda/pull/1440) · **3+1/OS/KK comparison:** [#1460](https://github.com/chboishabba/dashi_agda/pull/1460)

**Machine-readable single source of status truth:** [`YMClayEndpointPhaseLemmaManifest20261108.json`](YMClayEndpointPhaseLemmaManifest20261108.json). The exact theorem target identifiers YM01–YM10 in this document are **proposed final inhabitants**, not existing theorem names or Agda-accepted statements. Existing source-written interfaces are explicitly indicated below. This ledger supersedes older *priority/status descriptions*, not their mathematical proofs.

## 0. Goal and status contract

Construct, for **every compact simple Lie group** (K), a nontrivial four-dimensional interacting Yang–Mills theory on \(\mathbb R^4\) satisfying the required QFT axioms, with **one and the same** reconstructed physical Hamiltonian \(H_K\), vacuum \(\Omega_K\), and \(\Delta_K>0\) such that

\[
\operatorname{spec}\bigl(H_K|_{\Omega_K^\perp}\bigr)\subseteq[\Delta_K,\infty).
\]

**Unsolved as of 8 November 2026.** In particular, none of the current finite Wilson/Gibbs/Heisenberg/KK/OS *conditional* proof compilers are a completed Clay proof.

Four distinct evidence levels must not be collapsed: **(i)** source-written type/conditional compiler, **(ii)** inhabited physical-source hypotheses on original Wilson data, **(iii)** Agda kernel-accepted theorem on the selected source, **(iv)** full Clay endpoint (including the group scope). CI is not the user's priority, but source/kernel honesty is mandatory.

## 1. Phase plan and delivery/acceptance gates

| Phase | Owner / target | Existing machinery to reuse | Remaining delivery and exact acceptance |
|---|---|---|---|
| **PH0 — original physical lattice** | **YM01** | R443 original six positive plaquettes, gauge invariance, `YMClaySUNVariablePeriodicGibbsGaugeExact`, `YMClayE1OriginalSUNDependentCylinderExact` | Actual compact continuous SU(N) one-link Haar/Fubini and original normalized Wilson measure with physical beta, varying cutoff, and no rational SU2 substitution |
| **PH1 — RG to interacting continuum** | **YM02, YM03, YM09** | R445 original marked moments, native blocked Wilson pushforward, Gate4 UV iteration, E1 cylinder compiler, native OS pullback | Full original measure small/large-field estimates uniformly in cutoff and volume; noncollapsed R4 OS/QFT Schwinger limit; surviving genuinely interacting local witness |
| **PH2 — physical clustering** | **YM04, YM05** | `YMClayD1PhysicalRemoteCoverageNoGoExact`, CMP116/R320, `YMClayD1OriginalFullWilsonSmallLargeFieldExact` | Required **physical** remote pairs covered nonvacuously at *every* physical cutoff/volume; actual original large-field remainder and small-field bounds with one uniform \(q<1\) at fixed positive physical block size; complete real Wilson covariance bound |
| **PH3 — one OS theory and entire nonvacuum sector** | **YM06, YM07, YM08** | `YMClayOriginalWilsonNativeOSPullbackExact`, R330–R333, `YMClayDirectSourceOSMassGapFrontierExact`, R316 | Same E1 Schwinger theory and reflected form survive scale limits; actual OS reconstruction and dense physical gauge-invariant test vectors; no undetected arbitrarily low-energy sector; strict real-unit spectral gap of the same \(H_{OS}\) |
| **PH4 — Clay scope** | **YM10** | Fixed-group compilers; native SU(N) matrix and compact-group abstraction | One source-identical nontrivial continuum and positive gap for **every** compact simple gauge group, not just SU(2), SU(N), a rational quaternion group, or selected toy tests |

PH2 is a **preferred sufficient route**, not a logically mandatory independent Clay axiom: a new rigorous proof of YM08 on the complete nonvacuum sector could replace YM04–YM05. PH1, PH3, nontriviality and PH4 cannot be avoided.

## 2. Exact remaining theorem targets, with source owners

**YM01 — `originalSUNHaarPhysicalMeasure`.** Instantiate actual (SU(N)) trace/continuous one-link Haar, product Haar/Fubini, original normalized Wilson–Gibbs measure \(\mu_{a,L}^{K}\), and gauge invariance over the *original varying* periodic bond sets. **Already written:** periodic finite SU(N) holonomy/trace/action/gauge compatibility, source-backed generic one-link Haar interface, varying-cutoff cylinder expectations. **Open:** materializing those Haar and physical-scale inputs.

**YM02 — `originalWilsonUniformRGEstimates`.** Bound original R445 physical marked moments, polymer/tail and large-field contributions across changing cutoff and volume, with compatible native block maps, complete reflected-form control and fixed physical scales. **Already written:** finite blocked pushforward and conditional RG iterations. **Open:** the source-specific uniform estimates, not formal iteration.

**YM03 — `originalWilsonInteractingR4Limit`.** From the original \(\mu_{a,L}^{K}\) construct compatible and gauge-invariant local cylinder Schwinger functions on \(\mathbb R^4\) and prove their UV/IR limit, Euclidean covariance, reflection positivity, symmetry, regularity and required OS/QFT properties. The E1 all-section cylinder carrier is *too large*: arbitrary cutoff-alternating sections need not converge. **Open:** the noncollapsed physical local subalgebra and genuine limit.

**YM04 — `originalPhysicalRemotePairCoverage`.** Define the physical required remote boundary pair relation from the *actual original Wilson lattice geometry* at a fixed positive block length and prove all necessary pairs admissible across **every** cutoff/volume. **Already written:** `ActualPhysicalPairCoverage`, no-empty-predicate no-go and exact finite counterexample. **Open:** sourcing the actual geometric relation and its influence estimates.

**YM05 — `originalFullWilsonSmallLargeUniformDecay`.** Prove on the same actual Wilson measure, for \(F_x,F_y\) in a physically adequate local observable algebra,

\[
|\operatorname{Cov}_{\mu_{a,L}^{K}}(F_x,F_y)|
\le C_K(F_x,F_y)\,e^{-m_K d_{\mathrm{phys}}(x,y)},\qquad m_K>0
\]

with cutoff/volume-uniform real physical \(m_K\). Reuse the source-written small-field + original large-field envelope theorem. **Open:** actual CMP116-domain source and full large-field remainder, plus source-derived uniform rate and physical calibration.

**YM06 — `originalWilsonSameOSReconstruction`.** Establish reflection/positive-time compatibility of the actual native blocking map, whole reflected-form positivity on the *full* original Wilson source at all needed scales, passage to the continuum limit, and identify the **same** reconstructed OS Hilbert space and \(H_{OS}\) throughout. **Already written:** exact fixed-size reflected quadratic pullback and R331/R333 indexed interfaces. **Open:** physically instantiated symmetry and limit, not isolated formal RP labels.

**YM07 — `originalWilsonDenseNonvacuumDetection`.** The Wilson/local gauge-invariant reflected test-state domain is cyclic/dense in the complete relevant \(\Omega^\perp\) sector of the **same** OS reconstruction, with spectral subspace detection. **Open:** no hidden soft modes; selected-probe covariance bounds are insufficient.

**YM08 — `originalWilsonFullOSSubgapExclusion`.** Prove \(\exists\Delta_K>0\) in *physical units* so \(\operatorname{spec}(H_{OS}|_{\Omega^\perp})\subseteq[\Delta_K,\infty)\). Use YM05 with a properly proved density/spectral transfer or another honest full-sector mass-gap route. **Already written:** conditional direct R333/R316 algebraic compilers. **Open:** the true original-source positive physical spectral threshold on the entire sector. No dependence on isolated finite lattice gaps or selected test probes.

**YM09 — `originalInteractingLocalWitnessSurvives`.** Give an explicit physical local gauge-invariant renormalized correlation surviving the E1 continuum and prove enough structure to distinguish the resulting theory from a trivial/free model. One nonzero connected function without a discriminating condition may be insufficient: specify the genuine interacting criterion.

**YM10 — `clayAllCompactSimpleGroups`.** Close YM01–YM03, YM06–YM09 for **every** compact simple K (with YM04–YM05 or a substitute proof of YM08). The current finite SU(N) family is not by itself the all-compact-simple result.

## 3. Precise remaining producer-to-consumer map

```text
original SU(N) matrices/link geometry + compact Haar [YM01]
     ├──> changing-cutoff native Wilson source [EXISTS]
     ├──> R445 full finite marked pushforward [EXISTS / conditional estimates]
     └──> original physical RG uniform moments/tails [YM02 OPEN]
                      ├──> original interacting R4 OS limit [YM03 OPEN]
                      │         ├──> nontrivial local interaction [YM09 OPEN]
                      │         └──> same-source OS reconstruction [YM06 OPEN]
                      └──> actual physical pair coverage [YM04 OPEN]
                                └──> complete Wilson small+large covariance [YM05 OPEN]
[YM06] + [physically dense nonvacuum sector YM07]
        + [YM05 or alternate physical full-sector method]
                          └──> same-H spectral exclusion [YM08 OPEN]
[YM03, YM06, YM08, YM09] for every compact simple K
                          └──> [YM10 OPEN]
```

Re-use, do not recreate: R443, R445, R320 (CMP116), R331/R333, original Wilson OS pullback, SU(N) side-four lattice and the published Osterwalder–Schrader theorem. The analytic physical inputs are not discharged by importing a theorem module.

## 4. Explicit no-promotion tests and completion criteria

1. **Empty remote class:** `AdmissiblePerturbation = ⊥` can satisfy old conditional influence estimates vacuously; require actually populated physically mandated pairs. The existing negative control is source-written.
2. **Shrinking lattice rate:** \(a_n=1/n\), \(q_n=1-1/n^2\) gives \(q_n^n\to1\) across unit physical distance; \(q_n<1\) for every cutoff does **not** give uniform \(m>0\).
3. **Selected-probe gap:** \(H_n=\mathrm{diag}(1,1/2,\ldots,1/n)\); the probe \(e_1\) has a constant decay rate, but the full nonvacuum spectral infimum vanishes. Require density and full-sector coverage.
4. **Wrong source:** cutoff-independent link carriers, unrelated Haar Gibbs/OS theories and mixed physical units are inadmissible substitutions.
5. **Finite/literature nonpromotion:** fixed-volume R445 bounds, CMP116 small-field estimates, published CMP119 estimates for superrenormalizable models and a merely *conditional* OS spectral interface are not original 4D full-Wilson continuum proofs.
6. **Exact proof acceptance:** finish the original source estimates, inhabit the actual selected physical records, establish one same-source E1/D2/N1/G1 theorem, and separately obtain kernel acceptance before asserting formal verification. No CI run required for roadmap work.

## 5. 3+1, KK, Monster: present, but not extra Clay gates

**PR #1460 3+1:** `DASHI/Geometry/Signature31FromIntrinsicShellForcing`, `CausalForcesLorentz31`, `LorentzEmergenceFromCausalAxioms`, and `Lorentz31DirectionalProbeExact` already encode geometric and calibrated directional 3+1 results. `YMClayLorentz31DirectionalKKHodgeExact` explicitly distinguishes the Euclidean and Lorentzian two-form stars. The *physical* source is still conditional on `RealizedDynamics` and the measured cone/quadratic map. Do **not** repeat the signature combinatorics or add this physical observation as a Clay prerequisite.

**Unified observer/KK branch:** `originalObserverRealizedDynamics`, `originalObserverMetricEqualsKKReduction`, `selectedEuclideanOSLorentzReconstruction`, `sameObserverClockAndOSHamiltonian` remain a separate observer/KK/OS programme. The original physical observer clock ↔ OS H identification is not obtained just from the finite 3+1 sign theorem.

**KK #1241:** one fully sourced 5D Einstein–matter–gauge–radion action, its nonanomalous compactification and physical reduced solution remain independent. No KK gravity theorem is required to construct the standalone Euclidean YM Clay theory.

**Monster #1472:** Griess/DGL uniqueness, true same-80-relator group equivalence and original-vs-FLM action equality on u/v remain separate. Their 196884-dimensional chart or 194 classes have no proven positive YM full-sector mass-gap implication.

## 6. Phase status snapshot

| Phase | Gate status | Next decisive work product |
|---|---|---|
| PH0 | **Open physical-source instantiation** | Original continuous Haar SU(N) measure with physical normalization and scale |
| PH1 | **Open continuum analytics** | Uniform physical R445 tails + actual R4 interacting OS construction |
| PH2 | **Open actual full Wilson decay** | Nonvacuous physical remote pair geometry plus CMP116 small/large full-source inequality |
| PH3 | **Open full-sector spectral theorem** | Same E1 OS H, cyclic/dense physical sector and positive spectral threshold |
| PH4 | **Open Clay quantification** | Complete arbitrary compact simple K theorem |
 
**Prioritization:** PH1 YM02 and PH2 YM05 are the highest mathematical uncertainty. Advance them concurrently with the PH0 actual-source provider, then pay E1+N1, same-H_OS and dense full-sector gap. Avoid spending cycles rewriting already source-written finite algebra.

**Attribution:** Wilson, Bałaban (CMP109/116/119/122), Osterwalder–Schrader, and the corresponding published group/analysis authors retain historical theorem credit. DASHI source compilers and finite nonpromotion models are separate formal implementation work.
