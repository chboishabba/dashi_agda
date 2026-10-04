# CMP119 cosmology primary-source scope audit — 2026-10-04

## Purpose

This note records the exact boundary between the Bałaban source results currently represented in `dashi_agda` and the remaining cosmology source theorems on PR #1050.

The point is fail-closed provenance: an RG/locality theorem must not be silently promoted into a new signed Euclidean covariance law, an observable-semantics identification, an absolute finite/continuum calibration, or a cosmological metric-response sign.

## Primary sources represented by the current source layer

1. T. Bałaban, *Renormalization Group Approach to Lattice Gauge Field Theories. I. Generation of Effective Actions in a Small Field Approximation and a Coupling Constant Renormalization Transform*, Communications in Mathematical Physics 109 (1987), 249–301. DOI `10.1007/BF01215223`.
2. T. Bałaban, *Renormalization Group Approach to Lattice Gauge Field Theories. II. Cluster Expansions*, Communications in Mathematical Physics 116 (1988), 1–22. DOI `10.1007/BF01239022`.
3. T. Bałaban, *Convergent Renormalization Expansions for Lattice Gauge Theories*, Communications in Mathematical Physics 119 (1988), 243–285. DOI `10.1007/BF01217741`.
4. T. Bałaban, *Large Field Renormalization. II. Localization, Exponentiation, and Bounds for the R Operation*, Communications in Mathematical Physics 122 (1989), 355–392. DOI `10.1007/BF01238433`.

The repository represents these papers as supplying effective-action continuation/localization, local analytic insertion expansions, Section-2 E/R/B regularity/localization predicates, and the RG tail machinery under the relevant small-coupling hypotheses.

The repository deliberately records some concrete source instantiations as `conditional`, not `machineChecked`: in particular the literal CMP109/116 continuation instantiation, the active raw CMP119/CMP122 source-state instantiation, and the literal completed stress provenance.

## What is *not* supplied by those imported source surfaces

### A1 — signed R144 B4 covariance

The imported first-variation interface provides function-linearity and the source continuation provides localized effective activities. Neither determines the required signed rank-two hypercubic action on the selected rational readout.

This is not merely absent infrastructure. `CMP119CosmologyE1LinearityDoesNotForceB4CovarianceExact` gives a finite countermodel in which additive first-variation linearity and a linear coordinate symmetry coexist while the readout fails covariance. `CMP119CosmologyA1UnsignedTangentSignFirewallExact` additionally records that axis flips carry an independent sign on off-diagonal symmetric basis tensors.

Therefore A1 still requires a genuinely source-backed signed covariance/change-of-variables theorem on the selected finite family.

### A2 — Round109 pair semantics

CMP116/119 local-insertion theory supplies a source-native insertion-pair token and local-analytic admissibility. The current pair carrier has no eliminator to `Configuration -> R`.

The Local-C/Wilson compiler now constructs the canonical selected cylinder observable and discharges the published positive-time and gauge-invariance predicates. What remains is only the same-object statement identifying the opaque Round109 stress insertion with that observable.

`CMP119CosmologyR109PairObservableUnderdeterminationExact` proves that the bare pair carrier cannot determine this evaluator uniquely.

### B1 — selected same finite sequence and completed endpoint

Round109 controls response *differences*. Such control is invariant under translating every finite response by an additive constant. `CMP119CosmologyR109AbsoluteExpectationAnchorNoGoExact` formalizes this directly.

The strongest current max-cut is therefore the three same-object facts in `CMP119CosmologyB1SelectedSameSequenceMaxCutExact`:

1. the Round109 tail controls future values of the actual selected finite expectation sequence;
2. the canonical R136 completed scalar is the limit of that same sequence;
3. every finite value is the embedded rational R144 finite `D_Gamma` readout.

Once those are supplied, the direct tail inequality is compiler output at every cutoff.

### B2 — strict Eq. (2.23) source gap

CMP119/CMP122 Section-2 regularity and localization control magnitudes/decay of the E/R/B source terms. The raw Eq. (2.23) source carrier does not itself contain a metric derivative.

`CMP119CosmologyEq223ERBMetricVariationUnderdeterminationExact` holds the same raw Eq. (2.23) source fixed while changing only E/R/B metric derivatives and obtains different four-diagonal traces. `CMP119CosmologyEq223VacuumMetricSignUnderdeterminationExact` similarly holds the rest of the source fixed while changing only the vacuum metric derivative and obtains zero, positive, and negative vacuum Weyl coefficients.

Thus Section-2 localization alone cannot prove the cosmological sign.

The current Pareto-minimal B2 physics statement is now only

```text
M_ERB < -c_V
```

for the actual selected metric family. The Round109 dyadic tail is generic vanishing-error analysis: after a strict zero-tail gap exists, a sufficiently late cutoff satisfies

```text
M_ERB + Tail_109(k) < -c_V.
```

The all-cutoff B1 attachment allows the proof to move to that late cutoff without adding another physical calibration.

## Final irreducible basis

The current machine-readable frontier is `CMP119CosmologyIrreducibleSourceTheorems20261004Exact`. It contains six source theorems:

1. signed R144/B4 source covariance;
2. Round109 pair = selected Local-C cylinder semantics;
3. Round109 tail controls the selected finite expectation sequence;
4. completed response = limit of that same sequence;
5. all-cutoff R144 finite readout = selected finite expectation;
6. strict Eq. (2.23) coefficient gap `M_ERB < -c_V`.

There is no remaining adapter construction that can honestly remove these six. Closing them requires additional source derivation, a stronger source definition that makes the equality definitional, or genuinely new mathematics/physical input. They must not be populated by postulates, synthetic normalizations, convention labels, or arbitrary same-object records.
